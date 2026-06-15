#!/usr/bin/env python3
"""
ss_watch.py - Watch ss.lv car listings for new ads that match your filters.

What it does on each run:
  1. Loads your filters from config.yaml.
  2. Walks the ss.lv car listing page(s) you configured (newest ads first).
  3. Figures out which ads are NEW since the last run (state/seen.json).
  4. For new ads that pass the cheap pre-filter (price / year), it opens the
     ad page and reads the "Tehniskā apskate" (technical inspection) date.
  5. Keeps only cars whose inspection is valid for at least N months.
  6. Sorts matches cheapest-first, emails them (if SMTP secrets are set),
     and writes a webpage (docs/index.html) with a rolling list of matches.

Designed to run unattended on GitHub Actions. Nothing to install locally.
"""

from __future__ import annotations

import json
import os
import re
import smtplib
import sys
import time
import html as htmllib
from datetime import date, datetime, timezone, timedelta
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path

import requests
import yaml
from bs4 import BeautifulSoup
from dateutil.relativedelta import relativedelta

# --------------------------------------------------------------------------
# Paths & constants
# --------------------------------------------------------------------------
ROOT = Path(__file__).resolve().parent
CONFIG_PATH = ROOT / "config.yaml"
SEEN_PATH = ROOT / "state" / "seen.json"
MATCHES_PATH = ROOT / "state" / "matches.json"
REPORT_PATH = ROOT / "docs" / "index.html"

BASE = "https://www.ss.lv"
HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
    ),
    "Accept-Language": "lv,en;q=0.8,ru;q=0.5",
    "Accept": "text/html,application/xhtml+xml",
}

SEEN_KEEP_DAYS = 90      # forget ads we last saw more than this many days ago
MATCH_KEEP_DAYS = 30     # how long a match stays on the rolling webpage


# --------------------------------------------------------------------------
# Small helpers
# --------------------------------------------------------------------------
def log(msg: str) -> None:
    print(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}", flush=True)


def load_yaml(path: Path) -> dict:
    with open(path, "r", encoding="utf-8") as fh:
        return yaml.safe_load(fh) or {}


def load_json(path: Path, default):
    if not path.exists():
        return default
    try:
        with open(path, "r", encoding="utf-8") as fh:
            return json.load(fh)
    except (json.JSONDecodeError, OSError):
        return default


def save_json(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(data, fh, ensure_ascii=False, indent=2)


def today() -> date:
    return datetime.now(timezone.utc).date()


# --------------------------------------------------------------------------
# Networking
# --------------------------------------------------------------------------
def fetch(url: str, delay: float, retries: int = 2) -> str | None:
    """GET a page politely. Returns HTML text or None on failure."""
    for attempt in range(retries + 1):
        try:
            resp = requests.get(url, headers=HEADERS, timeout=25)
            if resp.status_code == 200:
                resp.encoding = resp.apparent_encoding or "utf-8"
                time.sleep(delay)
                return resp.text
            log(f"  HTTP {resp.status_code} for {url}")
        except requests.RequestException as exc:
            log(f"  request error ({exc}) for {url}")
        time.sleep(delay * (attempt + 1))
    return None


# --------------------------------------------------------------------------
# Value parsing from text cells
# --------------------------------------------------------------------------
PRICE_RE = re.compile(r"([\d\s.,]+)\s*\u20ac")          # number followed by €
YEAR_RE = re.compile(r"^(19|20)\d{2}$")
ENGINE_RE = re.compile(r"^\d\.\d\s*[A-Za-z]?$")          # 2.0 / 2.0D / 1.6
MILEAGE_RE = re.compile(r"t\u016bkst", re.IGNORECASE)    # "380 tūkst."


def parse_price(text: str) -> tuple[int | None, str]:
    """Return (price_in_eur or None, raw_text). Skips rent (€/mēn.)."""
    raw = text.strip()
    low = raw.lower()
    if "m\u0113n" in low:           # €/mēn. -> rental, ignore
        return None, raw
    m = PRICE_RE.search(raw)
    if not m:
        return None, raw
    digits = re.sub(r"[^\d]", "", m.group(1))
    if not digits:
        return None, raw
    return int(digits), raw


def classify_cells(cells: list[str]) -> dict:
    """Content-based classification of a listing row's value cells, so we do
    not depend on exact column order (which differs between pages)."""
    out = {"model": None, "year": None, "engine": None,
           "mileage": None, "price": None, "price_raw": None,
           "exchange": False}
    leftover = []
    for c in cells:
        c = c.strip()
        if not c or c == "-":
            continue
        if out["price"] is None and "\u20ac" in c:
            price, raw = parse_price(c)
            out["price"] = price
            out["price_raw"] = raw
            out["exchange"] = "mai\u0146" in c.lower()
            continue
        if out["year"] is None and YEAR_RE.match(c):
            out["year"] = int(c)
            continue
        if out["engine"] is None and ENGINE_RE.match(c):
            out["engine"] = c
            continue
        if out["mileage"] is None and MILEAGE_RE.search(c):
            out["mileage"] = c
            continue
        leftover.append(c)
    if leftover:
        out["model"] = leftover[0]
    return out


# --------------------------------------------------------------------------
# Listing page parsing
# --------------------------------------------------------------------------
def parse_listing(html_text: str) -> list[dict]:
    """Extract ad rows from a listing page.

    We find ads by their detail-page links (/msg/.../*.html) rather than
    relying on a specific row-id scheme, so this keeps working even if ss.lv
    tweaks its table markup. Each ad has two such links (thumbnail + title);
    we keep the one that carries the title text and dedupe by URL."""
    soup = BeautifulSoup(html_text, "lxml")
    ads: list[dict] = []
    seen: set[str] = set()
    for link in soup.select('a[href*="/msg/"]'):
        href = link.get("href", "")
        if "/transport/cars/" not in href or not href.endswith(".html"):
            continue
        title = link.get_text(" ", strip=True)
        if not title:                       # thumbnail (image) link -> skip
            continue
        url = href if href.startswith("http") else BASE + href
        if url in seen:
            continue
        seen.add(url)

        row = link.find_parent("tr")
        value_cells: list[str] = []
        if row is not None:
            value_cells = [td.get_text(" ", strip=True)
                           for td in row.select("td.msga2-o")]
            if not value_cells:
                value_cells = [td.get_text(" ", strip=True)
                               for td in row.find_all("td")]
        info = classify_cells(value_cells)
        info.update({"url": url, "title": title})
        ads.append(info)
    return ads


def page_url(source: str, n: int) -> str:
    source = source if source.endswith("/") else source + "/"
    return source if n == 1 else f"{source}page{n}.html"


# --------------------------------------------------------------------------
# Detail page parsing (the inspection date lives here)
# --------------------------------------------------------------------------
DATE_DMY = re.compile(r"(\d{1,2})\.(\d{1,2})\.(\d{4})")
DATE_MY = re.compile(r"(?<!\d)(\d{1,2})\.(\d{4})(?!\d)")
DATE_YM_DASH = re.compile(r"(\d{4})-(\d{1,2})(?!\d)")


def last_day_of_month(y: int, m: int) -> date:
    if m == 12:
        return date(y, 12, 31)
    return date(y, m + 1, 1) - relativedelta(days=1)


def parse_inspection_date(value: str) -> date | None:
    """Turn an inspection value into a 'valid until' date.
    Handles 'dd.mm.yyyy', 'mm.yyyy', 'yyyy-mm'. Returns None if absent."""
    if not value:
        return None
    v = value.strip().lower()
    # "Nav", "Bez apskates", "Bez tehniskās apskates", "Nav apskates" -> no TA
    if not v or v == "-" or "nav" in v or "bez" in v:
        return None
    m = DATE_DMY.search(value)
    if m:
        d, mo, y = (int(x) for x in m.groups())
        try:
            return date(y, mo, d)
        except ValueError:
            return last_day_of_month(y, mo)
    m = DATE_YM_DASH.search(value)
    if m:
        y, mo = int(m.group(1)), int(m.group(2))
        return last_day_of_month(y, mo)
    m = DATE_MY.search(value)
    if m:
        mo, y = int(m.group(1)), int(m.group(2))
        return last_day_of_month(y, mo)
    return None


def parse_detail(html_text: str) -> dict:
    """Read the label/value option table on an ad page."""
    soup = BeautifulSoup(html_text, "lxml")
    fields: dict[str, str] = {}

    # ss.lv option rows: a label cell (td.ads_opt_name) + value cell
    for row in soup.find_all("tr"):
        tds = row.find_all("td", recursive=False)
        if len(tds) != 2:
            continue
        label = tds[0].get_text(" ", strip=True).rstrip(":").lower()
        value = tds[1].get_text(" ", strip=True)
        if label and value and label not in fields:
            fields[label] = value

    # inspection date: try the dedicated field, then fall back to free text
    insp_raw = ""
    for key in fields:
        if "tehnisk" in key and "apskat" in key:   # "Tehniskā apskate"
            insp_raw = fields[key]
            break
    insp_date = parse_inspection_date(insp_raw)
    if insp_date is None:
        # fallback: some sellers write "TA līdz dd.mm.yyyy" in the body text
        body = soup.get_text(" ", strip=True)
        m = re.search(r"(?:ta|tehnisk\w*\s+apskat\w*)\D{0,12}"
                      r"(\d{1,2}\.\d{1,2}\.\d{4}|\d{1,2}\.\d{4})",
                      body, re.IGNORECASE)
        if m:
            insp_date = parse_inspection_date(m.group(1))

    # price on the detail page (more reliable than the listing cell)
    price = None
    price_node = soup.select_one(".ads_price, #tdo_8, [id^=tdo_]")
    if price_node:
        price, _ = parse_price(price_node.get_text(" ", strip=True))
    if price is None:
        for key in ("cena", "cena:"):
            if key in fields:
                price, _ = parse_price(fields[key])
                if price:
                    break

    # listed date
    posted = None
    m = re.search(r"Datums:\s*(\d{2}\.\d{2}\.\d{4})", soup.get_text(" ", strip=True))
    if m:
        posted = m.group(1)

    return {
        "inspection_raw": insp_raw,
        "inspection_until": insp_date.isoformat() if insp_date else None,
        "detail_price": price,
        "posted": posted,
        "place": fields.get("vieta"),
    }


# --------------------------------------------------------------------------
# Filtering
# --------------------------------------------------------------------------
def passes_prefilter(ad: dict, f: dict) -> bool:
    price = ad.get("price")
    if price is None:                       # no price (e.g. "buying" ads) -> skip
        return False
    if f.get("max_price_eur") is not None and price > f["max_price_eur"]:
        return False
    if f.get("min_price_eur") and price < f["min_price_eur"]:
        return False
    if f.get("min_year") and ad.get("year") and ad["year"] < f["min_year"]:
        return False
    if f.get("exclude_exchange_only") and ad.get("exchange"):
        return False
    title = (ad.get("title") or "").lower()
    for kw in f.get("keywords_exclude") or []:
        if kw.lower() in title:
            return False
    return True


def passes_inspection(detail: dict, f: dict) -> tuple[bool, int | None]:
    """Return (ok, months_left)."""
    until = detail.get("inspection_until")
    min_months = f.get("min_inspection_months", 3)
    if not until:
        return (not f.get("require_inspection", True), None)
    until_d = date.fromisoformat(until)
    cutoff = today() + relativedelta(months=min_months)
    rd = relativedelta(until_d, today())
    months_left = rd.years * 12 + rd.months
    return (until_d >= cutoff, months_left)


def inspection_left(until_iso: str) -> tuple[int, int]:
    """Return (months_left, days_left) until the inspection expires."""
    d = date.fromisoformat(until_iso)
    rd = relativedelta(d, today())
    months = rd.years * 12 + rd.months
    days = (d - today()).days
    return months, days


def inspection_status(until_iso: str | None, raw: str) -> str:
    """valid = has a future date; none = explicitly no TA; unknown = couldn't read."""
    if until_iso:
        return "valid"
    low = (raw or "").lower()
    if "nav" in low or "bez" in low:
        return "none"
    return "unknown"


# --------------------------------------------------------------------------
# Report / email rendering
# --------------------------------------------------------------------------
def esc(x) -> str:
    return htmllib.escape(str(x if x is not None else ""))


def insp_text(m: dict) -> str:
    """Plain-text-ish inspection summary for the email table."""
    if m.get("insp_status") == "valid" and m.get("inspection_until"):
        mo, d = m.get("months_left"), m.get("days_left")
        if mo and mo >= 1:
            left = f"{mo} mēn."
        elif d is not None:
            left = f"{d} d."
        else:
            left = ""
        return f"{m['inspection_until']} ({left})".strip()
    if m.get("inspection_raw"):
        return m["inspection_raw"]
    return "?"


def render_email_html(matches: list[dict]) -> str:
    """Simple static table for email (no JS)."""
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    rows = []
    for m in matches:
        price = f"{m['price']:,} \u20ac".replace(",", " ") if m.get("price") else "?"
        rows.append(
            "<tr>"
            f"<td><a href='{esc(m['url'])}'>{esc(m['title'])}</a></td>"
            f"<td style='white-space:nowrap;font-weight:600'>{esc(price)}</td>"
            f"<td>{esc(m.get('year') or '')}</td>"
            f"<td>{esc(m.get('engine') or '')}</td>"
            f"<td style='white-space:nowrap'>{esc(insp_text(m))}</td>"
            f"<td>{esc(m.get('place') or '')}</td>"
            "</tr>"
        )
    body = "\n".join(rows) or "<tr><td colspan=6>Nav rezultātu.</td></tr>"
    return f"""<!doctype html><html lang="lv"><head><meta charset="utf-8"></head>
<body style="font-family:system-ui,Segoe UI,Roboto,sans-serif;color:#111">
<h2 style="font-size:17px">Jaunie sludinājumi ({len(matches)})</h2>
<div style="color:#666;font-size:12px;margin-bottom:10px">{ts} &middot; lētākie augšā</div>
<table style="border-collapse:collapse;font-size:14px" border="0" cellpadding="6">
<thead><tr style="background:#111;color:#fff;text-align:left">
<th>Sludinājums</th><th>Cena</th><th>Gads</th><th>Dzinējs</th>
<th>Tehniskā apskate</th><th>Vieta</th></tr></thead>
<tbody>{body}</tbody></table>
</body></html>"""


def render_page_html(rows: list[dict], ts: str) -> str:
    """Interactive page: sortable, filterable, with pinned favourites
    (favourites persist in the browser via localStorage)."""
    data_json = json.dumps(rows, ensure_ascii=False)
    return """<!doctype html>
<html lang="lv"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>SS.LV auto novērošana</title>
<style>
  body{font-family:system-ui,Segoe UI,Roboto,sans-serif;margin:0;background:#f6f7f9;color:#111}
  .wrap{max-width:1100px;margin:0 auto;padding:20px 14px 64px}
  h1{font-size:21px;margin:0 0 4px}
  .meta{color:#666;font-size:13px;margin-bottom:14px}
  .controls{display:flex;flex-wrap:wrap;gap:10px 14px;align-items:center;margin-bottom:14px;
    background:#fff;border:1px solid #e6e6e6;border-radius:10px;padding:12px}
  .controls input[type=text],.controls input[type=number]{border:1px solid #ccc;border-radius:7px;
    padding:6px 8px;font-size:14px}
  .controls label{font-size:13px;color:#333;display:flex;align-items:center;gap:5px}
  .stat{margin-left:auto;color:#666;font-size:12px}
  table{width:100%;border-collapse:collapse;background:#fff;border-radius:10px;overflow:hidden;
    box-shadow:0 1px 3px rgba(0,0,0,.08);font-size:14px}
  th{text-align:left;background:#111;color:#fff;padding:9px 10px;font-weight:600;font-size:11px;
    text-transform:uppercase;letter-spacing:.03em;white-space:nowrap;user-select:none}
  th[data-k]:not([data-k=fav]){cursor:pointer}
  th .arr{opacity:.5;font-size:10px}
  td{padding:8px 10px;border-top:1px solid #eee;vertical-align:top}
  tr:hover td{background:#fafafa}
  .favrow td{background:#fffbea}
  .favrow:hover td{background:#fff6d6}
  a{color:#1d4ed8;text-decoration:none}a:hover{text-decoration:underline}
  .num{white-space:nowrap;font-weight:600}
  .badge{background:#16a34a;color:#fff;border-radius:4px;padding:1px 6px;font-size:11px}
  .star{background:none;border:none;cursor:pointer;font-size:18px;line-height:1;color:#e0b400;padding:0}
  .ins small{color:#666}
  .ins.ok{color:#15803d;font-weight:600}
  .ins.warn{color:#b45309}
  .ins.bad{color:#b91c1c}
  .ins.none{color:#999}
  .ins.unk{color:#bbb}
</style></head>
<body><div class="wrap">
  <h1>SS.LV vieglo auto nov\u0113ro\u0161ana</h1>
  <div class="meta">Atjaunin\u0101ts: __TS__ &middot; piesprausto izlasi glab\u0101 \u0161aj\u0101 p\u0101rl\u016bk\u0101</div>
  <div class="controls">
    <input id="q" type="text" placeholder="Mekl\u0113t nosaukum\u0101...">
    <label>Maks. cena <input id="maxp" type="number" style="width:80px"></label>
    <label>Min. TA m\u0113n. <input id="minm" type="number" style="width:60px"></label>
    <label><input id="onlyvalid" type="checkbox"> Tikai ar der\u012bgu TA</label>
    <label><input id="onlynew" type="checkbox"> Tikai jaunie</label>
    <span id="stat" class="stat"></span>
  </div>
  <table id="tbl"><thead><tr>
    <th data-k="fav">\u2605</th>
    <th data-k="title">Sludin\u0101jums <span class="arr"></span></th>
    <th data-k="price">Cena <span class="arr"></span></th>
    <th data-k="year">Gads <span class="arr"></span></th>
    <th data-k="engine">Dzin\u0113js <span class="arr"></span></th>
    <th data-k="mileage">Nobraukums <span class="arr"></span></th>
    <th data-k="months_left">Tehnisk\u0101 apskate <span class="arr"></span></th>
    <th data-k="place">Vieta <span class="arr"></span></th>
  </tr></thead><tbody id="body"></tbody></table>
</div>
<script>
const DATA = __DATA__;
const FAVKEY = "sscw_favs";
let favs = (()=>{try{return JSON.parse(localStorage.getItem(FAVKEY))||{};}catch(e){return {};}})();
function saveFavs(){localStorage.setItem(FAVKEY, JSON.stringify(favs));}
let sortK="price", sortDir=1;

function esc(s){return (s==null?"":String(s)).replace(/[&<>"]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]));}
function rowsAll(){
  const map={};
  DATA.forEach(r=>map[r.url]=r);
  Object.values(favs).forEach(r=>{if(!map[r.url])map[r.url]=r;});
  return Object.values(map);
}
function inspCell(r){
  if(r.insp_status==="valid"&&r.inspection_until){
    const m=r.months_left,d=r.days_left;
    const left=(m&&m>=1)?(m+" m\u0113n."):(d!=null?d+" d.":"");
    const cls=(m!=null&&m>=3)?"ok":(((m!=null&&m>=1)||(d!=null&&d>=30))?"warn":"bad");
    return '<span class="ins '+cls+'">'+r.inspection_until+' <small>'+left+'</small></span>';
  }
  if(r.inspection_raw)return '<span class="ins none">'+esc(r.inspection_raw)+'</span>';
  return '<span class="ins unk">?</span>';
}
function cmp(a,b,k){
  if(k==="title"||k==="engine"||k==="place"||k==="mileage"){
    const x=(a[k]||"").toString().toLowerCase(),y=(b[k]||"").toString().toLowerCase();
    return x<y?-1:x>y?1:0;
  }
  let x=a[k],y=b[k];
  x=(x==null)?Infinity:x; y=(y==null)?Infinity:y;
  return x<y?-1:x>y?1:0;
}
function passFilter(r){
  const q=document.getElementById("q").value.trim().toLowerCase();
  if(q&&!((r.title||"").toLowerCase().includes(q)))return false;
  const maxp=parseFloat(document.getElementById("maxp").value);
  if(!isNaN(maxp)&&(r.price==null||r.price>maxp))return false;
  const minm=parseFloat(document.getElementById("minm").value);
  if(!isNaN(minm)){if(r.insp_status!=="valid"||r.months_left==null||r.months_left<minm)return false;}
  if(document.getElementById("onlyvalid").checked&&r.insp_status!=="valid")return false;
  if(document.getElementById("onlynew").checked&&!r.is_new)return false;
  return true;
}
function rowHtml(r,fav){
  const price=r.price!=null?(r.price.toLocaleString("lv-LV")+" \u20ac"):"?";
  const badge=r.is_new?' <span class="badge">JAUNS</span>':"";
  const star=fav?"\u2605":"\u2606";
  return '<tr class="'+(fav?"favrow":"")+'">'
    +'<td><button class="star" data-u="'+encodeURIComponent(r.url)+'">'+star+'</button></td>'
    +'<td><a href="'+esc(r.url)+'" target="_blank" rel="noopener">'+esc(r.title)+'</a>'+badge+'</td>'
    +'<td class="num">'+price+'</td>'
    +'<td>'+esc(r.year||"")+'</td>'
    +'<td>'+esc(r.engine||"")+'</td>'
    +'<td>'+esc(r.mileage||"")+'</td>'
    +'<td>'+inspCell(r)+'</td>'
    +'<td>'+esc(r.place||"")+'</td></tr>';
}
function render(){
  const all=rowsAll();
  const favRows=all.filter(r=>favs[r.url]);
  const rest=all.filter(r=>!favs[r.url]&&passFilter(r));
  favRows.sort((a,b)=>sortDir*cmp(a,b,sortK));
  rest.sort((a,b)=>sortDir*cmp(a,b,sortK));
  let html="";
  favRows.forEach(r=>html+=rowHtml(r,true));
  rest.forEach(r=>html+=rowHtml(r,false));
  document.getElementById("body").innerHTML=html||'<tr><td colspan="8" style="padding:20px;color:#888">Nav rezult\u0101tu</td></tr>';
  document.getElementById("stat").textContent=favRows.length+" piesprausti \u00b7 "+rest.length+" r\u0101d\u012bti";
  document.querySelectorAll(".star").forEach(b=>b.onclick=()=>{
    const u=decodeURIComponent(b.dataset.u);
    if(favs[u])delete favs[u]; else{const r=rowsAll().find(x=>x.url===u); if(r)favs[u]=r;}
    saveFavs(); render();
  });
  document.querySelectorAll("th[data-k]").forEach(th=>{
    const a=th.querySelector(".arr"); if(!a)return;
    a.textContent=(th.dataset.k===sortK)?(sortDir>0?"\u25b2":"\u25bc"):"";
  });
}
document.querySelectorAll("th[data-k]").forEach(th=>{
  if(th.dataset.k==="fav")return;
  th.onclick=()=>{const k=th.dataset.k; if(sortK===k)sortDir*=-1; else{sortK=k; sortDir=1;} render();};
});
["q","maxp","minm","onlyvalid","onlynew"].forEach(id=>{
  const el=document.getElementById(id);
  el.addEventListener(el.type==="checkbox"?"change":"input", render);
});
render();
</script>
</body></html>""".replace("__TS__", esc(ts)).replace("__DATA__", data_json)


def send_email(subject: str, html_body: str) -> None:
    host = os.environ.get("SMTP_HOST")
    to_addr = os.environ.get("MAIL_TO")
    if not host or not to_addr:
        log("Email skipped (SMTP_HOST / MAIL_TO not set).")
        return
    port = int(os.environ.get("SMTP_PORT", "465"))
    user = os.environ.get("SMTP_USER", "")
    password = os.environ.get("SMTP_PASS", "")
    from_addr = os.environ.get("MAIL_FROM", user or to_addr)

    msg = MIMEMultipart("alternative")
    msg["Subject"] = subject
    msg["From"] = from_addr
    msg["To"] = to_addr
    msg.attach(MIMEText("Open in an HTML-capable client.", "plain"))
    msg.attach(MIMEText(html_body, "html"))

    try:
        if port == 465:
            with smtplib.SMTP_SSL(host, port, timeout=30) as s:
                if user:
                    s.login(user, password)
                s.sendmail(from_addr, [to_addr], msg.as_string())
        else:
            with smtplib.SMTP(host, port, timeout=30) as s:
                s.starttls()
                if user:
                    s.login(user, password)
                s.sendmail(from_addr, [to_addr], msg.as_string())
        log(f"Email sent to {to_addr}.")
    except Exception as exc:  # noqa: BLE001 - we just want to log and continue
        log(f"Email failed: {exc}")


# --------------------------------------------------------------------------
# State maintenance
# --------------------------------------------------------------------------
def prune_seen(seen: dict) -> dict:
    cutoff = today() - relativedelta(days=SEEN_KEEP_DAYS)
    return {u: t for u, t in seen.items()
            if date.fromisoformat(t[:10]) >= cutoff}


def prune_matches(matches: list[dict]) -> list[dict]:
    cutoff = today() - relativedelta(days=MATCH_KEEP_DAYS)
    return [m for m in matches
            if date.fromisoformat(m["first_seen"][:10]) >= cutoff]


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------
def main() -> int:
    cfg = load_yaml(CONFIG_PATH)
    sources = cfg.get("sources") or ["https://www.ss.lv/lv/transport/cars/"]
    f = cfg.get("filters") or {}
    scan = cfg.get("scan") or {}
    report_cfg = cfg.get("report") or {}

    delay = float(scan.get("request_delay_seconds", 1.5))
    max_pages = int(scan.get("max_pages_per_source", 3))
    detail_limit = int(scan.get("detail_fetch_limit", 60))
    top_n = int(report_cfg.get("top_n", 40))

    seen = load_json(SEEN_PATH, {})
    first_run = len(seen) == 0
    stored_matches = load_json(MATCHES_PATH, [])
    known_match_urls = {m["url"] for m in stored_matches}

    now_iso = datetime.now(timezone.utc).isoformat()

    # 1) collect current ads from all sources
    current: dict[str, dict] = {}
    for src in sources:
        for n in range(1, max_pages + 1):
            url = page_url(src, n)
            log(f"Fetching listing: {url}")
            html_text = fetch(url, delay)
            if not html_text:
                break
            ads = parse_listing(html_text)
            log(f"  parsed {len(ads)} ads")
            if not ads:
                break
            for ad in ads:
                current.setdefault(ad["url"], ad)

    log(f"Total unique ads seen this run: {len(current)}")
    if not current:
        log("WARNING: no ads parsed. The page layout may have changed, "
            "or the source URL is wrong. Check config.yaml sources.")

    # 2) which are new + pass the cheap pre-filter
    new_urls = [u for u in current if u not in seen]
    log(f"New ads since last run: {len(new_urls)}"
        + (" (first run -> seeding)" if first_run else ""))

    candidates = [current[u] for u in new_urls if passes_prefilter(current[u], f)]
    candidates.sort(key=lambda a: a.get("price") or 1_000_000)
    log(f"Passed price/year pre-filter: {len(candidates)}")

    # 3) fetch detail pages (capped) to read inspection date
    new_matches: list[dict] = []
    fetched = 0
    for ad in candidates:
        if fetched >= detail_limit:
            log(f"Reached detail_fetch_limit ({detail_limit}); stopping detail fetches.")
            break
        detail = parse_detail(fetch(ad["url"], delay) or "")
        fetched += 1
        ok, _ = passes_inspection(detail, f)
        if not ok:
            continue
        if detail.get("detail_price"):
            ad["price"] = detail["detail_price"]
        until = detail.get("inspection_until")
        raw = detail.get("inspection_raw") or ""
        if until:
            months_left, days_left = inspection_left(until)
        else:
            months_left = days_left = None
        ad.update({
            "inspection_until": until,
            "inspection_raw": raw,
            "insp_status": inspection_status(until, raw),
            "months_left": months_left,
            "days_left": days_left,
            "place": detail.get("place"),
            "posted": detail.get("posted"),
            "first_seen": now_iso,
            "is_new": True,
        })
        new_matches.append(ad)

    new_matches.sort(key=lambda a: a.get("price") or 1_000_000)
    log(f"New matches (passed inspection filter): {len(new_matches)}")

    # 4) update rolling match list for the webpage
    keep_fields = ("url", "title", "price", "year", "engine", "mileage",
                   "inspection_until", "inspection_raw", "insp_status",
                   "months_left", "days_left", "place", "first_seen")
    for m in new_matches:
        if m["url"] not in known_match_urls:
            stored_matches.append({k: m.get(k) for k in keep_fields})
    stored_matches = prune_matches(stored_matches)
    stored_matches.sort(key=lambda a: a.get("price") or 1_000_000)

    # mark which stored records are "new" (first seen in the last 24h) for the page
    cutoff_new = datetime.now(timezone.utc) - timedelta(hours=24)
    page_rows = []
    for r in stored_matches[:300]:
        rr = dict(r)
        try:
            rr["is_new"] = datetime.fromisoformat(r["first_seen"]) >= cutoff_new
        except Exception:
            rr["is_new"] = False
        page_rows.append(rr)

    # 5) write webpage (interactive: sort / filter / pinned favourites)
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(render_page_html(page_rows, ts), encoding="utf-8")
    log(f"Wrote {REPORT_PATH} ({len(page_rows)} rows)")

    # 6) email (only when there is something new and not on the seeding run)
    if new_matches and not first_run:
        subject = f"SS.LV auto: {len(new_matches)} jauns(-i) atbilstošs(-i) sludinājums(-i)"
        send_email(subject, render_email_html(new_matches[:top_n]))
    elif first_run:
        log("First run: seeded state, no email sent (avoids a huge initial blast).")

    # 7) persist state
    for u in current:
        seen[u] = now_iso
    seen = prune_seen(seen)
    save_json(SEEN_PATH, seen)
    save_json(MATCHES_PATH, stored_matches)
    log(f"State saved: {len(seen)} seen urls, {len(stored_matches)} stored matches.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
