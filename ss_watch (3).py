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
FINGERPRINTS_PATH = ROOT / "state" / "fingerprints.json"
REPORT_PATH = ROOT / "docs" / "index.html"
ARCHIVE_DIR = ROOT / "docs" / "archive"

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

    # description text (for the archived copy)
    description = ""
    desc_node = soup.select_one("#msg_div_msg") or soup.select_one(".msg_text")
    if desc_node:
        description = desc_node.get_text("\n", strip=True)

    # ad photos (best effort) for the archived copy
    images = []
    for img in soup.find_all("img"):
        src = img.get("src") or ""
        if "i.ss.lv" in src or "/gallery/" in src or src.lower().endswith(".jpg"):
            full = src if src.startswith("http") else "https:" + src if src.startswith("//") else BASE + src
            if full not in images:
                images.append(full)
        if len(images) >= 8:
            break

    return {
        "inspection_raw": insp_raw,
        "inspection_until": insp_date.isoformat() if insp_date else None,
        "detail_price": price,
        "posted": posted,
        "place": fields.get("vieta"),
        "fields": fields,
        "description": description,
        "images": images,
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


def posted_to_iso(posted: str | None) -> str | None:
    """'dd.mm.yyyy' -> 'yyyy-mm-dd' so dates sort chronologically. None-safe."""
    if not posted:
        return None
    m = re.match(r"(\d{2})\.(\d{2})\.(\d{4})", posted.strip())
    if not m:
        return None
    d, mo, y = m.groups()
    return f"{y}-{mo}-{d}"


def parse_mileage_km(text: str | None) -> int | None:
    """Exact kilometres. 'tūkst.' -> ×1000 ('6.5 tūkst.' -> 6500),
    '255 000' -> 255000, bare '7' -> 7 (a brand-new car's delivery km)."""
    if not text:
        return None
    t = text.lower().replace("\xa0", " ")
    m = re.search(r"\d[\d\s.,]*", t)
    if not m:
        return None
    raw = m.group(0).strip()
    if "kst" in t:                       # thousands (may be decimal)
        try:
            return int(round(float(raw.replace(",", ".").replace(" ", "")) * 1000))
        except ValueError:
            return None
    digits = re.sub(r"[^\d]", "", raw)
    return int(digits) if digits else None


def parse_mileage_k(text: str | None) -> float | None:
    """Thousands of km, for the page's mileage filter/sort. 7 km -> 0.0."""
    km = parse_mileage_km(text)
    return None if km is None else round(km / 1000, 1)


LV_MONTHS = {"janv": 1, "febr": 2, "marts": 3, "apr": 4, "maijs": 5, "j\u016bn": 6,
             "j\u016bl": 7, "aug": 8, "sept": 9, "okt": 10, "nov": 11, "dec": 12}


def parse_reg_date(text: str | None) -> tuple[date | None, bool]:
    """'2026 februāris' -> (date(2026,2,1), True). Year only -> (date, False)."""
    if not text:
        return (None, False)
    low = text.lower()
    ym = re.search(r"(19|20)\d{2}", low)
    if not ym:
        return (None, False)
    year = int(ym.group(0))
    month = next((num for name, num in LV_MONTHS.items() if name in low), None)
    try:
        return (date(year, month or 1, 1), month is not None)
    except ValueError:
        return (None, False)


def reg_age_months(reg: date) -> int:
    rd = relativedelta(today(), reg)
    return rd.years * 12 + rd.months


PHEV_KEYWORDS = ("plug-in", "plug in", "plugin", "phev")


def is_phev_text(*texts: str | None) -> bool:
    blob = " ".join(t or "" for t in texts).lower()
    return any(k in blob for k in PHEV_KEYWORDS)


def field_get(fields: dict, needle: str) -> str | None:
    for k, v in fields.items():
        if needle in k:
            return v
    return None


def slug_from_url(url: str) -> str:
    base = url.split("?")[0].rstrip("/").split("/")[-1]
    if base.endswith(".html"):
        base = base[:-5]
    return re.sub(r"[^A-Za-z0-9_-]", "", base) or "ad"


def car_fingerprint(url: str, ad: dict) -> str | None:
    """A best-effort identity for a physical car, so re-posted ads (which get a
    new URL each time) can be recognised. Needs make/model + year + engine +
    mileage; returns None when too little is known to group safely."""
    year = ad.get("year")
    engine = (ad.get("engine") or "").strip().lower()
    mileage = (ad.get("mileage") or "").strip().lower()
    if not (year and engine and mileage):
        return None
    # make/model from the URL path: .../cars/<make>/<model>/<id>.html
    parts = [p for p in url.split("?")[0].split("/") if p]
    make_model = ""
    if "cars" in parts:
        i = parts.index("cars")
        make_model = "/".join(parts[i + 1:i + 3])
    return f"{make_model}|{year}|{engine}|{mileage}"


# --------------------------------------------------------------------------
# Report / email rendering
# --------------------------------------------------------------------------
def esc(x) -> str:
    return htmllib.escape(str(x if x is not None else ""))


def render_archive(ad: dict, detail: dict, captured_iso: str) -> str:
    """A saved, permanent copy of one ad (survives ss.lv link recycling)."""
    fields = detail.get("fields") or {}
    rows = "".join(
        f"<tr><td class='k'>{esc(k.capitalize())}</td><td>{esc(v)}</td></tr>"
        for k, v in fields.items()
    )
    imgs = "".join(
        f"<a href='{esc(u)}' target='_blank' rel='noopener'>"
        f"<img src='{esc(u)}' loading='lazy' alt=''></a>"
        for u in (detail.get("images") or [])[:8]
    )
    desc = esc(detail.get("description") or "").replace("\n", "<br>")
    price = f"{ad['price']:,} \u20ac".replace(",", " ") if ad.get("price") else "?"
    cap = captured_iso[:10]
    return f"""<!doctype html><html lang="lv"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(ad.get('title') or 'Sludin\u0101juma kopija')}</title>
<style>
 body{{font-family:system-ui,Segoe UI,Roboto,sans-serif;max-width:820px;margin:0 auto;padding:20px 16px;color:#111}}
 .note{{background:#fff7ed;border:1px solid #fed7aa;border-radius:8px;padding:10px 12px;font-size:13px;margin-bottom:16px}}
 h1{{font-size:20px;margin:0 0 4px}} .price{{font-size:20px;font-weight:700;margin:6px 0 14px}}
 table{{border-collapse:collapse;font-size:14px;margin:8px 0 16px}} td{{padding:5px 10px;border-top:1px solid #eee;vertical-align:top}}
 .k{{color:#666;white-space:nowrap}} .imgs img{{height:120px;border-radius:6px;margin:0 6px 6px 0}}
 .desc{{white-space:normal;line-height:1.5;font-size:14px;background:#fafafa;border-radius:8px;padding:12px}}
 a{{color:#1d4ed8}}
</style></head><body>
<div class="note">\U0001F4C4 Š\u012b ir <b>arhiv\u0113ta kopija</b>, kas saglab\u0101ta {cap}. Ori\u0123in\u0101ls:
 <a href="{esc(ad.get('url') or '')}" target="_blank" rel="noopener">{esc(ad.get('url') or '')}</a>
 (saite var b\u016bt nov\u0113lota vai aizst\u0101ta ar citu auto).</div>
<h1>{esc(ad.get('title') or '')}</h1>
<div class="price">{esc(price)}</div>
<div class="imgs">{imgs}</div>
<table>{rows}</table>
<div class="desc">{desc}</div>
</body></html>"""


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
        ek = " \u26a1EKII" if m.get("ekii") else ""
        rows.append(
            "<tr>"
            f"<td><a href='{esc(m['url'])}'>{esc(m['title'])}</a>{esc(ek)}</td>"
            f"<td style='white-space:nowrap;font-weight:600'>{esc(price)}</td>"
            f"<td>{esc(m.get('year') or '')}</td>"
            f"<td>{esc(m.get('engine') or '')}</td>"
            f"<td style='white-space:nowrap'>{esc(insp_text(m))}</td>"
            f"<td style='white-space:nowrap'>{esc(m.get('posted') or '')}</td>"
            f"<td>{esc(m.get('place') or '')}</td>"
            "</tr>"
        )
    body = "\n".join(rows) or "<tr><td colspan=7>Nav rezultātu.</td></tr>"
    return f"""<!doctype html><html lang="lv"><head><meta charset="utf-8"></head>
<body style="font-family:system-ui,Segoe UI,Roboto,sans-serif;color:#111">
<h2 style="font-size:17px">Jaunie sludinājumi ({len(matches)})</h2>
<div style="color:#666;font-size:12px;margin-bottom:10px">{ts} &middot; lētākie augšā</div>
<table style="border-collapse:collapse;font-size:14px" border="0" cellpadding="6">
<thead><tr style="background:#111;color:#fff;text-align:left">
<th>Sludinājums</th><th>Cena</th><th>Gads</th><th>Dzinējs</th>
<th>Tehniskā apskate</th><th>Datums</th><th>Vieta</th></tr></thead>
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
  .tabs{display:flex;flex-wrap:wrap;gap:8px;margin-bottom:14px}
  .tab{border:1px solid #d4d4d8;background:#fff;border-radius:999px;padding:8px 18px;
    font-size:14px;font-weight:600;cursor:pointer;color:#333}
  .tab.active{background:#111;color:#fff;border-color:#111}
  .controls{display:flex;flex-wrap:wrap;gap:10px 14px;align-items:center;margin-bottom:14px;
    background:#fff;border:1px solid #e6e6e6;border-radius:10px;padding:12px}
  .controls input[type=text],.controls input[type=number]{border:1px solid #ccc;border-radius:7px;
    padding:6px 8px;font-size:14px}
  .controls select{border:1px solid #ccc;border-radius:7px;padding:6px 8px;font-size:13px;background:#fff}
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
  .b2{border-radius:4px;padding:1px 6px;font-size:11px;margin-left:4px;white-space:nowrap}
  .rep{background:#6b7280;color:#fff}
  .ta2{background:#7c3aed;color:#fff}
  .ek{background:#0d9488;color:#fff}
  .ekok{background:#15803d;color:#fff}
  .cnew{background:#2563eb;color:#fff}
  .cused{background:#9ca3af;color:#fff}
  .star{background:none;border:none;cursor:pointer;font-size:18px;line-height:1;color:#e0b400;padding:0}
  .cpy{font-size:11px;color:#6b7280;margin-left:6px;white-space:nowrap}
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
  <div id="tabs" class="tabs"></div>
  <div class="controls">
    <input id="q" type="text" placeholder="Mekl\u0113t (nosaukums, dzin\u0113js)...">
    <label>Cena <input id="minp" type="number" style="width:74px" placeholder="no">\u2013<input id="maxp" type="number" style="width:74px" placeholder="l\u012bdz"></label>
    <label>Gads <input id="ymin" type="number" style="width:60px" placeholder="no">\u2013<input id="ymax" type="number" style="width:60px" placeholder="l\u012bdz"></label>
    <label>Maks. nobr. t\u016bkst. <input id="mmax" type="number" style="width:70px"></label>
    <label>Min. TA m\u0113n. <input id="minm" type="number" style="width:60px"></label>
    <select id="fuelf"><option value="">Visas degvielas</option><option value="elektro">Elektro</option><option value="plug-in">Plug-in</option><option value="hibr\u012bds">Hibr\u012bds</option><option value="benz\u012bns">Benz\u012bns</option><option value="d\u012bzelis">D\u012bzelis</option><option value="g\u0101ze">G\u0101ze</option></select>
    <select id="condf"><option value="">Jebkur\u0161 st\u0101voklis</option><option value="new">Jauni auto</option><option value="used">Lietoti</option></select>
    <label><input id="onlyvalid" type="checkbox"> Tikai ar der\u012bgu TA</label>
    <label><input id="onlynew" type="checkbox"> Tikai jaunie</label>
    <label><input id="hiderep" type="checkbox"> Pasl\u0113pt atk\u0101rtotos</label>
    <label><input id="onlyekii" type="checkbox"> Tikai EKII</label>
    <span id="stat" class="stat"></span>
  </div>
  <table id="tbl"><thead><tr>
    <th data-k="fav">\u2605</th>
    <th data-k="title">Sludin\u0101jums <span class="arr"></span></th>
    <th data-k="price">Cena <span class="arr"></span></th>
    <th data-k="year">Gads <span class="arr"></span></th>
    <th data-k="engine">Dzin\u0113js <span class="arr"></span></th>
    <th data-k="mileage_k">Nobraukums <span class="arr"></span></th>
    <th data-k="months_left">Tehnisk\u0101 apskate <span class="arr"></span></th>
    <th data-k="posted_iso">Datums <span class="arr"></span></th>
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
  if(k==="title"||k==="engine"||k==="place"||k==="mileage"||k==="posted_iso"){
    const x=(a[k]||"").toString().toLowerCase(),y=(b[k]||"").toString().toLowerCase();
    return x<y?-1:x>y?1:0;
  }
  let x=a[k],y=b[k];
  x=(x==null)?Infinity:x; y=(y==null)?Infinity:y;
  return x<y?-1:x>y?1:0;
}
function passFilter(r){
  const q=document.getElementById("q").value.trim().toLowerCase();
  if(q){const hay=((r.title||"")+" "+(r.engine||"")).toLowerCase(); if(!hay.includes(q))return false;}
  const maxp=parseFloat(document.getElementById("maxp").value);
  if(!isNaN(maxp)&&(r.price==null||r.price>maxp))return false;
  const minp=parseFloat(document.getElementById("minp").value);
  if(!isNaN(minp)&&(r.price==null||r.price<minp))return false;
  const ymin=parseFloat(document.getElementById("ymin").value);
  if(!isNaN(ymin)&&(r.year==null||r.year<ymin))return false;
  const ymax=parseFloat(document.getElementById("ymax").value);
  if(!isNaN(ymax)&&(r.year==null||r.year>ymax))return false;
  const mmax=parseFloat(document.getElementById("mmax").value);
  if(!isNaN(mmax)&&(r.mileage_k==null||r.mileage_k>mmax))return false;
  const minm=parseFloat(document.getElementById("minm").value);
  if(!isNaN(minm)){if(r.insp_status!=="valid"||r.months_left==null||r.months_left<minm)return false;}
  if(document.getElementById("onlyvalid").checked&&r.insp_status!=="valid")return false;
  if(document.getElementById("onlynew").checked&&!r.is_new)return false;
  if(document.getElementById("hiderep").checked&&r.is_repeat)return false;
  const fv=document.getElementById("fuelf").value;
  if(fv&&(r.fuel_cat||"")!==fv)return false;
  const sv=activeTab;
  if(sv&&!((r.labels||[]).includes(sv)))return false;
  if(document.getElementById("onlyekii").checked&&!(r.ekii||r.ekii_eligible))return false;
  const cf=document.getElementById("condf").value;
  if(cf&&(r.condition||"")!==cf)return false;
  return true;
}
function rowHtml(r,fav){
  const price=r.price!=null?(r.price.toLocaleString("lv-LV")+" \u20ac"):"?";
  let badge=r.is_new?' <span class="badge">JAUNS</span>':"";
  if(r.ekii_eligible)badge+=' <span class="b2 ekok" title="'+esc(r.reg||"")+'">EKII \u2713'+(r.ekii_reason?(" "+esc(r.ekii_reason)):"")+'</span>';
  else if(r.ekii)badge+=' <span class="b2 ek">EKII</span>';
  if(r.fuel_cat==="elektro"||r.fuel_cat==="plug-in"||r.fuel_cat==="hibr\u012bds"){
    if(r.condition==="new")badge+=' <span class="b2 cnew" title="'+esc(r.reg||"")+'">JAUNS AUTO</span>';
    else if(r.condition==="used")badge+=' <span class="b2 cused">LIETOTS</span>';
  }
  if(r.ta_renewed)badge+=' <span class="b2 ta2">TA ATJAUNOTS</span>';
  if(r.is_repeat)badge+=' <span class="b2 rep">ATK\u0100RTOTS'+(r.seen_count>1?(" \u00d7"+r.seen_count):"")+'</span>';
  const star=fav?"\u2605":"\u2606";
  const eng=esc(r.engine|| (r.fuel_cat?r.fuel_cat:""));
  return '<tr class="'+(fav?"favrow":"")+'">'
    +'<td><button class="star" data-u="'+encodeURIComponent(r.url)+'">'+star+'</button></td>'
    +'<td><a href="'+esc(r.url)+'" target="_blank" rel="noopener">'+esc(r.title)+'</a>'+badge
      +(r.archive?(' <a class="cpy" href="'+esc(r.archive)+'" target="_blank" rel="noopener">kopija</a>'):'')+'</td>'
    +'<td class="num">'+price+'</td>'
    +'<td>'+esc(r.year||"")+'</td>'
    +'<td>'+eng+'</td>'
    +'<td>'+esc(r.mileage||"")+'</td>'
    +'<td>'+inspCell(r)+'</td>'
    +'<td>'+esc(r.posted||"")+'</td>'
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
  document.getElementById("body").innerHTML=html||'<tr><td colspan="9" style="padding:20px;color:#888">Nav rezult\u0101tu</td></tr>';
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
let activeTab="";
(function(){
  const order=[]; DATA.forEach(r=>(r.labels||[]).forEach(l=>{if(!order.includes(l))order.push(l);}));
  const tabs=document.getElementById("tabs");
  const count=v=> v===""?DATA.length:DATA.filter(r=>(r.labels||[]).includes(v)).length;
  const mk=(val,txt)=>{const b=document.createElement("button");
    b.className="tab"+(val===activeTab?" active":"");b.dataset.v=val;
    b.textContent=txt+" ("+count(val)+")";
    b.onclick=()=>{activeTab=val;document.querySelectorAll(".tab").forEach(t=>t.classList.toggle("active",t.dataset.v===val));render();};
    tabs.appendChild(b);};
  mk("","Visi"); order.forEach(l=>mk(l,l));
})();
["q","minp","maxp","ymin","ymax","mmax","minm","onlyvalid","onlynew","hiderep","fuelf","onlyekii","condf"].forEach(id=>{
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


def prune_fingerprints(fps: dict) -> dict:
    """Forget cars we haven't seen for a long time, to bound the store."""
    cutoff = today() - relativedelta(days=180)
    out = {}
    for k, v in fps.items():
        stamp = (v.get("last_seen") or v.get("first_seen") or "")[:10]
        try:
            if date.fromisoformat(stamp) >= cutoff:
                out[k] = v
        except (ValueError, TypeError):
            out[k] = v
    return out


def fuel_category(text: str | None) -> str:
    """Normalise an engine/Motors string to a fuel bucket."""
    t = (text or "").lower()
    if "plug" in t:
        return "plug-in"
    if "hibr" in t:
        return "hibrīds"
    if "elektr" in t:
        return "elektro"
    if "d\u012bzel" in t or "dizel" in t:
        return "dīzelis"
    if "benz" in t:
        return "benzīns"
    if "g\u0101z" in t or "gaz" in t:
        return "gāze"
    return ""


def has_ekii(*texts: str | None) -> bool:
    """True if any text mentions the EKII subsidy."""
    return "ekii" in " ".join(t or "" for t in texts).lower()


def normalize_searches(cfg: dict) -> list[dict]:
    """Use cfg['searches'] if present; otherwise build a single search from the
    legacy cfg['filters'] + cfg['sources'] block (backward compatible)."""
    if cfg.get("searches"):
        out = []
        for s in cfg["searches"]:
            s = dict(s)
            s.setdefault("label", "Meklējums")
            s.setdefault("sources", cfg.get("sources") or [])
            out.append(s)
        return out
    f = dict(cfg.get("filters") or {})
    f["label"] = "Visi"
    f["sources"] = cfg.get("sources") or ["https://www.ss.lv/lv/transport/cars/"]
    return [f]


def passes_fuel_keywords(fuel_cat: str, title: str, desc: str, search: dict) -> bool:
    fuels = search.get("fuel_types")
    if fuels:
        hay = (fuel_cat + " " + (title or "")).lower()
        if not any(ft.lower() in hay for ft in fuels):
            return False
    req = search.get("require_keywords")
    if req:
        blob = ((title or "") + " " + (desc or "")).lower()
        if not any(k.lower() in blob for k in req):
            return False
    return True


def run_search(search: dict, scan: dict, seen: dict, fps: dict,
               now_iso: str) -> list[dict]:
    """Run one named search and return its newly-matched records.
    Mutates `seen` and `fps`."""
    delay = float(scan.get("request_delay_seconds", 1.5))
    max_pages = int(search.get("max_pages", scan.get("max_pages_per_source", 3)))
    detail_limit = int(search.get("detail_fetch_limit",
                                 scan.get("detail_fetch_limit", 60)))
    label = search.get("label", "Meklējums")

    current: dict[str, dict] = {}
    for src in search.get("sources", []):
        for n in range(1, max_pages + 1):
            url = page_url(src, n)
            log(f"[{label}] Fetching: {url}")
            html_text = fetch(url, delay)
            if not html_text:
                break
            ads = parse_listing(html_text)
            log(f"[{label}]   parsed {len(ads)} ads")
            if not ads:
                break
            for ad in ads:
                ad["_src"] = src
                current.setdefault(ad["url"], ad)

    new_urls = [u for u in current if u not in seen]
    require_phev = search.get("require_phev")
    ps_min_year = search.get("prescreen_min_year")
    ps_max_mk = search.get("prescreen_max_mileage_k")

    def listing_ok(ad: dict) -> bool:
        if not passes_prefilter(ad, search):
            return False
        if require_phev and not is_phev_text(ad.get("title")):
            return False
        if ps_min_year is not None or ps_max_mk is not None:
            y_ok = ps_min_year is not None and (ad.get("year") or 0) >= ps_min_year
            mk = parse_mileage_k(ad.get("mileage"))
            m_ok = (ps_max_mk is not None and mk is not None and mk <= ps_max_mk)
            if not (y_ok or m_ok):
                return False
        return True

    candidates = [current[u] for u in new_urls if listing_ok(current[u])]
    candidates.sort(key=lambda a: a.get("price") or 1_000_000)
    log(f"[{label}] unique={len(current)} new={len(new_urls)} "
        f"passed-prefilter={len(candidates)}")

    matches: list[dict] = []
    fetched = 0
    for ad in candidates:
        if fetched >= detail_limit:
            log(f"[{label}] reached detail_fetch_limit ({detail_limit})")
            break
        detail = parse_detail(fetch(ad["url"], delay) or "")
        fetched += 1
        ok, _ = passes_inspection(detail, search)
        if not ok:
            continue
        if detail.get("detail_price"):
            ad["price"] = detail["detail_price"]

        until = detail.get("inspection_until")
        raw = detail.get("inspection_raw") or ""
        months_left, days_left = inspection_left(until) if until else (None, None)
        now_valid = inspection_status(until, raw) == "valid"

        fields = detail.get("fields") or {}
        desc = detail.get("description")
        is_phev = is_phev_text(ad.get("title"), desc)
        if require_phev and not is_phev:
            continue

        fuel_cat = ("plug-in" if is_phev
                    else fuel_category(fields.get("motors") or ad.get("engine")))
        if not fuel_cat and "/electric-cars/" in ad["url"]:
            fuel_cat = "elektro"
        ekii = has_ekii(ad.get("title"), desc)

        # exact mileage + registration month (for the new-PHEV EKII test)
        mileage_km = (parse_mileage_km(field_get(fields, "nobraukums"))
                      or parse_mileage_km(ad.get("mileage")))
        reg_raw = field_get(fields, "izlaiduma")
        reg_date, has_month = parse_reg_date(reg_raw)
        new_by_km = mileage_km is not None and mileage_km <= 6000
        new_by_age = has_month and reg_date is not None and reg_age_months(reg_date) <= 6
        is_new_car = new_by_km or new_by_age
        condition = ("new" if is_new_car
                     else "used" if (mileage_km is not None or has_month) else "")
        ekii_eligible, ekii_reason = False, ""
        if is_phev and is_new_car:
            ekii_eligible = True
            ekii_reason = "≤6000 km" if new_by_km else "≤6 mēn."

        if not passes_fuel_keywords(fuel_cat, ad.get("title"), desc, search):
            continue

        fp = car_fingerprint(ad["url"], ad)
        is_repeat, seen_count, first_seen_any, ta_renewed = False, 1, now_iso, False
        if fp:
            prior = fps.get(fp)
            if prior:
                urls = prior.get("urls", [])
                is_repeat = ad["url"] not in urls
                seen_count = len(set(urls) | {ad["url"]})
                first_seen_any = prior.get("first_seen", now_iso)
                if is_repeat and now_valid and not prior.get("had_valid_ta"):
                    ta_renewed = True
            entry = fps.setdefault(fp, {"first_seen": now_iso, "urls": [],
                                        "had_valid_ta": False, "last_ta": None})
            if ad["url"] not in entry["urls"]:
                entry["urls"].append(ad["url"])
            entry["last_seen"] = now_iso
            if now_valid:
                entry["had_valid_ta"] = True
                entry["last_ta"] = until

        ad.update({
            "inspection_until": until, "inspection_raw": raw,
            "insp_status": inspection_status(until, raw),
            "months_left": months_left, "days_left": days_left,
            "place": detail.get("place"), "posted": detail.get("posted"),
            "posted_iso": posted_to_iso(detail.get("posted")),
            "mileage_k": parse_mileage_k(ad.get("mileage")),
            "mileage_km": mileage_km, "reg": reg_raw, "condition": condition,
            "fuel_cat": fuel_cat, "ekii": ekii,
            "ekii_eligible": ekii_eligible, "ekii_reason": ekii_reason,
            "labels": [label],
            "is_repeat": is_repeat, "seen_count": seen_count,
            "first_seen_any": first_seen_any, "ta_renewed": ta_renewed,
            "first_seen": now_iso, "is_new": True,
        })
        try:
            slug = slug_from_url(ad["url"])
            ARCHIVE_DIR.mkdir(parents=True, exist_ok=True)
            (ARCHIVE_DIR / f"{slug}.html").write_text(
                render_archive(ad, detail, now_iso), encoding="utf-8")
            ad["archive"] = f"archive/{slug}.html"
        except OSError as exc:
            log(f"  archive write failed: {exc}")
            ad["archive"] = None
        matches.append(ad)

    # remember every currently-listed car (fingerprint) and mark all as seen
    for u, ad in current.items():
        fp = car_fingerprint(u, ad)
        if fp:
            entry = fps.setdefault(fp, {"first_seen": now_iso, "urls": [],
                                        "had_valid_ta": False, "last_ta": None})
            if u not in entry["urls"]:
                entry["urls"].append(u)
            entry["last_seen"] = now_iso
        seen[u] = now_iso

    log(f"[{label}] matches: {len(matches)}")
    return matches


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------
def main() -> int:
    cfg = load_yaml(CONFIG_PATH)
    scan = cfg.get("scan") or {}
    report_cfg = cfg.get("report") or {}
    top_n = int(report_cfg.get("top_n", 40))
    searches = normalize_searches(cfg)

    seen = load_json(SEEN_PATH, {})
    first_run = len(seen) == 0
    stored_matches = load_json(MATCHES_PATH, [])
    known_match_urls = {m["url"] for m in stored_matches}
    fps = load_json(FINGERPRINTS_PATH, {})
    now_iso = datetime.now(timezone.utc).isoformat()

    # run every configured search (each with its own price band / fuel / rules)
    all_matches: list[dict] = []
    for s in searches:
        all_matches.extend(run_search(s, scan, seen, fps, now_iso))

    # dedup across searches by URL, merging the labels that matched
    by_url: dict[str, dict] = {}
    for m in all_matches:
        if m["url"] in by_url:
            for lb in m.get("labels", []):
                if lb not in by_url[m["url"]]["labels"]:
                    by_url[m["url"]]["labels"].append(lb)
        else:
            by_url[m["url"]] = m
    new_matches = sorted(by_url.values(), key=lambda a: a.get("price") or 1_000_000)
    log(f"Total new matches across searches: {len(new_matches)}"
        + (" (first run -> seeding)" if first_run else ""))

    # rolling match list for the webpage
    keep_fields = ("url", "title", "price", "year", "engine", "mileage",
                   "mileage_k", "inspection_until", "inspection_raw",
                   "insp_status", "months_left", "days_left", "place",
                   "first_seen", "posted", "posted_iso", "archive",
                   "fuel_cat", "ekii", "ekii_eligible", "ekii_reason",
                   "mileage_km", "reg", "condition", "labels",
                   "is_repeat", "seen_count", "first_seen_any", "ta_renewed")
    for m in new_matches:
        if m["url"] not in known_match_urls:
            stored_matches.append({k: m.get(k) for k in keep_fields})
    stored_matches = prune_matches(stored_matches)
    stored_matches.sort(key=lambda a: a.get("price") or 1_000_000)

    cutoff_new = datetime.now(timezone.utc) - timedelta(hours=24)
    page_rows = []
    for r in stored_matches[:400]:
        rr = dict(r)
        try:
            rr["is_new"] = datetime.fromisoformat(r["first_seen"]) >= cutoff_new
        except Exception:
            rr["is_new"] = False
        page_rows.append(rr)

    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(render_page_html(page_rows, ts), encoding="utf-8")
    log(f"Wrote {REPORT_PATH} ({len(page_rows)} rows)")

    if new_matches and not first_run:
        subject = f"SS.LV auto: {len(new_matches)} jauns(-i) sludinājums(-i)"
        send_email(subject, render_email_html(new_matches[:top_n]))
    elif first_run:
        log("First run: seeded state, no email sent (avoids a huge initial blast).")

    seen = prune_seen(seen)
    save_json(SEEN_PATH, seen)
    save_json(MATCHES_PATH, stored_matches)
    fps = prune_fingerprints(fps)
    save_json(FINGERPRINTS_PATH, fps)
    log(f"State saved: {len(seen)} seen urls, {len(stored_matches)} stored "
        f"matches, {len(fps)} car fingerprints.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
