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
from email.utils import parsedate_to_datetime
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path

import requests
import yaml
from bs4 import BeautifulSoup

# Prefer lxml (fast) but fall back to Python's built-in parser so a missing
# dependency can never crash the run.
try:
    import lxml  # noqa: F401
    BS_PARSER = "lxml"
except Exception:
    BS_PARSER = "html.parser"
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
RSS_LABELS = r"(?:Marka|Modelis|Gads|Tilpums|Nobraukums|Cena|Apskat|Марка|Модель|Год|Объ|Пробег|Цена)"


def parse_rss(xml_text: str) -> list[dict]:
    """Parse an ss.lv category RSS feed into ad dicts with a precise posting
    timestamp from <pubDate>. Regex-based (ss.lv wraps <link> plainly and text
    in CDATA), fail-safe: returns [] if the feed can't be read."""
    ads: list[dict] = []
    for it in re.findall(r"<item\b[^>]*>(.*?)</item>", xml_text or "", re.S | re.I):
        lm = (re.search(r"<link>\s*(?:<!\[CDATA\[)?\s*(https?://[^<\]\s]+)", it, re.I)
              or re.search(r"<guid[^>]*>\s*(https?://[^<\s]+)", it, re.I))
        url = lm.group(1).strip() if lm else ""
        if "/msg/" not in url:
            continue
        posted_ts = None
        pm = re.search(r"<pubDate>\s*(.*?)\s*</pubDate>", it, re.S | re.I)
        if pm:
            try:
                posted_ts = parsedate_to_datetime(pm.group(1).strip()).strftime("%Y-%m-%dT%H:%M")
            except Exception:
                posted_ts = None
        dm = re.search(r"<description>\s*(?:<!\[CDATA\[)?(.*?)(?:\]\]>)?\s*</description>", it, re.S | re.I)
        desc = re.sub(r"<[^>]+>", " ", dm.group(1)) if dm else ""
        tm = re.search(r"<title>\s*(?:<!\[CDATA\[)?(.*?)(?:\]\]>)?\s*</title>", it, re.S | re.I)
        title = tm.group(1).strip() if tm else ""

        def field(name: str):
            m = re.search(name + r":\s*(.*?)\s*(?=" + RSS_LABELS + r":|$)", desc, re.S | re.I)
            return m.group(1).strip() if m else None

        yr = field("Gads") or field("Год")
        year = None
        if yr:
            ym = re.search(r"(19|20)\d{2}", yr)
            year = int(ym.group(0)) if ym else None
        cena = field("Cena") or field("\u0426\u0435\u043d\u0430")
        price = None
        if cena:
            digits = re.sub(r"[^\d]", "", cena)
            price = int(digits) if digits else None
        if not title:
            title = " ".join(x for x in [field("Marka"), field("Modelis")] if x)
        ads.append({"url": url, "title": title, "year": year, "price": price,
                    "mileage": field("Nobraukums") or field("Пробег"),
                    "engine": field("Tilpums") or "", "thumb": "",
                    "posted_ts": posted_ts})
    return ads


def parse_listing(html_text: str) -> list[dict]:
    """Extract ad rows from a listing page.

    We find ads by their detail-page links (/msg/.../*.html) rather than
    relying on a specific row-id scheme, so this keeps working even if ss.lv
    tweaks its table markup. Each ad has two such links (thumbnail + title);
    we keep the one that carries the title text and dedupe by URL."""
    soup = BeautifulSoup(html_text, BS_PARSER)
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
        thumb = ""
        if row is not None:
            value_cells = [td.get_text(" ", strip=True)
                           for td in row.select("td.msga2-o")]
            if not value_cells:
                value_cells = [td.get_text(" ", strip=True)
                               for td in row.find_all("td")]
            img = row.find("img")
            if img is not None:
                for attr in ("src", "data-original", "data-src"):
                    v = img.get(attr) or ""
                    if v and ("ss.lv" in v or v.lower().endswith(".jpg")):
                        thumb = (v if v.startswith("http")
                                 else "https:" + v if v.startswith("//")
                                 else BASE + v)
                        break
        info = classify_cells(value_cells)
        info.update({"url": url, "title": title, "thumb": thumb})
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
    soup = BeautifulSoup(html_text, BS_PARSER)
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

    # listed date (with time when ss.lv provides it, e.g. "24.06.2026 09:00")
    posted = None
    m = re.search(r"Datums:\s*(\d{2}\.\d{2}\.\d{4})(?:\s+(\d{2}:\d{2}))?",
                  soup.get_text(" ", strip=True))
    if m:
        posted = m.group(1) + (f" {m.group(2)}" if m.group(2) else "")

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


def posted_to_ts(posted: str | None) -> str | None:
    """'dd.mm.yyyy hh:mm' -> 'yyyy-mm-ddThh:mm' (local, for 'X hours ago').
    Falls back to date only when no time is given."""
    if not posted:
        return None
    m = re.match(r"(\d{2})\.(\d{2})\.(\d{4})(?:\s+(\d{2}):(\d{2}))?", posted.strip())
    if not m:
        return None
    d, mo, y, hh, mm = m.groups()
    return f"{y}-{mo}-{d}" + (f"T{hh}:{mm}" if hh else "")


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


def battery_kwh(*texts: str | None) -> float | None:
    """Pull battery capacity (kWh) out of ad text — ss.lv has no field for it.
    Matches '40 kWh', '77,4 kWh', '64kwh', '40 kw/h', Cyrillic 'кВтч'. Ignores
    plain kW (motor power) by requiring the 'h'. Sanity-bounded to 5-250 kWh."""
    blob = " ".join(t or "" for t in texts).lower().replace("\xa0", " ")
    best = None
    for m in re.finditer(
            r"(\d{1,3}(?:[.,]\d)?)\s*"
            r"(?:kwh|kw\s*[·./-]?\s*h|kvth|k\s*w\s*t\s*h|квтч|квт\s*[·./-]?\s*ч)",
            blob):
        val = float(m.group(1).replace(",", "."))
        if 5 <= val <= 250:
            best = val if best is None else best
    return best


HEATPUMP_KEYWORDS = ("siltums\u016bkn", "siltumsukn", "heat pump", "heatpump",
                     "\u0442\u0435\u043f\u043b\u043e\u0432\u043e\u0439 \u043d\u0430\u0441\u043e\u0441",
                     "\u0442\u0435\u043f\u043b\u043e\u043d\u0430\u0441\u043e\u0441",
                     "\u0442\u0435\u043f\u043b. \u043d\u0430\u0441\u043e\u0441")


def has_heat_pump(*texts: str | None) -> bool:
    blob = " ".join(t or "" for t in texts).lower()
    return any(k in blob for k in HEATPUMP_KEYWORDS)


def field_get(fields: dict, needle: str) -> str | None:
    for k, v in fields.items():
        if needle in k:
            return v
    return None


def split_make_model(url: str, fields: dict) -> tuple[str, str]:
    """Make + model. Prefer the detail 'Marka' field ('Volkswagen Tayron'),
    fall back to the URL path. Multi-word makes split imperfectly (rare)."""
    marka = (fields.get("marka") or "").strip()
    if marka:
        toks = marka.split()
        return (toks[0], " ".join(toks[1:]))
    parts = [p for p in url.split("?")[0].split("/") if p]
    if "cars" in parts:
        i = parts.index("cars")
        seg = parts[i + 1:i + 3]
        if seg and seg[0] != "electric-cars":
            mk = seg[0].replace("-", " ").title()
            md = seg[1].replace("-", " ").title() if len(seg) > 1 else ""
            return (mk, md)
    return ("", "")


def slug_from_url(url: str) -> str:
    base = url.split("?")[0].rstrip("/").split("/")[-1]
    if base.endswith(".html"):
        base = base[:-5]
    return re.sub(r"[^A-Za-z0-9_-]", "", base) or "ad"


def car_key(ad: dict) -> str | None:
    """Best-effort identity for a physical car, so a re-posted ad (new URL,
    possibly new price) can be recognised as the same vehicle. Built from the
    enriched record (make/model from the detail 'Marka' field, year, engine or
    fuel, and mileage in thousands). Returns None when too little is known.
    Works for EVs too, where engine is blank but fuel = elektro."""
    year = ad.get("year")
    make = (ad.get("make") or "").strip().lower()
    model = (ad.get("model") or "").strip().lower()
    motor = (ad.get("engine") or ad.get("fuel_cat") or "").strip().lower()
    km = ad.get("mileage_km")
    if not (year and make and model and motor and km is not None):
        return None
    return f"{make}|{model}|{year}|{motor}|{int(round(km / 1000))}"


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


def default_banners() -> list[dict]:
    return [
        {"title": "Jūsu reklāma šeit",
         "text": "Sasniedziet pircējus, kas tieši tagad meklē elektroauto. "
                 "Reklamējiet savu uzņēmumu šajā vietā.",
         "cta": "Sazināties", "url": "mailto:info@example.com", "placeholder": True},
        {"title": "Aviloo baterijas sertifikāts",
         "text": "Pārbaudiet lietota elektroauto baterijas patieso veselību "
                 "pirms pirkšanas.",
         "cta": "Uzzināt vairāk", "url": "https://www.aviloo.com/"},
        {"title": "VIN un vēstures pārbaude",
         "text": "Pasūtiet auto VIN un vēstures pārbaudi pirms darījuma.",
         "cta": "Pasūtīt", "url": "https://www.provin.lv/"},
    ]


def render_banners(banners: list[dict]) -> str:
    out = []
    for b in banners:
        ph = " ph" if b.get("placeholder") else ""
        url = b.get("url", "#")
        rel = ' target="_blank" rel="noopener sponsored"' if str(url).startswith("http") else ""
        out.append(
            f'<div class="banner{ph}"><h3>{esc(b.get("title",""))}</h3>'
            f'<p>{esc(b.get("text",""))}</p>'
            f'<a class="cta" href="{esc(url)}"{rel}>{esc(b.get("cta","Uzzināt vairāk"))}</a></div>'
        )
    out.append('<div class="rail-note">Reklāma</div>')
    return "\n".join(out)


def render_page_html(rows: list[dict], ts: str, tab_labels: list[str],
                     banners: list[dict] | None = None) -> str:
    """Interactive page: sortable, filterable, with pinned favourites
    (favourites persist in the browser via localStorage)."""
    data_json = json.dumps(rows, ensure_ascii=False)
    tabs_json = json.dumps(tab_labels, ensure_ascii=False)
    banners_html = render_banners(banners if banners is not None else default_banners())
    return """<!doctype html>
<html lang="lv"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Elektroauto un EKII meklētava</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Manrope:wght@400;500;600;700&family=Space+Grotesk:wght@500;600;700&display=swap" rel="stylesheet">
<style>
  :root{
    --bg:#F5F7F6; --surface:#fff; --ink:#17211C; --muted:#5E6B64;
    --line:#E4E9E6; --line-2:#EEF2F0;
    --brand:#0E7C5A; --brand-ink:#0A5C43; --brand-soft:#E7F4EE;
    --amber:#B45309; --red:#B91C1C; --red-soft:#FBE7E7;
    --shadow:0 1px 2px rgba(20,40,30,.04),0 8px 26px -14px rgba(20,40,30,.14);
    --radius:14px;
  }
  *{box-sizing:border-box}
  body{font-family:'Manrope',system-ui,sans-serif;margin:0;background:var(--bg);color:var(--ink);
    -webkit-font-smoothing:antialiased;font-size:14px;line-height:1.45}
  a{color:var(--brand-ink);text-decoration:none}a:hover{text-decoration:underline}
  .appbar{background:var(--surface);border-bottom:1px solid var(--line);position:sticky;top:0;z-index:50}
  .appbar-in{max-width:1400px;margin:0 auto;padding:14px 18px;display:flex;align-items:baseline;gap:14px;flex-wrap:wrap}
  .brand{font-family:'Space Grotesk',sans-serif;font-weight:600;font-size:19px;letter-spacing:-.01em;
    color:var(--ink);display:flex;align-items:center;gap:9px}
  .brand .dot{width:11px;height:11px;border-radius:50%;background:var(--brand);box-shadow:0 0 0 4px var(--brand-soft)}
  .tagline{color:var(--muted);font-size:13px}
  .updated{margin-left:auto;color:var(--muted);font-size:12px}
  .wrap{max-width:1400px;margin:0 auto;padding:16px 14px 80px}
  .layout{display:flex;gap:22px;align-items:flex-start}
  .main{flex:1;min-width:0}
  .rail{width:248px;flex-shrink:0;display:flex;flex-direction:column;gap:14px;position:sticky;top:78px}
  .banner{background:var(--surface);border:1px solid var(--line);border-radius:var(--radius);padding:16px;box-shadow:var(--shadow)}
  .banner h3{font-family:'Space Grotesk',sans-serif;font-size:15px;margin:0 0 6px;color:var(--ink);font-weight:600}
  .banner p{margin:0 0 12px;font-size:13px;color:var(--muted);line-height:1.5}
  .banner .cta{display:inline-block;background:var(--brand);color:#fff;border-radius:9px;padding:8px 14px;font-size:13px;font-weight:600}
  .banner .cta:hover{background:var(--brand-ink);text-decoration:none}
  .banner.ph{border-style:dashed;background:var(--brand-soft)}
  .banner.ph .cta{background:transparent;color:var(--brand-ink);border:1px solid var(--brand)}
  .rail-note{font-size:11px;color:var(--muted);text-align:center;letter-spacing:.02em}
  @media(max-width:1024px){
    .layout{flex-direction:column}
    .rail{width:100%;position:static;flex-direction:row;flex-wrap:wrap}
    .rail .banner{flex:1 1 240px}
    .rail-note{width:100%}
  }
  @media(max-width:560px){.rail{flex-direction:column}.rail .banner{flex:none}}
  .tabs{display:inline-flex;flex-wrap:wrap;gap:4px;background:var(--surface);border:1px solid var(--line);
    border-radius:999px;padding:4px;margin:4px 0 16px;box-shadow:var(--shadow)}
  .tab{border:none;background:none;border-radius:999px;padding:8px 16px;font:inherit;font-weight:600;
    font-size:13.5px;cursor:pointer;color:var(--muted);white-space:nowrap;transition:background .15s,color .15s}
  .tab:hover{color:var(--ink)}
  .tab.active{background:var(--brand);color:#fff}
  .controls{display:flex;flex-wrap:wrap;gap:8px 12px;align-items:center;margin-bottom:16px;
    background:var(--surface);border:1px solid var(--line);border-radius:var(--radius);padding:12px 14px;box-shadow:var(--shadow)}
  .controls .row2{display:none;flex-wrap:wrap;gap:8px 12px;align-items:center;width:100%;
    border-top:1px solid var(--line-2);padding-top:12px;margin-top:2px}
  .controls.more .row2{display:flex}
  .controls input[type=text],.controls input[type=number],.controls select{
    border:1px solid var(--line);border-radius:9px;padding:7px 10px;font:inherit;font-size:13px;background:#fff;color:var(--ink)}
  .controls input:focus,.controls select:focus{outline:2px solid var(--brand-soft);border-color:var(--brand)}
  .controls input[type=text]{min-width:200px;flex:1 1 200px;max-width:340px}
  .controls label{font-size:13px;color:var(--muted);display:inline-flex;align-items:center;gap:6px}
  .controls input[type=checkbox]{accent-color:var(--brand);width:16px;height:16px}
  .btn{border:1px solid var(--line);border-radius:9px;padding:7px 12px;background:#fff;cursor:pointer;font:inherit;font-size:13px;color:var(--ink)}
  .btn:hover{border-color:var(--brand);color:var(--brand-ink)}
  .btn-more{margin-left:auto;font-weight:600}
  .stat{color:var(--muted);font-size:12px;width:100%;margin-top:2px}
  .tablewrap{overflow-x:auto;border-radius:var(--radius);border:1px solid var(--line);background:var(--surface);box-shadow:var(--shadow)}
  table{border-collapse:collapse;background:var(--surface);width:100%;font-size:14px;table-layout:fixed}
  thead th{text-align:left;background:var(--brand-ink);color:#fff;padding:10px 8px;font-weight:600;font-size:12px;
    white-space:nowrap;user-select:none;position:relative;overflow:hidden}
  .rsz{position:absolute;top:0;right:0;width:7px;height:100%;cursor:col-resize}
  .rsz:hover{background:rgba(255,255,255,.25)}
  th[data-k]:not([data-k=fav]){cursor:pointer}
  th .arr{opacity:.55;font-size:10px}
  td{padding:9px 8px;border-top:1px solid var(--line-2);vertical-align:middle;overflow:hidden;
    text-overflow:ellipsis;white-space:nowrap;color:var(--ink)}
  td.desccell{white-space:normal}
  .desc{display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden;font-weight:600;line-height:1.35}
  .desc a{color:var(--ink)}
  .bdg{margin-top:5px;display:flex;flex-wrap:wrap;gap:5px}
  tbody tr:hover td{background:#F8FBF9}
  .favrow td{background:#FBFAF2}
  .favrow:hover td{background:#F6F4E8}
  .num{white-space:nowrap;font-weight:600;font-family:'Space Grotesk',sans-serif;font-variant-numeric:tabular-nums}
  .price{font-weight:700;font-size:15px;font-family:'Space Grotesk',sans-serif}
  .badge,.b2{display:inline-flex;align-items:center;gap:3px;border-radius:999px;padding:2px 9px;
    font-size:11.5px;font-weight:600;line-height:1.5;white-space:nowrap}
  .badge{background:var(--brand-soft);color:var(--brand-ink)}
  .rep{background:#EEF1EF;color:#55625B}
  .pdn{background:var(--brand-soft);color:var(--brand-ink)}
  .pup{background:var(--red-soft);color:var(--red)}
  .hp{background:#E4F0F6;color:#0B6089}
  .ta2{background:#EFE9FB;color:#6D3FC4}
  .ek{background:#DEF1EA;color:#0A6E4F}
  .ekok{background:var(--brand);color:#fff}
  .cnew{background:#E5EEFB;color:#1F5FBF}
  .cused{background:#EEF1EF;color:#68746D}
  .star{background:none;border:none;cursor:pointer;font-size:18px;line-height:1;color:#D9B44A;padding:0}
  .cpy{font-size:11px;color:var(--muted);margin-left:6px;white-space:nowrap;font-weight:500}
  .thumb{height:44px;width:66px;object-fit:cover;border-radius:8px;display:block;background:#EEF2F0}
  tr.viewed td{opacity:.5}
  tr.viewed.favrow td{opacity:1}
  .vbtn{background:none;border:none;cursor:pointer;font-size:13px;color:#C4CCC7;padding:0 0 0 3px}
  .vbtn.on{color:var(--brand)}
  .ins small{color:var(--muted)}
  .ins.ok{color:var(--brand-ink);font-weight:700}
  .ins.warn{color:var(--amber)}
  .ins.bad{color:var(--red)}
  .ins.none{color:#9AA39E}
  .ins.unk{color:#BAC2BD}
  @media(max-width:820px){
    .appbar-in{padding:12px 14px}
    .updated{width:100%;margin:2px 0 0}
    .wrap{padding:14px 12px 80px}
    .controls input[type=text]{max-width:none}
    .tablewrap{overflow:visible;border:none;background:none;box-shadow:none}
    table{table-layout:auto;width:100%}
    thead{display:none}
    tbody,tr,td{display:block;width:auto!important}
    tbody tr{background:var(--surface);border:1px solid var(--line);border-radius:var(--radius);
      box-shadow:var(--shadow);margin-bottom:12px;padding:12px 14px 14px;position:relative}
    tbody tr:hover td,.favrow td{background:none}
    td{border:none;padding:3px 0;white-space:normal;overflow:visible;text-overflow:clip}
    td[data-label]{display:flex;gap:8px;align-items:baseline}
    td[data-label]::before{content:attr(data-label);color:var(--muted);font-size:12px;font-weight:600;min-width:104px}
    td.c-fav{position:absolute;top:10px;right:8px;padding:0}
    td.c-thumb{padding:0 0 10px}
    .thumb{height:180px;width:100%;border-radius:12px}
    td.c-desc{padding:0 0 4px}
    .desc{-webkit-line-clamp:3;font-size:15.5px}
    td.c-price .price{font-size:19px}
    td.c-make,td.c-model{display:none}
    td.c-year::before,td.c-engine::before{min-width:104px}
  }
  @media(prefers-reduced-motion:reduce){*{transition:none!important}}
</style></head>
<body>
  <div class="appbar"><div class="appbar-in">
    <span class="brand"><span class="dot"></span>Elektroauto meklētava</span>
    <span class="tagline">Elektro un plug-in auto ar EKII atbalstu</span>
    <span class="updated">Atjaunināts __TS__</span>
  </div></div>
  <div class="wrap">
  <div id="tabs" class="tabs"></div>
  <div class="layout">
  <div class="main">
  <div class="controls" id="controls">
    <input id="q" type="text" placeholder="Meklēt nosaukumā vai dzinējā...">
    <label>Cena <input id="minp" type="number" style="width:74px" placeholder="no">\u2013<input id="maxp" type="number" style="width:74px" placeholder="l\u012bdz"></label>
    <select id="fuelf"><option value="">Visas degvielas</option><option value="elektro">Elektro</option><option value="plug-in">Plug-in</option><option value="hibr\u012bds">Hibr\u012bds</option><option value="benz\u012bns">Benz\u012bns</option><option value="d\u012bzelis">D\u012bzelis</option><option value="g\u0101ze">G\u0101ze</option></select>
    <label title="Sludin\u0101jumi bez nor\u0101d\u012btas kWh paliek redzami">Min. kWh <input id="minkwh" type="number" style="width:64px"></label>
    <label><input id="onlyekii" type="checkbox"> Tikai EKII</label>
    <button class="btn btn-more" id="morebtn" type="button">Vair\u0101k filtru</button>
    <div class="row2">
      <label>Gads <input id="ymin" type="number" style="width:60px" placeholder="no">\u2013<input id="ymax" type="number" style="width:60px" placeholder="l\u012bdz"></label>
      <label>Maks. nobr. t\u016bkst. <input id="mmax" type="number" style="width:70px"></label>
      <label>Min. TA m\u0113n. <input id="minm" type="number" style="width:60px"></label>
      <select id="condf"><option value="">Jebkur\u0161 st\u0101voklis</option><option value="new">Jauni auto</option><option value="used">Lietoti</option></select>
      <label><input id="onlyhp" type="checkbox"> Ar siltums\u016bkni</label>
      <label><input id="onlyvalid" type="checkbox"> Tikai ar der\u012bgu TA</label>
      <label><input id="onlynew" type="checkbox"> Tikai jaunie</label>
      <label><input id="onlypc" type="checkbox"> Tikai ar cenas izmai\u0146\u0101m</label>
      <label><input id="hiderep" type="checkbox"> Pasl\u0113pt atk\u0101rtotos</label>
      <label><input id="hideviewed" type="checkbox"> Pasl\u0113pt redz\u0113tos</label>
      <button id="clrviewed" class="btn" type="button">Not\u012br\u012bt redz\u0113tos</button>
    </div>
    <span id="stat" class="stat"></span>
  </div>
  <div class="tablewrap">
  <table id="tbl">
  <colgroup>
    <col data-c="fav" data-def="44"><col data-c="thumb" data-def="78">
    <col data-c="title" data-def="204"><col data-c="make" data-def="78">
    <col data-c="model" data-def="80"><col data-c="price" data-def="82">
    <col data-c="year" data-def="48"><col data-c="engine" data-def="62">
    <col data-c="battery" data-def="72">
    <col data-c="mileage" data-def="84"><col data-c="ta" data-def="90">
    <col data-c="posted" data-def="78"><col data-c="place" data-def="82">
  </colgroup>
  <thead><tr>
    <th data-k="fav">\u2605</th>
    <th>Foto</th>
    <th data-k="title">Apraksts <span class="arr"></span></th>
    <th data-k="make">Marka <span class="arr"></span></th>
    <th data-k="model">Modelis <span class="arr"></span></th>
    <th data-k="price">Cena <span class="arr"></span></th>
    <th data-k="year">Gads <span class="arr"></span></th>
    <th data-k="engine">Dzin\u0113js <span class="arr"></span></th>
    <th data-k="battery_kwh">Baterija <span class="arr"></span></th>
    <th data-k="mileage_k">Nobraukums <span class="arr"></span></th>
    <th data-k="days_left">Tehnisk\u0101 apskate <span class="arr"></span></th>
    <th data-k="posted_iso">Datums <span class="arr"></span></th>
    <th data-k="place">Vieta <span class="arr"></span></th>
  </tr></thead><tbody id="body"></tbody></table>
  </div>
  </div>
  <aside class="rail">__BANNERS__</aside>
  </div>
</div>
<script>
const DATA = __DATA__;
const BUILD_TS = "__TS__";
const TABS = __TABS__;
const FAVKEY = "sscw_favs";
let favs = (()=>{try{return JSON.parse(localStorage.getItem(FAVKEY))||{};}catch(e){return {};}})();
function saveFavs(){localStorage.setItem(FAVKEY, JSON.stringify(favs));}
const VIEWKEY="sscw_viewed";
let viewed=(()=>{try{return JSON.parse(localStorage.getItem(VIEWKEY))||{};}catch(e){return {};}})();
function saveViewed(){localStorage.setItem(VIEWKEY, JSON.stringify(viewed));}
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
  if(k==="title"||k==="make"||k==="model"||k==="engine"||k==="place"||k==="mileage"||k==="posted_iso"){
    const x=(a[k]||"").toString().toLowerCase(),y=(b[k]||"").toString().toLowerCase();
    return x<y?-1:x>y?1:0;
  }
  const x=a[k],y=b[k];
  return x<y?-1:x>y?1:0;
}
function dirCmp(a,b){
  const k=sortK,x=a[k],y=b[k];
  const xn=(x==null||x===""),yn=(y==null||y==="");
  if(xn&&yn)return 0;
  if(xn)return 1;            // missing value -> always last
  if(yn)return -1;
  return sortDir*cmp(a,b,k);
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
  if(document.getElementById("hideviewed").checked&&viewed[r.url])return false;
  const fv=document.getElementById("fuelf").value;
  if(fv&&(r.fuel_cat||"")!==fv)return false;
  const sv=activeTab;
  if(sv&&!((r.labels||[]).includes(sv)))return false;
  if(document.getElementById("onlyekii").checked&&!(r.ekii||r.ekii_eligible))return false;
  if(document.getElementById("onlypc").checked&&!r.price_delta)return false;
  const mk=parseFloat(document.getElementById("minkwh").value);
  if(!isNaN(mk)&&r.battery_kwh!=null&&r.battery_kwh<mk)return false;
  if(document.getElementById("onlyhp").checked&&!r.heat_pump)return false;
  const cf=document.getElementById("condf").value;
  if(cf&&(r.condition||"")!==cf)return false;
  return true;
}
function rowHtml(r,fav){
  const price=r.price!=null?(r.price.toLocaleString("lv-LV")+" \u20ac"):"?";
function relPosted(r){
  const ts=r.posted_ts;
  if(!ts)return {t:esc(r.posted||""),title:esc(r.posted||"")};
  const d=new Date(ts.replace(" ","T")), now=new Date();
  if(isNaN(d))return {t:esc(r.posted||""),title:esc(r.posted||"")};
  const abs=esc(r.posted||"");
  const sameDay=d.getFullYear()===now.getFullYear()&&d.getMonth()===now.getMonth()&&d.getDate()===now.getDate();
  const hasTime=ts.length>10;
  if(sameDay){
    if(!hasTime)return {t:"\u0161odien",title:abs};
    const mins=Math.floor((now-d)/60000);
    if(mins<1)return {t:"tikko",title:abs};
    if(mins<60)return {t:"pirms "+mins+" min",title:abs};
    return {t:"pirms "+Math.floor(mins/60)+" h",title:abs};
  }
  // calendar-day difference
  const a=new Date(d.getFullYear(),d.getMonth(),d.getDate());
  const b=new Date(now.getFullYear(),now.getMonth(),now.getDate());
  const days=Math.round((b-a)/86400000);
  if(days<=0)return {t:"\u0161odien",title:abs};
  if(days===1)return {t:"vakar",title:abs};
  return {t:"pirms "+days+" d.",title:abs};
}
  let badge=r.is_new?' <span class="badge">Jauns</span>':"";
  if(r.ekii_eligible)badge+=' <span class="b2 ekok" title="'+esc(r.reg||"")+'">EKII \u2713'+(r.ekii_reason?(" "+esc(r.ekii_reason)):"")+'</span>';
  else if(r.ekii)badge+=' <span class="b2 ek">EKII</span>';
  if(r.fuel_cat==="elektro"||r.fuel_cat==="plug-in"||r.fuel_cat==="hibr\u012bds"){
    if(r.condition==="new")badge+=' <span class="b2 cnew" title="'+esc(r.reg||"")+'">Jauns auto</span>';
    else if(r.condition==="used")badge+=' <span class="b2 cused">Lietots</span>';
  }
  if(r.heat_pump)badge+=' <span class="b2 hp">\u2600 Siltums\u016bknis</span>';
  if(r.ta_renewed)badge+=' <span class="b2 ta2">TA atjaunots</span>';
  if(r.is_repeat)badge+=' <span class="b2 rep">Atk\u0101rtots'+(r.seen_count>1?(" \u00d7"+r.seen_count):"")+'</span>';
  if(r.price_delta){const ab=Math.abs(r.price_delta).toLocaleString("lv-LV"),
    was=(r.prev_price!=null?("Agr\u0101k: "+r.prev_price.toLocaleString("lv-LV")+" \u20ac"):"");
    badge+=(r.price_delta<0
      ?' <span class="b2 pdn" title="'+was+'">\u2193 '+ab+' \u20ac</span>'
      :' <span class="b2 pup" title="'+was+'">\u2191 '+ab+' \u20ac</span>');}
  const star=fav?"\u2605":"\u2606";
  const eng=esc(r.engine|| (r.fuel_cat?r.fuel_cat:""));
  const eu=encodeURIComponent(r.url);
  const vw=!!viewed[r.url];
  const rp=relPosted(r);
  return '<tr class="'+(fav?"favrow":"")+(vw?" viewed":"")+'">'
    +'<td class="c-fav" style="white-space:nowrap"><button class="star" data-u="'+eu+'">'+star+'</button>'
      +'<button class="vbtn'+(vw?" on":"")+'" data-vu="'+eu+'" title="Atz\u012bm\u0113t k\u0101 redz\u0113tu">'+(vw?"\u2713":"\u25cb")+'</button></td>'
    +'<td class="c-thumb">'+(r.thumb?('<a class="adlink" data-u="'+eu+'" href="'+esc(r.url)+'" target="_blank" rel="noopener"><img class="thumb" src="'+esc(r.thumb)+'" loading="lazy" alt=""></a>'):'')+'</td>'
    +'<td class="desccell c-desc"><div class="desc"><a class="adlink" data-u="'+eu+'" href="'+esc(r.url)+'" target="_blank" rel="noopener" title="'+esc(r.title)+'">'+esc(r.title)+'</a></div>'
      +'<div class="bdg">'+badge+(r.archive?(' <a class="cpy" href="'+esc(r.archive)+'" target="_blank" rel="noopener">kopija</a>'):'')+'</div></td>'
    +'<td class="c-make" data-label="Marka">'+esc(r.make||"")+'</td>'
    +'<td class="c-model" data-label="Modelis">'+esc(r.model||"")+'</td>'
    +'<td class="c-price num" data-label="Cena"><span class="price">'+price+'</span></td>'
    +'<td class="c-year" data-label="Gads">'+esc(r.year||"")+'</td>'
    +'<td class="c-engine" data-label="Dzin\u0113js">'+eng+'</td>'
    +'<td class="c-battery" data-label="Baterija">'+(r.battery_kwh?(r.battery_kwh+' kWh'):'')+'</td>'
    +'<td class="c-mileage" data-label="Nobraukums">'+esc(r.mileage|| (r.mileage_km!=null?(r.mileage_km.toLocaleString("lv-LV")+" km"):""))+'</td>'
    +'<td class="c-ta" data-label="Tehnisk\u0101 apskate">'+inspCell(r)+'</td>'
    +'<td class="c-posted" data-label="Datums" title="'+rp.title+'">'+rp.t+'</td>'
    +'<td class="c-place" data-label="Vieta">'+esc(r.place||"")+'</td></tr>';
}
function render(){
  const all=rowsAll();
  const favRows=all.filter(r=>favs[r.url]);
  const rest=all.filter(r=>!favs[r.url]&&passFilter(r));
  favRows.sort(dirCmp);
  rest.sort(dirCmp);
  let html="";
  favRows.forEach(r=>html+=rowHtml(r,true));
  rest.forEach(r=>html+=rowHtml(r,false));
  document.getElementById("body").innerHTML=html||'<tr><td colspan="13" style="padding:20px;color:#888">Nav rezult\u0101tu</td></tr>';
  document.getElementById("stat").textContent=favRows.length+" piesprausti \u00b7 "+rest.length+" r\u0101d\u012bti";
  document.querySelectorAll(".star").forEach(b=>b.onclick=()=>{
    const u=decodeURIComponent(b.dataset.u);
    if(favs[u])delete favs[u]; else{const r=rowsAll().find(x=>x.url===u); if(r)favs[u]=r;}
    saveFavs(); render();
  });
  document.querySelectorAll(".vbtn").forEach(b=>b.onclick=()=>{
    const u=decodeURIComponent(b.dataset.vu);
    if(viewed[u])delete viewed[u]; else viewed[u]=true;
    saveViewed(); render();
  });
  document.querySelectorAll(".adlink").forEach(a=>a.addEventListener("click",()=>{
    const u=decodeURIComponent(a.dataset.u);
    if(!viewed[u]){viewed[u]=true; saveViewed();}
    const tr=a.closest("tr"); if(tr)tr.classList.add("viewed");
  }));
  document.querySelectorAll("th[data-k]").forEach(th=>{
    const a=th.querySelector(".arr"); if(!a)return;
    a.textContent=(th.dataset.k===sortK)?(sortDir>0?"\u25b2":"\u25bc"):"";
  });
}
document.querySelectorAll("th[data-k]").forEach(th=>{
  if(th.dataset.k==="fav")return;
  th.onclick=()=>{const k=th.dataset.k; if(sortK===k)sortDir*=-1; else{sortK=k; sortDir=1;} render();};
});
let activeTab=(()=>{try{return localStorage.getItem("sscw_tab")||"";}catch(e){return "";}})();
(function(){
  const order=[]; (typeof TABS!=="undefined"?TABS:[]).forEach(l=>{if(l&&!order.includes(l))order.push(l);});
  DATA.forEach(r=>(r.labels||[]).forEach(l=>{if(!order.includes(l))order.push(l);}));
  if(activeTab && activeTab!=="" && !order.includes(activeTab))activeTab="";
  const tabs=document.getElementById("tabs");
  const count=v=> v===""?DATA.length:DATA.filter(r=>(r.labels||[]).includes(v)).length;
  const fuelFor=l=>{const t=(l||"").toLowerCase();return t.includes("elektro")?"elektro":(t.includes("plug")?"plug-in":"");};
  const mk=(val,txt)=>{const b=document.createElement("button");
    b.className="tab"+(val===activeTab?" active":"");b.dataset.v=val;
    b.textContent=txt+" ("+count(val)+")";
    b.onclick=()=>{activeTab=val;
      try{localStorage.setItem("sscw_tab",val);}catch(e){}
      document.getElementById("fuelf").value=fuelFor(val);
      document.querySelectorAll(".tab").forEach(t=>t.classList.toggle("active",t.dataset.v===val));
      render();};
    tabs.appendChild(b);};
  mk("","Visi"); order.forEach(l=>mk(l,l));
  if(activeTab)document.getElementById("fuelf").value=fuelFor(activeTab);
})();
// ---- Excel-like resizable columns (widths remembered in the browser) ----
const COLW_KEY="sscw_colw2";
let colw=(()=>{try{return JSON.parse(localStorage.getItem(COLW_KEY))||{};}catch(e){return {};}})();
function saveColw(){localStorage.setItem(COLW_KEY,JSON.stringify(colw));}
const COLS=[...document.querySelectorAll("#tbl colgroup col")];
function applyColw(){let total=0;COLS.forEach(c=>{const w=colw[c.dataset.c]||parseInt(c.dataset.def,10);c.style.width=w+"px";total+=w;});document.getElementById("tbl").style.width=total+"px";}
applyColw();
[...document.querySelectorAll("#tbl thead th")].forEach((th,i)=>{
  const col=COLS[i]; if(!col)return;
  const h=document.createElement("span"); h.className="rsz"; th.appendChild(h);
  h.addEventListener("click",e=>e.stopPropagation());
  h.addEventListener("mousedown",e=>{
    e.preventDefault(); e.stopPropagation();
    const sx=e.clientX, sw=col.getBoundingClientRect().width;
    document.body.style.userSelect="none";
    function mm(ev){colw[col.dataset.c]=Math.max(40,Math.round(sw+(ev.clientX-sx))); applyColw();}
    function mu(){document.removeEventListener("mousemove",mm); document.removeEventListener("mouseup",mu); document.body.style.userSelect=""; saveColw();}
    document.addEventListener("mousemove",mm); document.addEventListener("mouseup",mu);
  });
});
["q","minp","maxp","ymin","ymax","mmax","minm","minkwh","onlyvalid","onlynew","hiderep","hideviewed","fuelf","onlyhp","onlyekii","onlypc","condf"].forEach(id=>{
  const el=document.getElementById(id);
  el.addEventListener(el.type==="checkbox"?"change":"input", render);
});
document.getElementById("clrviewed").onclick=()=>{viewed={}; saveViewed(); render();};
(function(){const c=document.getElementById("controls"),b=document.getElementById("morebtn");
  b.onclick=()=>{c.classList.toggle("more");b.textContent=c.classList.contains("more")?"Maz\u0101k filtru":"Vair\u0101k filtru";};})();

// ---- auto-refresh: check for fresh data, reload when the user is idle ----
let lastActive=Date.now(), updateReady=false;
["mousemove","keydown","scroll","click","touchstart"].forEach(e=>
  addEventListener(e,()=>{lastActive=Date.now();},{passive:true}));
function doReload(){location.href=location.pathname+"?t="+Date.now();}
function showBanner(){
  if(document.getElementById("upbanner"))return;
  const b=document.createElement("button");
  b.id="upbanner"; b.textContent="\u21bb Pieejami jauni dati \u2014 atjaunot";
  b.onclick=doReload;
  Object.assign(b.style,{position:"fixed",bottom:"18px",left:"50%",
    transform:"translateX(-50%)",zIndex:"9999",background:"#111",color:"#fff",
    border:"none",borderRadius:"999px",padding:"10px 20px",fontSize:"14px",
    cursor:"pointer",boxShadow:"0 2px 10px rgba(0,0,0,.3)"});
  document.body.appendChild(b);
}
async function checkUpdate(){
  try{
    const r=await fetch("version.txt?t="+Date.now(),{cache:"no-store"});
    if(!r.ok)return;
    const v=(await r.text()).trim();
    if(v && v!==BUILD_TS){updateReady=true; showBanner();}
  }catch(e){}
}
setInterval(checkUpdate, 5*60*1000);                    // check every 5 min
setInterval(()=>{ if(updateReady && Date.now()-lastActive>30000) doReload(); }, 15000);
render();
</script>
</body></html>""".replace("__TS__", esc(ts)).replace("__DATA__", data_json).replace("__TABS__", tabs_json).replace("__BANNERS__", banners_html)


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
def listing_sig(ad: dict) -> str:
    """Signature of a listing row. If it changes for the same URL, ss.lv has
    recycled that URL to a different (or edited) ad and we must re-read it."""
    return "|".join(str(ad.get(k) or "")
                    for k in ("title", "year", "mileage", "price"))


def seen_ts(entry) -> str | None:
    return entry.get("ts") if isinstance(entry, dict) else entry


def seen_sig(entry):
    return entry.get("sig") if isinstance(entry, dict) else None


def prune_seen(seen: dict) -> dict:
    cutoff = today() - relativedelta(days=SEEN_KEEP_DAYS)
    out = {}
    for u, e in seen.items():
        ts = seen_ts(e)
        if ts and date.fromisoformat(ts[:10]) >= cutoff:
            out[u] = e
    return out


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


CARS_ROOT = "https://www.ss.lv/lv/transport/cars/"

# Fallback make list if discovery fails (kept short but broad)
FALLBACK_MAKES = [
    "audi", "bmw", "chevrolet", "chrysler", "citroen", "dacia", "dodge",
    "fiat", "ford", "honda", "hyundai", "jaguar", "jeep", "kia", "land-rover",
    "lexus", "mazda", "mercedes", "mini", "mitsubishi", "nissan", "opel",
    "peugeot", "porsche", "renault", "seat", "skoda", "subaru", "suzuki",
    "tesla", "toyota", "volkswagen", "volvo", "others",
]


def discover_makes(delay: float) -> list[str]:
    """Read every make sub-page link off the /transport/cars/ hub, so an
    'all cars' source truly covers all makes and stays current automatically."""
    html_text = fetch(CARS_ROOT, delay)
    if not html_text:
        log("Make discovery failed; using fallback list.")
        return [CARS_ROOT + m + "/" for m in FALLBACK_MAKES]
    soup = BeautifulSoup(html_text, BS_PARSER)
    slugs: list[str] = []
    for a in soup.select("a[href]"):
        m = re.match(r"^/lv/transport/cars/([a-z0-9\-]+)/$", a.get("href", ""))
        if m:
            slug = m.group(1)
            if slug != "electric-cars" and slug not in slugs:
                slugs.append(slug)
    if not slugs:
        log("No makes parsed from hub; using fallback list.")
        slugs = FALLBACK_MAKES
    log(f"Discovered {len(slugs)} car makes from the cars hub.")
    return [CARS_ROOT + s + "/" for s in slugs]


def expand_sources(searches: list[dict], delay: float) -> None:
    """Replace an 'all cars' root source with every discovered make URL."""
    roots = {CARS_ROOT, CARS_ROOT.rstrip("/")}
    needs = any(s in roots for srch in searches for s in srch.get("sources", []))
    makes = discover_makes(delay) if needs else []
    for srch in searches:
        expanded: list[str] = []
        for s in srch.get("sources", []):
            if s in roots:
                expanded.extend(makes)
            else:
                expanded.append(s)
        # de-dupe while preserving order
        seen_s: set[str] = set()
        srch["sources"] = [x for x in expanded if not (x in seen_s or seen_s.add(x))]


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
    # Hourly "quick" runs scan only the first page(s) to catch fresh listings
    # fast; the once-a-day "deep" run scans everything. Set via SCAN_MODE env.
    if os.environ.get("SCAN_MODE", "").lower() == "quick":
        max_pages = int(search.get("quick_pages", scan.get("quick_pages", 1)))
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

    # RSS fast-lane: one tiny request that discovers the newest ads and stamps
    # them with a precise <pubDate> posting time
    rss_ts: dict[str, str] = {}
    rss_url = search.get("rss")
    if rss_url:
        rss_ads = parse_rss(fetch(rss_url, delay) or "")
        log(f"[{label}] RSS: {len(rss_ads)} items")
        for a in rss_ads:
            if a.get("posted_ts"):
                rss_ts[a["url"]] = a["posted_ts"]
            current.setdefault(a["url"], a)

    def is_new_or_changed(u: str) -> bool:
        e = seen.get(u)
        if e is None:
            return True
        old = seen_sig(e)
        if old is None:                 # legacy entry (no signature) -> adopt silently
            return False
        return old != listing_sig(current[u])

    new_urls = [u for u in current if is_new_or_changed(u)]
    # URLs already seen but with a changed signature = ss.lv recycled/edited them;
    # their previously-stored data is now stale and must be dropped.
    changed_urls = [u for u in new_urls
                    if seen.get(u) is not None and seen_sig(seen[u]) is not None]
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
        make, model = split_make_model(ad["url"], fields)
        is_phev = is_phev_text(ad.get("title"), desc)
        if require_phev and not is_phev:
            continue

        fuel_cat = ("plug-in" if is_phev
                    else fuel_category(fields.get("motors") or ad.get("engine")))
        if not fuel_cat and "/electric-cars/" in ad["url"]:
            fuel_cat = "elektro"
        ekii = has_ekii(ad.get("title"), desc)
        batt = battery_kwh(ad.get("title"), desc)
        heatpump = has_heat_pump(ad.get("title"), desc)

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

        fp = car_key({"make": make, "model": model, "year": ad.get("year"),
                      "engine": ad.get("engine"), "fuel_cat": fuel_cat,
                      "mileage_km": mileage_km})
        price = ad.get("price")
        is_repeat, seen_count, first_seen_any, ta_renewed = False, 1, now_iso, False
        prev_price, price_delta = None, None
        if fp:
            prior = fps.get(fp)
            if prior:
                urls = prior.get("urls", [])
                is_repeat = ad["url"] not in urls
                seen_count = len(set(urls) | {ad["url"]})
                first_seen_any = prior.get("first_seen", now_iso)
                if is_repeat and now_valid and not prior.get("had_valid_ta"):
                    ta_renewed = True
                lp = prior.get("last_price")
                if lp and price and price != lp:          # same car, new price
                    prev_price, price_delta = lp, price - lp
            entry = fps.setdefault(fp, {"first_seen": now_iso, "urls": [],
                                        "had_valid_ta": False, "last_ta": None,
                                        "last_price": None})
            if ad["url"] not in entry["urls"]:
                entry["urls"].append(ad["url"])
            entry["last_seen"] = now_iso
            if now_valid:
                entry["had_valid_ta"] = True
                entry["last_ta"] = until
            if price:
                entry["last_price"] = price

        ad.update({
            "make": make, "model": model,
            "inspection_until": until, "inspection_raw": raw,
            "insp_status": inspection_status(until, raw),
            "months_left": months_left, "days_left": days_left,
            "place": detail.get("place"), "posted": detail.get("posted")
                or (rss_ts.get(ad["url"], "").replace("T", " ") or None),
            "posted_iso": posted_to_iso(detail.get("posted"))
                or (rss_ts.get(ad["url"], "")[:10] or None),
            "posted_ts": rss_ts.get(ad["url"]) or posted_to_ts(detail.get("posted")),
            "mileage_k": parse_mileage_k(ad.get("mileage")),
            "mileage_km": mileage_km, "reg": reg_raw, "condition": condition,
            "fuel_cat": fuel_cat, "ekii": ekii,
            "ekii_eligible": ekii_eligible, "ekii_reason": ekii_reason,
            "battery_kwh": batt, "heat_pump": heatpump,
            "labels": [label],
            "is_repeat": is_repeat, "seen_count": seen_count,
            "first_seen_any": first_seen_any, "ta_renewed": ta_renewed,
            "prev_price": prev_price, "price_delta": price_delta,
            "car_fp": fp,
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

    # keep every matched car's fingerprint fresh and mark all as seen
    matched_by_url = {m["url"]: m for m in matches}
    for u, ad in current.items():
        m = matched_by_url.get(u)
        fp = car_key(m) if m else None
        if fp:
            entry = fps.setdefault(fp, {"first_seen": now_iso, "urls": [],
                                        "had_valid_ta": False, "last_ta": None,
                                        "last_price": None})
            if u not in entry["urls"]:
                entry["urls"].append(u)
            entry["last_seen"] = now_iso
        seen[u] = {"ts": now_iso, "sig": listing_sig(ad)}

    log(f"[{label}] matches: {len(matches)}")
    return matches, changed_urls


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------
def main() -> int:
    cfg = load_yaml(CONFIG_PATH)
    scan = cfg.get("scan") or {}
    report_cfg = cfg.get("report") or {}
    top_n = int(report_cfg.get("top_n", 40))
    searches = normalize_searches(cfg)
    expand_sources(searches, float((cfg.get("scan") or {}).get("request_delay_seconds", 1.5)))

    seen = load_json(SEEN_PATH, {})
    first_run = len(seen) == 0
    stored_matches = load_json(MATCHES_PATH, [])
    known_match_urls = {m["url"] for m in stored_matches}
    fps = load_json(FINGERPRINTS_PATH, {})
    now_iso = datetime.now(timezone.utc).isoformat()

    # run every configured search (each with its own price band / fuel / rules)
    all_matches: list[dict] = []
    changed_all: set[str] = set()
    for s in searches:
        ms, changed = run_search(s, scan, seen, fps, now_iso)
        all_matches.extend(ms)
        changed_all.update(changed)

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
    keep_fields = ("url", "title", "thumb", "make", "model", "price", "year",
                   "engine", "mileage",
                   "mileage_k", "inspection_until", "inspection_raw",
                   "insp_status", "months_left", "days_left", "place",
                   "first_seen", "posted", "posted_iso", "posted_ts", "archive",
                   "fuel_cat", "ekii", "ekii_eligible", "ekii_reason",
                   "mileage_km", "reg", "condition", "battery_kwh", "heat_pump",
                   "labels",
                   "is_repeat", "seen_count", "first_seen_any", "ta_renewed",
                   "prev_price", "price_delta", "car_fp")
    # remove stale rows for any URL ss.lv recycled/edited (even if the new ad
    # no longer qualifies, e.g. expired TA), then add/replace fresh matches
    if changed_all:
        stored_matches = [sm for sm in stored_matches if sm["url"] not in changed_all]
    for m in new_matches:
        stored_matches = [sm for sm in stored_matches if sm["url"] != m["url"]]
        stored_matches.append({k: m.get(k) for k in keep_fields})
    stored_matches = prune_matches(stored_matches)
    # collapse re-listings of the same physical car: keep only the most recent
    # listing (newest first_seen) so the dashboard shows one row per car, with
    # the price-change badge on the current listing
    seen_fp: set[str] = set()
    deduped: list[dict] = []
    for m in sorted(stored_matches, key=lambda x: x.get("first_seen", ""), reverse=True):
        k = m.get("car_fp")
        if k:
            if k in seen_fp:
                continue
            seen_fp.add(k)
        deduped.append(m)
    stored_matches = deduped
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
    REPORT_PATH.write_text(render_page_html(page_rows, ts,
                                            [s.get("label", "") for s in searches],
                                            cfg.get("banners")),
                           encoding="utf-8")
    log(f"Wrote {REPORT_PATH} ({len(page_rows)} rows)")
    (REPORT_PATH.parent / "version.txt").write_text(ts, encoding="utf-8")

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
