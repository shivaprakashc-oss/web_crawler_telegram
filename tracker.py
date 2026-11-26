#!/usr/bin/env python3
"""
Daily price tracker for amazon.in and flipkart.com.

- Reads product URLs from products.txt (one per line, '#' lines are comments).
- Fetches the current price of each product.
- Compares with the last recorded price in prices.json.
- Sends a Telegram alert ONLY when the price is lower than the last recorded one.
- Saves every price (with history) back to prices.json next to this script.

Environment variables:
    TELEGRAM_BOT_TOKEN   Bot token from @BotFather
    TELEGRAM_CHAT_ID     Your chat id

Usage:
    python tracker.py              # normal run
    python tracker.py --dry-run    # prints alerts instead of sending to Telegram

Exit codes:
    0  all products processed
    1  one or more products failed (fetch/parse/alert) -> GitHub emails you
    2  configuration error (missing Telegram secrets, corrupt prices.json)
"""
from __future__ import annotations

import argparse
import html
import json
import logging
import os
import random
import re
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Optional
from urllib.parse import parse_qs, urlparse
try:
    from curl_cffi import requests as cffi_requests
except ImportError:          # falls back to plain requests
    cffi_requests = None
import requests
from bs4 import BeautifulSoup

# --------------------------------------------------------------------------- #
# Config
# --------------------------------------------------------------------------- #
BASE_DIR = Path(__file__).resolve().parent
PRODUCTS_FILE = BASE_DIR / "products.txt"
PRICES_FILE = BASE_DIR / "prices.json"

MAX_HISTORY = 365            # entries kept per product
REQUEST_TIMEOUT = 25         # seconds
MAX_ATTEMPTS = max(1, int(os.environ.get("MAX_ATTEMPTS", "15")))
FLIPKART_MAX_ATTEMPTS = 6 # per product
SHORT_WAIT = (3, 7)          # seconds between failed attempts (block is per-request, not rate-based)
COOLDOWN_EVERY = 4           # after every 4th failure, take a longer pause
COOLDOWN_WAIT = (25, 40)
WARMUP = True                # on retries, hit amazon.in homepage first to get cookies
TIME_BUDGET = 25 * 60
DELAY_BETWEEN_PRODUCTS = (6, 12)
IMPERSONATE = ["chrome124", "chrome120", "chrome119", "chrome116"]
BIG_DROP_WARN_PCT = 50       # add a "verify" note to alerts for drops this large
IST = timezone(timedelta(hours=5, minutes=30))

AMAZON_DOMAINS = ("amazon.in", "amzn.in")
FLIPKART_DOMAINS = ("flipkart.com", "fkrt.it")

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/124.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/123.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:125.0) Gecko/20100101 Firefox/125.0",
]

# Selectors are the part most likely to need maintenance when the sites change
# their markup. Order matters: most specific first. Deliberately NO page-wide
# generic fallback, so we never grab the price of a sponsored/related product.
AMAZON_PRICE_SELECTORS = [
    "#corePriceDisplay_desktop_feature_div span.priceToPay span.a-offscreen",
    "#corePriceDisplay_desktop_feature_div span.a-price:not(.a-text-price) span.a-offscreen",
    "#corePrice_feature_div span.a-price:not(.a-text-price) span.a-offscreen",
    "#apex_desktop span.priceToPay span.a-offscreen",
    "#newBuyBoxPrice",
    "#price_inside_buybox",
    "#priceblock_dealprice",
    "#priceblock_ourprice",
]
AMAZON_TITLE_SELECTORS = ["#productTitle"]

FLIPKART_PRICE_SELECTORS = [
    "div.Nx9bqj.CxhGGd",
    "div._30jeq3._16Jk6d",
]
FLIPKART_TITLE_SELECTORS = ["span.VU-ZEz", "span.B_NuCI", "h1"]

BLOCK_MARKERS = (
    "api-services-support@amazon.com",
    "enter the characters you see below",
    "type the characters you see in this image",
    "/errors/validatecaptcha",
    "not a robot",
    "access denied",
)

log = logging.getLogger("price-tracker")


class FetchError(Exception):
    """Raised when a page cannot be fetched or a price cannot be extracted."""


@dataclass
class Quote:
    site: str                 # "amazon" | "flipkart"
    title: str
    price: Optional[float]    # None if the product is unavailable
    unavailable: bool = False


# --------------------------------------------------------------------------- #
# URL helpers
# --------------------------------------------------------------------------- #
def _domain_match(host: str, domains: tuple[str, ...]) -> bool:
    return any(host == d or host.endswith("." + d) for d in domains)


def site_of(url: str) -> Optional[str]:
    host = (urlparse(url).hostname or "").lower()
    if _domain_match(host, AMAZON_DOMAINS):
        return "amazon"
    if _domain_match(host, FLIPKART_DOMAINS):
        return "flipkart"
    return None


def normalize_url(raw: str) -> str:
    """Strip tracking junk so the same product always maps to the same key."""
    url = raw.strip()
    parsed = urlparse(url)
    if parsed.scheme not in ("http", "https") or not parsed.hostname:
        raise ValueError(f"not a valid http(s) URL: {raw!r}")
    site = site_of(url)
    if site is None:
        raise ValueError(f"unsupported site (only amazon.in / flipkart.com): {raw!r}")

    if site == "amazon":
        m = re.search(r"/(?:dp|gp/product|gp/aw/d)/([A-Z0-9]{10})", parsed.path, re.I)
        if m and _domain_match(parsed.hostname.lower(), ("amazon.in",)):
            return f"https://www.amazon.in/dp/{m.group(1).upper()}"
        return url  # short link (amzn.in/...) – resolved at fetch time

    # flipkart
    if _domain_match(parsed.hostname.lower(), ("flipkart.com",)):
        pid = parse_qs(parsed.query).get("pid", [None])[0]
        base = f"https://www.flipkart.com{parsed.path}"
        return f"{base}?pid={pid}" if pid else base
    return url


def load_products() -> list[str]:
    if not PRODUCTS_FILE.exists():
        raise FileNotFoundError(f"{PRODUCTS_FILE.name} not found")
    urls: list[str] = []
    for line in PRODUCTS_FILE.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            urls.append(line)
    return urls


# --------------------------------------------------------------------------- #
# Price parsing
# --------------------------------------------------------------------------- #
def parse_price(value) -> Optional[float]:
    """'₹1,29,999.00' -> 129999 ; 'Rs. 499' -> 499 ; 1299.5 -> 1299.5"""
    if value is None:
        return None
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        num = float(value)
    else:
        m = re.search(r"\d[\d,]*(?:\.\d+)?", str(value))
        if not m:
            return None
        try:
            num = float(m.group(0).replace(",", ""))
        except ValueError:
            return None
    if num <= 0:
        return None
    return int(num) if num.is_integer() else round(num, 2)


def fmt_inr(n: float) -> str:
    """Indian digit grouping: 129999 -> ₹1,29,999"""
    whole = int(n)
    paise = int(round((n - whole) * 100))
    digits = str(whole)
    if len(digits) > 3:
        head, tail = digits[:-3], digits[-3:]
        head = re.sub(r"(\d)(?=(\d\d)+$)", r"\1,", head)
        digits = f"{head},{tail}"
    return f"₹{digits}" + (f".{paise:02d}" if paise else "")


def _clean(text: Optional[str]) -> str:
    return re.sub(r"\s+", " ", text or "").strip()


def _first_text(soup: BeautifulSoup, selectors: list[str]) -> str:
    for sel in selectors:
        el = soup.select_one(sel)
        if el:
            t = _clean(el.get_text())
            if t:
                return t
    return ""


def _fallback_title(soup: BeautifulSoup) -> str:
    og = soup.find("meta", property="og:title")
    if og and og.get("content"):
        return _clean(og["content"])
    if soup.title and soup.title.string:
        return _clean(soup.title.string)
    return "Unknown product"


def _price_from_selectors(soup: BeautifulSoup, selectors: list[str]) -> Optional[float]:
    for sel in selectors:
        for el in soup.select(sel):
            price = parse_price(el.get_text(strip=True))
            if price is not None:
                return price
    return None


def _find_offer_price(node) -> Optional[float]:
    """Walk JSON-LD for offers.price / lowPrice."""
    if isinstance(node, dict):
        if "offers" in node:
            p = _find_offer_price(node["offers"])
            if p is not None:
                return p
        for key in ("price", "lowPrice"):
            if key in node:
                p = parse_price(node[key])
                if p is not None:
                    return p
        for v in node.values():
            if isinstance(v, (dict, list)):
                p = _find_offer_price(v)
                if p is not None:
                    return p
    elif isinstance(node, list):
        for item in node:
            p = _find_offer_price(item)
            if p is not None:
                return p
    return None


def _price_from_json_ld(soup: BeautifulSoup) -> Optional[float]:
    for script in soup.find_all("script", type="application/ld+json"):
        raw = script.string or script.get_text()
        if not raw or not raw.strip():
            continue
        try:
            data = json.loads(raw)
        except json.JSONDecodeError:
            continue
        price = _find_offer_price(data)
        if price is not None:
            return price
    return None


def parse_amazon(soup: BeautifulSoup) -> tuple[str, Optional[float], bool]:
    title = _first_text(soup, AMAZON_TITLE_SELECTORS) or _fallback_title(soup)
    price = _price_from_selectors(soup, AMAZON_PRICE_SELECTORS)
    unavailable = False
    if price is None:
        avail = soup.select_one("#availability, #outOfStock")
        unavailable = bool(avail and "unavailable" in avail.get_text().lower())
    return title, price, unavailable


def parse_flipkart(soup: BeautifulSoup) -> tuple[str, Optional[float], bool]:
    title = _first_text(soup, FLIPKART_TITLE_SELECTORS) or _fallback_title(soup)
    price = _price_from_json_ld(soup)
    if price is None:
        price = _price_from_selectors(soup, FLIPKART_PRICE_SELECTORS)
    unavailable = False
    if price is None:
        text = soup.get_text(" ").lower()
        unavailable = "sold out" in text or "currently unavailable" in text
    return title, price, unavailable


# --------------------------------------------------------------------------- #
# Fetching
# --------------------------------------------------------------------------- #
def _headers() -> dict:
    return {
        "User-Agent": random.choice(USER_AGENTS),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,"
                  "image/avif,image/webp,*/*;q=0.8",
        "Accept-Language": "en-IN,en;q=0.9",
        "Upgrade-Insecure-Requests": "1",
        "Cache-Control": "no-cache",
        "Referer": "https://www.google.com/",
        "Sec-Fetch-Dest": "document",
        "Sec-Fetch-Mode": "navigate",
        "Sec-Fetch-Site": "cross-site",
        "Sec-Fetch-User": "?1",
    }


def _is_blocked(text: str) -> bool:
    # Real product pages are large; bot-check pages are small.
    if len(text) > 60_000:
        return False
    low = text.lower()
    return any(marker in low for marker in BLOCK_MARKERS)


def _new_session(site: str, attempt: int):
    """Amazon: always Chrome-impersonated curl_cffi (this is what fixed Amazon).
    Flipkart: alternate plain requests (worked before) and curl_cffi."""
    use_cffi = cffi_requests is not None
    if site == "flipkart" and use_cffi:
        use_cffi = (attempt % 2 == 0)       # odd attempts: requests, even: curl_cffi
    if use_cffi:
        return (cffi_requests.Session(impersonate=random.choice(IMPERSONATE)),
                {"Accept-Language": "en-IN,en;q=0.9"}, "curl_cffi")
    return requests.Session(), _headers(), "requests"


def _scraper_api_fetch(url: str):
    """Optional last resort. Only used if SCRAPER_API_KEY is set."""
    key = os.environ.get("SCRAPER_API_KEY", "").strip()
    if not key:
        return None
    try:
        r = requests.get("https://api.scraperapi.com/",
                         params={"api_key": key, "url": url, "country_code": "in"},
                         timeout=70)
    except requests.RequestException:
        return None
    if r.status_code == 200 and not _is_blocked(r.text):
        log.info("  succeeded via scraper API fallback")
        return r
    return None


def fetch(url: str):
    last_err = "unknown error"
    site = site_of(url)
    is_amazon = site == "amazon"
    max_attempts = MAX_ATTEMPTS if is_amazon else FLIPKART_MAX_ATTEMPTS
    for attempt in range(1, max_attempts + 1):
        resp = None
        client = "?"
        try:
            session, headers, client = _new_session(site or "", attempt)
            with session:
                if is_amazon and WARMUP and attempt > 1:
                    try:
                        session.get("https://www.amazon.in/", headers=headers, timeout=15)
                    except Exception:
                        pass
                    time.sleep(random.uniform(1, 2.5))
                resp = session.get(url, headers=headers, timeout=REQUEST_TIMEOUT,
                                   allow_redirects=True)
        except Exception as exc:
            last_err = f"network error: {exc.__class__.__name__} [{client}]"
        else:
            if resp.status_code in (404, 410):
                raise FetchError(f"HTTP {resp.status_code} (product page gone?)")
            if resp.status_code == 200 and not _is_blocked(resp.text):
                log.info("  OK via %s on attempt %d/%d", client, attempt, max_attempts)
                return resp
            last_err = f"HTTP {resp.status_code} [{client}]" + (
                " (bot check / captcha page)" if resp.status_code == 200 else "")
        if attempt < max_attempts:
            wait = random.uniform(*(COOLDOWN_WAIT if attempt % COOLDOWN_EVERY == 0 else SHORT_WAIT))
            log.info("  attempt %d/%d failed (%s); retrying in %.0fs",
                     attempt, max_attempts, last_err, wait)
            time.sleep(wait)
    fallback = _scraper_api_fetch(url)
    if fallback is not None:
        return fallback
    raise FetchError(f"{last_err} after {max_attempts} attempts")


def check_product(url: str) -> Quote:
    resp = fetch(url)
    site = site_of(str(resp.url)) or site_of(url)   # scraper API responses have a different URL
    parser = {"amazon": parse_amazon, "flipkart": parse_flipkart}.get(site or "")
    if parser is None:
        raise FetchError(f"redirected to unsupported page: {resp.url}")
    soup = BeautifulSoup(resp.text, "lxml")
    title, price, unavailable = parser(soup)
    if price is None and not unavailable:
        raise FetchError("price not found (layout changed, or page served without price)")
    return Quote(site=site, title=title[:150], price=price, unavailable=unavailable)


# --------------------------------------------------------------------------- #
# Storage
# --------------------------------------------------------------------------- #
def load_prices() -> dict:
    if not PRICES_FILE.exists():
        return {}
    raw = PRICES_FILE.read_text(encoding="utf-8").strip()
    if not raw:
        return {}
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as exc:
        # Never overwrite a damaged history file silently.
        raise SystemExit(f"{PRICES_FILE.name} is not valid JSON ({exc}). Fix or delete it.")
    if not isinstance(data, dict):
        raise SystemExit(f"{PRICES_FILE.name} must contain a JSON object.")
    return data


def save_prices(data: dict) -> None:
    tmp = PRICES_FILE.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(tmp, PRICES_FILE)  # atomic: no half-written file on crash


# --------------------------------------------------------------------------- #
# Telegram
# --------------------------------------------------------------------------- #
def send_telegram(token: str, chat_id: str, text: str) -> None:
    try:
        resp = requests.post(
            f"https://api.telegram.org/bot{token}/sendMessage",
            json={
                "chat_id": chat_id,
                "text": text,
                "parse_mode": "HTML",
                "disable_web_page_preview": False,
            },
            timeout=20,
        )
    except requests.RequestException as exc:
        # exception text can contain the URL (with the token) -> scrub it
        raise RuntimeError(f"Telegram request failed: {str(exc).replace(token, '***')}") from None
    if not resp.ok:
        raise RuntimeError(f"Telegram API error {resp.status_code}: {resp.text[:200]}")


def build_alert(url: str, quote: Quote, prev: float, new: float, lowest_before: Optional[float]) -> str:
    diff = prev - new
    pct = diff / prev * 100
    site_name = "Amazon.in" if quote.site == "amazon" else "Flipkart"
    lines = [
        "📉 <b>Price drop!</b>",
        f"<b>{html.escape(quote.title)}</b>",
        f"🛒 {site_name}",
        f"Was {fmt_inr(prev)} → <b>Now {fmt_inr(new)}</b>",
        f"You save {fmt_inr(diff)} ({pct:.1f}%)",
    ]
    if lowest_before is None or new <= lowest_before:
        lines.append("🏆 Lowest price recorded so far")
    else:
        lines.append(f"Lowest recorded: {fmt_inr(lowest_before)}")
    if pct >= BIG_DROP_WARN_PCT:
        lines.append("⚠️ Unusually large drop – verify on the site before buying.")
    lines.append(f'<a href="{html.escape(url, quote=True)}">Open product</a>')
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# Main
# --------------------------------------------------------------------------- #
def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument("--dry-run", action="store_true", help="print alerts instead of sending to Telegram")
    args = parser.parse_args(argv)

    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")

    token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
    chat_id = os.environ.get("TELEGRAM_CHAT_ID", "").strip()
    if not args.dry_run and not (token and chat_id):
        log.error("TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID must be set (or use --dry-run).")
        return 2

    try:
        raw_urls = load_products()
    except FileNotFoundError as exc:
        log.error("%s", exc)
        return 2
    if not raw_urls:
        log.warning("products.txt has no URLs. Nothing to do.")
        return 0

    data = load_prices()
    failures = 0
    alert_failures = 0
    started = time.monotonic()
    seen: set[str] = set()
    now = datetime.now(IST)
    today = now.strftime("%Y-%m-%d")

    for i, raw in enumerate(raw_urls):
        try:
            key = normalize_url(raw)
        except RuntimeError as exc:
                # Do NOT store the new price: next run will detect the drop again.
                log.error("  alert failed, keeping old price so it retries tomorrow: %s", exc)
                alert_failures += 1
                continue
        if key in seen:
            continue
        seen.add(key)

        if time.monotonic() - started > TIME_BUDGET:
            left = len(raw_urls) - i
            log.error("Time budget exceeded; %d product(s) not checked this run.", left)
            failures += left
            break

        if len(seen) > 1:
            time.sleep(random.uniform(*DELAY_BETWEEN_PRODUCTS))

        log.info("[%d/%d] %s", i + 1, len(raw_urls), key)
        try:
            quote = check_product(key)
        except FetchError as exc:
            log.warning("  could not check this product today: %s", exc)
            failures += 1
            continue
        except Exception:  # one bad product must never kill the whole run
            log.exception("  UNEXPECTED ERROR")
            failures += 1
            continue

        if quote.unavailable or quote.price is None:
            log.warning("  currently unavailable – nothing recorded")
            continue

        new = quote.price
        entry = data.get(key) or {}
        prev = entry.get("last_price")
        lowest_before = entry.get("lowest_price")
        log.info("  %s | now %s | previous %s", quote.title[:60], fmt_inr(new),
                 fmt_inr(prev) if prev is not None else "none (first run)")

        if prev is not None and new < prev:
            message = build_alert(key, quote, prev, new, lowest_before)
            try:
                if args.dry_run:
                    print("\n--- DRY RUN ALERT ---\n" + message + "\n---------------------\n")
                else:
                    send_telegram(token, chat_id, message)
                log.info("  price drop alert sent")
            except RuntimeError as exc:
                # Do NOT store the new price: next run will detect the drop again.
                log.error("  alert failed, keeping old price so it retries tomorrow: %s", exc)
                failures += 1
                continue

        history = entry.get("history", [])
        if history and history[-1].get("date") == today:
            history[-1]["price"] = new          # re-run on the same day: overwrite
        else:
            history.append({"date": today, "price": new})

        data[key] = {
            "site": quote.site,
            "title": quote.title,
            "last_price": new,
            "lowest_price": new if lowest_before is None else min(lowest_before, new),
            "last_checked": now.isoformat(timespec="seconds"),
            "history": history[-MAX_HISTORY:],
        }
        save_prices(data)   # save per product so a crash never loses sent-alert state

    save_prices(data)
    log.info("Done. %d product(s) checked, %d could not be fetched (ignored), %d alert failure(s).",
             len(seen), failures, alert_failures)
    return 1 if alert_failures else 0


if __name__ == "__main__":
    sys.exit(main())
