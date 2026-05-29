#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Polední menu dashboard v5.7
- jeden hlavní skript pro všechny pracovní dny, bez pěti denních wrapperů
- HTML scraping zůstává hlavní zdroj, protože menu bývá na statických stránkách
- volitelný RSS/Atom fallback: použije se až když HTML parser nenajde položky
- cache posledního úspěšně načteného menu pro případ výpadku webu nebo parseru
- debug výpisy a textový report pro ladění jednotlivých restaurací

Instalace:
  python -m pip install requests beautifulsoup4 urllib3

Spuštění aktuálního pracovního dne:
  python lunch_dashboard_engine_v4.py

Spuštění konkrétního dne:
  python lunch_dashboard_engine_v4.py --day pondeli
  python lunch_dashboard_engine_v4.py --day utery
  python lunch_dashboard_engine_v4.py --day streda
  python lunch_dashboard_engine_v4.py --day ctvrtek
  python lunch_dashboard_engine_v4.py --day patek

Ladění:
  python lunch_dashboard_engine_v4.py --day streda --dump --report debug_report.md

Vypnutí fallbacků:
  python lunch_dashboard_engine_v4.py --no-rss --no-cache
"""

from __future__ import annotations

import argparse
import base64
import html
import json
import re
import socket
import sys
import webbrowser
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Callable, Iterable
from urllib.parse import urljoin, urlparse
import xml.etree.ElementTree as ET

import requests
import urllib3
from bs4 import BeautifulSoup

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36 lunch-dashboard/5.7"
)

# Některé CI/cloudové prostředí může zkusit pro problematické weby IPv6,
# i když cesta ven vede jen přes IPv4. U DnešníOběd.cz to může skončit
# chybou Network is unreachable. Proto pro tento host preferujeme IPv4.
_ORIGINAL_GETADDRINFO = socket.getaddrinfo
IPV4_PREFERRED_HOSTS = {"www.dnesniobed.cz", "dnesniobed.cz"}

def _getaddrinfo_ipv4_preferred(host, port, family=0, type=0, proto=0, flags=0):
    results = _ORIGINAL_GETADDRINFO(host, port, family, type, proto, flags)
    if str(host).lower() in IPV4_PREFERRED_HOSTS:
        ipv4 = [r for r in results if r[0] == socket.AF_INET]
        return ipv4 or results
    return results

socket.getaddrinfo = _getaddrinfo_ipv4_preferred

DAYS = ["pondělí", "úterý", "středa", "čtvrtek", "pátek"]
DAY_ALIASES = {
    "pondeli": "pondělí", "pondělí": "pondělí", "po": "pondělí", "monday": "pondělí",
    "utery": "úterý", "úterý": "úterý", "ut": "úterý", "úterý": "úterý", "tuesday": "úterý",
    "streda": "středa", "středa": "středa", "st": "středa", "wednesday": "středa",
    "ctvrtek": "čtvrtek", "čtvrtek": "čtvrtek", "ct": "čtvrtek", "čt": "čtvrtek", "thursday": "čtvrtek",
    "patek": "pátek", "pátek": "pátek", "pa": "pátek", "friday": "pátek",
}
DAY_TITLE = {
    "pondělí": "Pondělí", "úterý": "Úterý", "středa": "Středa", "čtvrtek": "Čtvrtek", "pátek": "Pátek"
}

JUNK_EXACT = {
    "úvod", "o nás", "menu", "kontakt", "galerie", "home", "print view", "sitemap",
    "jídelní lístek", "nápojový lístek", "vinný lístek", "rezervace", "shop", "english",
    "all works", "přejít nahoru", "odeslat", "x", "cs", "en", "de", "populární", "0",
    "zobrazit", "language", "česky", "euro přijímáme", "platba kartou - qerko",
}
JUNK_CONTAINS = (
    "otevírací doba", "copyright", "privacy policy", "gdpr", "informační povinnost",
    "zpracování osobních údajů", "přeskočit na obsah", "powered by", "facebook", "instagram",
    "zavolám vám zpět", "povinný údaj", "rezervace stolu", "kudy k nám", "telefon", "e-mail",
    "další dny", "celé dnešní menu", "rozvoz", "takeaway", "zavolejte nám", "rezervujte stůl",
    "navštivte nás", "kurz 1€", "qerko", "language", "cookies", "alergen:", "alergeny",
)
STOP_CONTAINS = (
    "aktuality", "kudy k nám", "rezervace", "otevírací doba", "kontakt", "nápojový", "vinný",
    "galerie", "all works", "sitemap", "informační povinnost", "na zobnutí", "vlajkové jídlo",
    "euro přijímáme", "platba kartou", "o nás", "stálé menu", "varný proces", "tradice", "péče",
)

PRICE_RE = re.compile(r"(?P<price>(?:od\s*)?\d{2,4}\s*(?:,-|,|kč|Kč|CZK))")
PRICE_ONLY_RE = re.compile(r"^(?:od\s*)?\d{2,4}\s*(?:,-|,|kč|Kč|CZK)$")
WEIGHT_RE = re.compile(r"^\d+(?:[,.]\d+)?\s*(?:g|kg|ml|l|dcl|ks)\b", re.I)
DAY_HEADING_RE = re.compile(
    r"^(pondělí|pondeli|úterý|utery|středa|streda|čtvrtek|ctvrtek|pátek|patek)\b(?:\s+\d{1,2}[./]\s*\d{1,2}[./]?)?",
    re.I,
)
SECTION_WORDS = {
    "polévka", "polévky", "menu i.", "menu ii.", "menu iii.", "dnes doporučujeme",
    "polední nabídka", "hlavní chod", "hlavní chody", "denní menu", "polední menu", "dezert", "dezerty",
}
EMPTY_MENU_PHRASES = (
    "denní menu ještě bublá", "menu ještě bublá", "těšte se na něco lahodného",
    "polední menu není dostupné", "menu nenalezeno", "momentálně není dostupné",
)


@dataclass
class Restaurant:
    name: str
    sources: list[str]
    parser: str
    max_items: int = 10
    empty_is_ok: bool = False


@dataclass
class MenuItem:
    title: str
    price: str = ""
    note: str = ""
    section: str = ""


RESTAURANTS = [
    Restaurant(
        "Na Paloučku",
        [
            "https://www.restpaloucek.cz/jidelnilistek/poledni-nabidka-2/",
        ],
        "paloucek",
        12,
    ),
    Restaurant(
        "Palatino Pankrác",
        [
            "https://nominanza.com/index-pankrac.html",
        ],
        "palatino",
        9,
    ),
    Restaurant(
        "Restaurace Klika",
        [
            "https://restauraceklika.cz/",
            "https://restauraceklika.cz/cs/menu/poledni-menu/",
        ],
        "klika",
        9,
    ),
    Restaurant(
        "U Bansethů",
        [
            # Primární zdroj. V GitHub Actions někdy zlobí www/IPv6, proto jsou
            # hned pod ním připravené non-www a HTTP varianty stejné stránky.
            "https://www.dnesniobed.cz/restaurace-hospoda/nusle_u-bansethu-a-basta",
            "https://dnesniobed.cz/restaurace-hospoda/nusle_u-bansethu-a-basta",
            "http://www.dnesniobed.cz/restaurace-hospoda/nusle_u-bansethu-a-basta",
            "http://dnesniobed.cz/restaurace-hospoda/nusle_u-bansethu-a-basta",
            "https://www.firmy.cz/detail/684629-restaurace-u-bansethu-praha-nusle.html",
            "https://www.ubansethu.cz/poledni-nabidka/",
        ],
        "external_daily",
        12,
    ),
    Restaurant(
        "Kandelábr",
        [
            # Skutečný zdroj poledního menu je iframe/widget Zomato vložený na oficiálním webu.
            # URL je zakódovaná ve WordPress RSS obsahu stránky poledního menu.
            "https://www.zomato.com/widgets/daily_menu.php?entity_id=16506739",
            "https://www.restaurantkandelabr.cz/poledni-menu/",
            # Meníčka/Firmy necháváme jen jako fallbacky. V dumpu často vrací jen profil, ne menu.
            "https://www.menicka.cz/2277-restaurant-kandelabr.html#m",
            "https://www.menicka.cz/2277-restaurant-kandelabr.html",
            "https://www.menicka.cz/mobilni/2277-restaurant-kandelabr.html?t=info",
            "https://www.firmy.cz/detail/12777240-vysehradsky-restaurant-kandelabr-praha-nusle.html?c=293",
        ],
        "external_daily",
        10,
        empty_is_ok=True,
    ),
    Restaurant(
        "Na Květnici",
        [
            "https://www.nakvetnici.cz/cs/#daily_menu",
            "https://www.nakvetnici.cz/cs/",
        ],
        "kvetnice",
        12,
        empty_is_ok=True,
    ),
]


def normalize_day(value: str | None) -> str:
    if not value:
        today = datetime.now().weekday()
        return DAYS[today] if today < 5 else "pondělí"
    key = value.strip().lower()
    key = key.replace("ě", "e").replace("š", "s").replace("č", "c").replace("ř", "r").replace("ž", "z").replace("ý", "y").replace("á", "a").replace("í", "i").replace("é", "e").replace("ú", "u").replace("ů", "u")
    # nejdřív zkusíme bez diakritiky, potom originál
    if key in DAY_ALIASES:
        return DAY_ALIASES[key]
    original = value.strip().lower()
    if original in DAY_ALIASES:
        return DAY_ALIASES[original]
    raise ValueError(f"Neznámý den: {value}. Použij pondeli, utery, streda, ctvrtek nebo patek.")


def fetch_html(url: str, timeout: int = 25) -> str:
    headers = {
        "User-Agent": USER_AGENT,
        "Accept-Language": "cs-CZ,cs;q=0.9,en;q=0.6",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Connection": "close",
    }
    # Zomato widget je vložený v iframe na oficiálním webu Kandelábru.
    # Referer zvyšuje šanci, že widget nevrátí prázdnou/ochrannou stránku.
    if "zomato.com/widgets/daily_menu.php" in url:
        headers["Referer"] = "https://www.restaurantkandelabr.cz/poledni-menu/"

    last_exc: Exception | None = None
    for attempt in range(3):
        try:
            r = requests.get(
                url,
                headers=headers,
                timeout=timeout,
                verify=False,
            )
            r.raise_for_status()
            r.encoding = r.apparent_encoding or r.encoding
            return r.text
        except Exception as exc:  # noqa: BLE001
            last_exc = exc
            if attempt < 2:
                time.sleep(1.2 * (attempt + 1))
                continue
            raise
    raise last_exc or RuntimeError(f"Nepodařilo se stáhnout {url}")

def slugify(value: str) -> str:
    value = without_diacritics(value)
    value = re.sub(r"[^a-z0-9]+", "-", value).strip("-")
    return value or "restaurant"


def cache_key(cfg: Restaurant, target_day: str) -> str:
    return f"{slugify(cfg.name)}::{target_day}"


def load_cache(path: Path) -> dict:
    if not path.exists():
        return {"version": 1, "entries": {}}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(data, dict) and isinstance(data.get("entries"), dict):
            return data
    except Exception:
        pass
    return {"version": 1, "entries": {}}


def save_cache(path: Path, cache: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(cache, ensure_ascii=False, indent=2), encoding="utf-8")


def item_to_dict(item: MenuItem) -> dict:
    return {"title": item.title, "price": item.price, "note": item.note, "section": item.section}


def item_from_dict(data: dict) -> MenuItem:
    return MenuItem(
        title=str(data.get("title") or ""),
        price=str(data.get("price") or ""),
        note=str(data.get("note") or ""),
        section=str(data.get("section") or ""),
    )


def cache_set(cache: dict, cfg: Restaurant, target_day: str, url: str, items: list[MenuItem]) -> None:
    if not items:
        return
    cache.setdefault("entries", {})[cache_key(cfg, target_day)] = {
        "name": cfg.name,
        "day": target_day,
        "url": url,
        "updated_at": datetime.now().isoformat(timespec="seconds"),
        "items": [item_to_dict(x) for x in items],
    }


def cache_items_look_valid(cfg: Restaurant, items: list[MenuItem]) -> bool:
    """Ochrana proti staré špatné cache, hlavně u Kandelábru.

    Ve v49/v50 se do cache mohl uložit profilový řádek z Firmy.cz
    („Ječná 511/16...“) jako falešná položka za 16,-. Takový zápis
    už nechceme nikdy vracet.
    """
    if not items:
        return False
    if cfg.name.lower().startswith("kandel"):
        bad_words = ("ječná", "jecna", "štětkova", "stetkova", "praha", "nové město", "nove mesto")
        if all(any(w in item.title.lower() for w in bad_words) for item in items):
            return False
        if len(items) == 1 and items[0].price.strip() in {"16,-", "16"}:
            return False
    return True


def cache_get(cache: dict, cfg: Restaurant, target_day: str, max_age_hours: int) -> dict | None:
    entry = cache.get("entries", {}).get(cache_key(cfg, target_day))
    if not isinstance(entry, dict):
        return None
    try:
        updated_at = datetime.fromisoformat(str(entry.get("updated_at")))
    except Exception:
        return None
    age_hours = (datetime.now() - updated_at).total_seconds() / 3600
    if age_hours > max_age_hours:
        return None
    items = [item_from_dict(x) for x in entry.get("items", []) if isinstance(x, dict)]
    if not cache_items_look_valid(cfg, items):
        return None
    return {
        "name": cfg.name,
        "url": entry.get("url") or cfg.sources[0],
        "items": items,
        "error": None,
        "empty_ok": False,
        "cached": True,
        "cache_updated_at": entry.get("updated_at"),
        "source_type": "cache",
    }


def discover_rss_urls(page_html: str, base_url: str) -> list[str]:
    """Najde RSS/Atom odkazy deklarované v HTML a přidá několik běžných fallback URL."""
    soup = BeautifulSoup(page_html, "html.parser")
    urls: list[str] = []
    for link in soup.find_all("link"):
        rel = " ".join(link.get("rel") or []).lower()
        typ = str(link.get("type") or "").lower()
        href = link.get("href")
        if not href:
            continue
        if "alternate" in rel and any(x in typ for x in ("rss", "atom", "xml")):
            urls.append(urljoin(base_url, href))
    parsed = urlparse(base_url)
    root = f"{parsed.scheme}://{parsed.netloc}"
    urls.extend([urljoin(root, "/feed/"), urljoin(root, "/rss.xml"), urljoin(root, "/feed.xml")])
    seen: set[str] = set()
    out: list[str] = []
    for url in urls:
        if url not in seen:
            out.append(url)
            seen.add(url)
    return out


def decode_embedded_base64_html(text: str) -> str:
    """Rozbalí zakódované iframe/html bloky z Visual Composeru.

    Kandelábr má ve WordPress RSS obsahu stránky poledního menu zakódovaný
    iframe na Zomato jako base64/url-encoded řetězec. Běžný get_text() ho
    nechá jako nesmyslný token, proto ho zkusíme rozbalit před parsováním.
    """
    import urllib.parse

    chunks = [text]
    # Hledej delší base64-like tokeny, které mohou být zakódované HTML.
    for token in re.findall(r"[A-Za-z0-9+/=]{40,}", text):
        try:
            decoded = base64.b64decode(token + "=" * ((4 - len(token) % 4) % 4)).decode("utf-8", errors="ignore")
        except Exception:
            continue
        decoded = urllib.parse.unquote(decoded)
        if "<iframe" in decoded or "daily_menu.php" in decoded or "zomato" in decoded:
            chunks.append(decoded)
    return "\n".join(chunks)


def extract_zomato_widget_urls(text: str) -> list[str]:
    expanded = decode_embedded_base64_html(text)
    urls: list[str] = []
    for m in re.finditer(r"https?://[^\s'\"<>]+daily_menu\.php\?entity_id=\d+", expanded):
        urls.append(html.unescape(m.group(0)))
    # Fallback pro entity_id bez celé URL.
    for entity_id in re.findall(r"entity_id\s*=\s*(\d+)", expanded):
        urls.append(f"https://www.zomato.com/widgets/daily_menu.php?entity_id={entity_id}")
    seen = set()
    out = []
    for url in urls:
        if url not in seen:
            out.append(url)
            seen.add(url)
    return out


def rss_to_lines(feed_xml: str) -> list[str]:
    """Převede RSS/Atom na řádky textu. Nepotřebuje externí balíček feedparser."""
    try:
        root = ET.fromstring(feed_xml.encode("utf-8", errors="ignore"))
    except Exception:
        return visible_lines(feed_xml)

    def local_name(tag: str) -> str:
        return tag.rsplit("}", 1)[-1].lower()

    chunks: list[str] = []
    wanted = {"title", "description", "summary", "content", "encoded"}
    for elem in root.iter():
        if local_name(elem.tag) in wanted and elem.text:
            chunks.append(elem.text)
    html_blob = decode_embedded_base64_html("\n".join(chunks))
    return visible_lines(html_blob)


def try_parse_rss_fallback(base_html: str, base_url: str, parser: Callable[[list[str], int, str], list[MenuItem]], max_items: int, target_day: str, errors: list[str], dump_dir: Path | None, restaurant_name: str) -> tuple[list[MenuItem], str | None]:
    for feed_url in discover_rss_urls(base_html, base_url):
        try:
            feed_xml = fetch_html(feed_url, timeout=12)
            lines = rss_to_lines(feed_xml)
            if dump_dir:
                safe = re.sub(r"[^A-Za-z0-9_-]+", "_", restaurant_name.lower())
                host = re.sub(r"[^A-Za-z0-9_-]+", "_", urlparse(feed_url).netloc)
                (dump_dir / f"{safe}_{host}_rss.txt").write_text("\n".join(lines), encoding="utf-8")
            items = parser(lines, max_items, target_day)
            if items:
                return items, feed_url

            # Speciální případ Kandelábr: RSS obsahuje jen zakódovaný iframe
            # na Zomato widget. Když ho najdeme, stáhneme přímo widget.
            for widget_url in extract_zomato_widget_urls(feed_xml):
                try:
                    widget_html = fetch_html(widget_url, timeout=12)
                    widget_lines = visible_lines(widget_html)
                    if dump_dir:
                        (dump_dir / f"{safe}_www_zomato_com_widget.txt").write_text("\n".join(widget_lines), encoding="utf-8")
                    widget_items = parser(widget_lines, max_items, target_day)
                    if widget_items:
                        return widget_items, widget_url
                except Exception as widget_exc:  # noqa: BLE001
                    errors.append(f"Zomato widget {urlparse(widget_url).netloc}: {widget_exc}")
        except Exception as exc:  # noqa: BLE001
            errors.append(f"RSS {urlparse(feed_url).netloc}: {exc}")
    return [], None


def clean_line(s: str) -> str:
    s = html.unescape(s).replace("\xa0", " ")
    s = re.sub(r"\s+", " ", s)
    s = s.strip(" \t\r\n-|•·")
    s = s.replace(" ,-", ",- ").replace(", Kč", " Kč")
    s = re.sub(r"\s+,-\s*Kč", ",- Kč", s)
    s = re.sub(r"\s+,-", ",-", s)
    # Weby Palatina/Kandelábru dávají ceny často jako "189,".
    # Interně je sjednotíme, ale v dashboardu už nezobrazujeme zkratku Kč.
    s = re.sub(r"^(od\s*)?(\d{2,4}),$", lambda m: f"{m.group(1) or ''}{m.group(2)},- Kč", s, flags=re.I)
    return s.strip()


def normalize_price(value: str) -> str:
    """Vrátí cenu v kratším tvaru pro dashboard, např. 195 Kč -> 195,-."""
    value = clean_line(value)
    if not value:
        return ""
    m = re.search(r"(?:od\s*)?(\d{2,4})\s*(?:,-|,|kč|Kč|CZK)?", value, flags=re.I)
    if not m:
        return value.replace("Kč", "").replace("CZK", "").strip()
    prefix = "od " if value.lower().strip().startswith("od") else ""
    return f"{prefix}{m.group(1)},-"


def strip_trailing_price_from_title(value: str) -> str:
    """Odstraní cenu nebo zatoulané Kč/CZK, pokud zůstaly omylem v názvu jídla."""
    value = clean_line(value)
    value = re.sub(r"\s+(?:od\s*)?\d{2,4}\s*(?:,-|,|kč|Kč|CZK)\s*$", "", value, flags=re.I)
    value = re.sub(r"\s+(?:kč|czk)\s*$", "", value, flags=re.I)
    return clean_line(value)


def split_title_and_note(parts: list[str], split_multiline_note: bool = False) -> tuple[str, str]:
    """Rozdělí vícerádkovou položku na název a popis.

    U Palatina bývá název jídla a jeho popis ve více řádcích před cenou,
    proto má smysl držet první řádek jako název a zbytek jako menší poznámku.
    U běžných českých menu zůstává výchozí chování konzervativní.
    """
    cleaned = [strip_trailing_price_from_title(x) for x in parts if clean_line(x)]
    if not cleaned:
        return "", ""
    if split_multiline_note and len(cleaned) >= 2:
        title = cleaned[0]
        note = clean_line(" ".join(cleaned[1:]))
        return title, note
    return clean_line(" ".join(cleaned)), ""


def visible_lines(page_html: str) -> list[str]:
    soup = BeautifulSoup(page_html, "html.parser")
    for tag in soup(["script", "style", "noscript", "svg", "iframe", "form", "header", "footer"]):
        tag.decompose()

    # U některých webů je menu v datech atributů, ne v normálním textu.
    attr_lines: list[str] = []
    for tag in soup.find_all(True):
        for attr in ("data-title", "data-content", "data-text", "alt", "title"):
            val = tag.get(attr)
            if isinstance(val, str) and len(val) > 5:
                attr_lines.extend(clean_line(x) for x in re.split(r"[\n|]+", val))

    root = soup.find("main") or soup.find("article") or soup.body or soup
    raw = root.get_text("\n")
    lines = [clean_line(x) for x in raw.splitlines()] + attr_lines
    out: list[str] = []
    prev = ""
    for line in lines:
        if not line or len(line) < 2:
            continue
        low = line.lower()
        if low in JUNK_EXACT or any(j in low for j in JUNK_CONTAINS):
            continue
        if low.startswith(("intro image", "pre loader", "logo ", "popup", "oembed", "rss ")):
            continue
        if low.startswith(("intro image", "pre loader", "logo ", "popup", "oembed", "rss ")):
            continue
        if re.fullmatch(r"[\d\s:+\-.]+", line):
            continue
        if line == prev:
            continue
        out.append(line)
        prev = line
    return out




def kvetnice_raw_lines(page_html: str) -> list[str]:
    """Vrátí textové řádky pro Květnici bez globálního JUNK filtru."""
    soup = BeautifulSoup(page_html, "html.parser")
    for tag in soup(["script", "style", "noscript", "svg", "iframe"]):
        tag.decompose()

    raw = soup.get_text("\n")
    lines: list[str] = []
    prev = ""
    for part in raw.splitlines():
        line = clean_line(part)
        if not line or len(line) < 2:
            continue
        if re.fullmatch(r"[*\s\-·]+", line):
            continue
        line = clean_line(re.sub(r"^#{1,6}\s*", "", line))
        line = clean_line(re.sub(r"^[•*]\s*", "", line))
        if line == prev:
            continue
        lines.append(line)
        prev = line
    return lines

def is_price(line: str) -> bool:
    return bool(PRICE_ONLY_RE.match(line.strip()))


def extract_price(line: str) -> tuple[str, str]:
    m = PRICE_RE.search(line)
    if not m:
        return line, ""
    price = m.group("price")
    title = (line[: m.start()] + " " + line[m.end() :]).strip(" ,;:-")
    return clean_line(title), clean_line(price)


def without_diacritics(value: str) -> str:
    table = str.maketrans({
        "ě": "e", "š": "s", "č": "c", "ř": "r", "ž": "z", "ý": "y", "á": "a", "í": "i", "é": "e", "ú": "u", "ů": "u",
        "Ě": "e", "Š": "s", "Č": "c", "Ř": "r", "Ž": "z", "Ý": "y", "Á": "a", "Í": "i", "É": "e", "Ú": "u", "Ů": "u",
    })
    return value.translate(table).lower()


DAY_VARIANTS = {
    "pondělí": ("pondeli", "pondělí", "monday"),
    "úterý": ("utery", "úterý", "tuesday"),
    "středa": ("streda", "středa", "wednesday"),
    "čtvrtek": ("ctvrtek", "čtvrtek", "thursday"),
    "pátek": ("patek", "pátek", "friday"),
}


def line_day_marker(line: str) -> str | None:
    """Vrátí den, pokud řádek vypadá jako nadpis dne v týdenním menu.

    Zdroje často mění formát: někdy je den na začátku řádku, někdy jako
    "STŘEDA 21. 5.", jindy bez diakritiky. Tohle je záměrně tolerantní,
    ale ignoruje dlouhé věty a řádky s cenou, aby za nadpis nepovažovalo jídlo.
    """
    raw = clean_line(line)
    if not raw or len(raw) > 90 or PRICE_RE.search(raw):
        return None
    norm = without_diacritics(raw)
    for canonical, variants in DAY_VARIANTS.items():
        for variant in variants:
            v = without_diacritics(variant)
            if re.search(rf"(?<![a-z]){re.escape(v)}(?![a-z])", norm):
                return canonical
    return None


def canonical_day_from_line(line: str) -> str | None:
    m = DAY_HEADING_RE.match(line.strip().lower())
    if m:
        return normalize_day(m.group(1))
    return line_day_marker(line)


def strip_day_heading(line: str, target_day: str) -> str:
    """Odstraní samotný nadpis dne, ale ponechá případný obsah za ním."""
    raw = clean_line(line)
    norm = without_diacritics(raw)
    for variant in DAY_VARIANTS[target_day]:
        v = without_diacritics(variant)
        # den + volitelná datumová část na začátku řádku
        pat = rf"^\s*{re.escape(v)}\s*(?:\d{{1,2}}\s*[./]\s*\d{{1,2}}\s*[./]?\s*(?:\d{{4}})?\s*)?[:\-–—|]*\s*"
        m = re.match(pat, norm)
        if m:
            # Použij délku matchnutého normalizovaného prefixu jako hrubý řez.
            return clean_line(raw[m.end():])
    # Když je řádek jen nadpis typu "STŘEDA 21. 5.", vrať prázdno.
    if line_day_marker(raw) == target_day and len(raw.split()) <= 5:
        return ""
    return raw


def is_section(line: str) -> bool:
    low = line.lower().strip()
    if low in SECTION_WORDS or canonical_day_from_line(line):
        return True
    letters = re.sub(r"[^A-Za-zÁ-Žá-ž]", "", line)
    return bool(letters) and len(line) <= 36 and line.upper() == line and not PRICE_RE.search(line)


def contains_empty_marker(lines: list[str]) -> bool:
    blob = "\n".join(lines).lower()
    return any(phrase in blob for phrase in EMPTY_MENU_PHRASES)


def extract_day_section(lines: list[str], target_day: str) -> list[str]:
    """Vrátí nejlepší blok mezi nadpisem cílového dne a dalším pracovním dnem.

    Důležitá oprava: některé weby mají nejdřív taby "Pondělí Úterý Středa..."
    a až potom reálné bloky "STŘEDA 20.5.2026". Starší parser se chytil právě
    těch tabů a vrátil prázdný blok. Teď projdeme všechny kandidáty a vybereme
    první, který obsahuje reálné položky/ceny.
    """
    starts: list[tuple[int, str]] = []
    last_idx = -10
    last_day = None
    for i, line in enumerate(lines):
        day = line_day_marker(line)
        if day in DAYS:
            if not (day == last_day and i - last_idx <= 2):
                starts.append((i, day))
            last_idx, last_day = i, day

    if not starts:
        return []

    def build_block(start_idx: int) -> list[str]:
        end_idx = len(lines)
        for idx, day in starts:
            if idx > start_idx and day in DAYS and day != target_day:
                end_idx = idx
                break

        raw_block = lines[start_idx:end_idx]
        block: list[str] = []
        for n, line in enumerate(raw_block):
            if n == 0:
                trimmed = strip_day_heading(line, target_day)
                if trimmed:
                    block.append(trimmed)
                continue
            if line_day_marker(line) == target_day and len(line) <= 90 and not PRICE_RE.search(line):
                trimmed = strip_day_heading(line, target_day)
                if trimmed:
                    block.append(trimmed)
                continue
            block.append(line)
        return block

    candidates: list[list[str]] = []
    for idx, day in starts:
        if day != target_day:
            continue
        block = build_block(idx)
        # ignoruj navigační tab bez obsahu
        meaningful = [
            x for x in block
            if x and not canonical_day_from_line(x) and x.lower() not in JUNK_EXACT
        ]
        if not meaningful:
            continue
        candidates.append(block)

    if not candidates:
        return []

    def score(block: list[str]) -> int:
        score_value = 0
        for x in block:
            if PRICE_RE.search(x):
                score_value += 5
            if PRICE_ONLY_RE.search(x):
                score_value += 6
            if WEIGHT_RE.match(x):
                score_value += 2
            if len(x) > 18:
                score_value += 1
            if x.lower().startswith("alergen"):
                score_value -= 2
        return score_value

    candidates.sort(key=score, reverse=True)
    return candidates[0]


def menu_window(lines: list[str], start_words: Iterable[str]) -> list[str]:
    lows = [x.lower() for x in lines]
    start = 0
    for word in start_words:
        for i, low in enumerate(lows):
            if word in low:
                start = i
                break
        if start:
            break
    selected: list[str] = []
    for line in lines[start:]:
        low = line.lower()
        if selected and any(stop in low for stop in STOP_CONTAINS):
            break
        selected.append(line)
    return selected


def parse_items_from_lines(lines: list[str], max_items: int = 10, split_multiline_note: bool = False) -> list[MenuItem]:
    items: list[MenuItem] = []
    section = ""
    pending_title: list[str] = []
    held_weight = ""
    held_price = ""

    def flush(price: str = "") -> None:
        nonlocal pending_title, held_weight, held_price
        title, note = split_title_and_note(pending_title, split_multiline_note=split_multiline_note)
        title = re.sub(r"\b(Image|Read more|Více\.\.\.|Zobrazit)\b", "", title).strip()
        title = strip_trailing_price_from_title(title)
        note = strip_trailing_price_from_title(note)
        if not title or len(title) < 3:
            pending_title = []
            held_weight = ""
            held_price = ""
            return
        if held_weight and not title.lower().startswith(held_weight.lower()):
            title = f"{held_weight} {title}"
        final_price = normalize_price(price or held_price)
        items.append(MenuItem(title=title, price=final_price, note=note, section=section))
        pending_title = []
        held_weight = ""
        held_price = ""

    for raw in lines:
        line = clean_line(raw)
        if not line:
            continue
        low = line.lower()
        if low in JUNK_EXACT or any(j in low for j in JUNK_CONTAINS):
            continue
        if len(line) > 180:
            continue
        # Nezaměňovat otevírací dobu za položku menu.
        if re.match(r"^\s*\d{1,2}[:.]\d{2}\s*[-–—]\s*\d{1,2}[:.]\d{2}\s*$", line):
            continue
        if canonical_day_from_line(line):
            if pending_title:
                flush()
            continue
        if is_section(line):
            if pending_title:
                flush()
            section = line.title()
            continue
        if is_price(line):
            if pending_title:
                flush(line)
            else:
                held_price = line
            if len(items) >= max_items:
                break
            continue
        if WEIGHT_RE.match(line):
            if pending_title and PRICE_RE.search(" ".join(pending_title)):
                flush()
            held_weight = line
            continue
        title, price = extract_price(line)
        if price:
            title = strip_trailing_price_from_title(title)
            if pending_title:
                pending_title.append(title)
            else:
                pending_title = [title]
            flush(price)
            if len(items) >= max_items:
                break
            continue
        if held_price and not pending_title:
            pending_title = [line]
            flush(held_price)
            if len(items) >= max_items:
                break
            continue

        pending_title.append(line)

    if pending_title and len(items) < max_items:
        flush()

    cleaned: list[MenuItem] = []
    seen = set()
    for item in items:
        item.title = strip_trailing_price_from_title(item.title)
        item.note = strip_trailing_price_from_title(item.note)
        item.price = normalize_price(item.price)
        title_low = item.title.lower()
        if any(j in title_low for j in STOP_CONTAINS):
            continue
        # Rok z copyrightu nebo z nadpisu dne není jídlo.
        if re.fullmatch(r"20\d{2}", item.title.strip()):
            continue
        key = (item.title.lower(), item.price.lower())
        if key in seen:
            continue
        seen.add(key)
        if not item.price:
            # U běžných parserů nechceme z krátkých řádků bez ceny dělat popisky
            # k předchozímu jídlu. Právě to rozbíjelo Palouček/Kliku.
            continue
        cleaned.append(item)
    return cleaned[:max_items]

def parse_generic(lines: list[str], max_items: int, target_day: str) -> list[MenuItem]:
    w = menu_window(lines, ["polední menu", "denní menu", "dnešní menu", "hlavní chod", "polévka", "polévky"])
    return parse_items_from_lines(w, max_items)


def parse_weekly(lines: list[str], max_items: int, target_day: str) -> list[MenuItem]:
    day_lines = extract_day_section(lines, target_day)
    if not day_lines:
        return []
    return parse_items_from_lines(day_lines, max_items)


def parse_palatino(lines: list[str], max_items: int, target_day: str) -> list[MenuItem]:
    day_lines = extract_day_section(lines, target_day)
    if not day_lines:
        return []

    # Palatino občas za páteční nabídku přimíchá dezerty nebo obecné bloky.
    # Pro dashboard chceme jen obědovou část konkrétního dne.
    filtered: list[str] = []
    for raw in day_lines:
        line = clean_line(raw)
        low = without_diacritics(line)
        if not line:
            continue
        if low in {"dezert", "dezerty", "dolci", "dessert", "desserts"}:
            break
        if any(stop in low for stop in (
            "dezert", "dezerty", "dolci", "dessert", "napoj", "napoje",
            "vinny listek", "jidelni listek", "kontakt", "rezervace",
            "rozvoz", "pizza menu", "stale menu", "akce", "zobrazit",
        )) and not PRICE_RE.search(line):
            break
        filtered.append(line)

    items = parse_items_from_lines(filtered, max_items, split_multiline_note=True)
    cleaned: list[MenuItem] = []
    for item in items:
        low_title = without_diacritics(item.title)
        low_note = without_diacritics(item.note)
        if any(bad in low_title for bad in ("dezert", "dezerty", "dolci", "dessert")):
            continue
        if any(bad in low_note for bad in ("dezert", "dezerty", "dolci", "dessert")):
            item.note = ""
        cleaned.append(item)
    return cleaned[:max_items]


def parse_klika(lines: list[str], max_items: int, target_day: str) -> list[MenuItem]:
    w = menu_window(lines, ["hlavní chod", "polední menu"])
    return parse_items_from_lines(w, max_items)


def strip_allergens(value: str) -> str:
    """Odstraní alergenové značky typu (1,3,7) nebo /1,3,7/."""
    value = clean_line(value)
    value = re.sub(r"\s*\((?:\d+\s*,?\s*)+\)\s*$", "", value)
    value = re.sub(r"\s*/\s*(?:\d+\s*,?\s*)+/\s*$", "", value)
    return clean_line(value)


def parse_external_daily(lines: list[str], max_items: int, target_day: str) -> list[MenuItem]:
    """Parser pro agregátory typu DnešníOběd.cz / Firmy.cz / Meníčka.cz.

    U Bansethů oficiální stránka jen odkazuje na DnešníOběd.cz. Kandelábr má
    oficiální stránku polední nabídky bez položek v základním HTML; denní menu
    se veřejně propisuje přes agregátory Firmy.cz/Meníčka.cz. Tenhle parser je
    proto postavený na běžném tvaru: nadpis dne, sekce, položka a cena.
    """
    clean = [clean_line(x) for x in lines if clean_line(x)]
    if not clean:
        return []

    def norm(value: str) -> str:
        return without_diacritics(clean_line(value))

    def is_external_stop(line: str) -> bool:
        low = norm(line)
        return any(stop in low for stop in (
            "zobrazit vice", "odkazy", "detail restaurace", "nahlasit chybu",
            "predstaveni", "zobrazit dalsi restaurace", "nacitam dalsi restaurace",
            "uzitecne odkazy", "dnesniobed.cz", "nabidky podobnych", "fotogalerie",
            "hodnoceni firmy", "paticka stranky", "partneri", "kategorie", "stitky",
            "podobne firmy", "cele dnesni menu", "dalsi dny", "web restaurace",
            "ukaz na mape", "tel:", "ico", "dic", "e-mail", "oteviraci hodiny",
            "pridat hodnoceni", "oblibene restaurace", "nejlepsi menu", "menicka.cz",
            "kontaktujte nas", "otevreno", "otevreno dnes", "naplanovat trasu",
            "detail firmy", "mapa", "znacka polohy", "trasa", "web", "info",
        ))

    def looks_like_profile_or_address(line: str) -> bool:
        """True pro řádky typu adresa, otevírací doba, hodnocení nebo profil restaurace.

        Důvod: Firmy.cz u Kandelábru vrátily profilovou stránku jiné/okolní firmy
        a obecný parser z řádku „Ječná 511/16, Praha...“ vyrobil nesmyslnou cenu 16,-.
        Externí parser proto musí umět profilové řádky tvrdě odmítnout.
        """
        raw = clean_line(line)
        low = norm(raw)

        if not raw:
            return True

        # Adresy: Ječná 511/16, Štětkova 1638/18, 140 00 Praha 4...
        if re.search(r"\b\d{2,5}\s*/\s*\d{1,4}\b", raw):
            return True
        if re.search(r"\b\d{3}\s*\d{2}\b", raw) and any(x in low for x in ("praha", "nusle", "nove mesto", "psc")):
            return True
        if any(x in low for x in (
            "praha", "nusle", "nove mesto", "stetkova", "jecna", "pankrac",
            "restaurace", "restaurant", "vysehradsky", "pivovarsky dum",
            "detail firmy", "naplanovat trasu", "znacka polohy", "mapa ",
            "hodnoceni", "fotogalerie", "platebni karty", "stravenky",
            "otevreno", "dnes do", "dnes:", "pondeli:", "utery:", "streda:",
            "ctvrtek:", "patek:", "sobota:", "nedele:", "kontaktujte nas",
            "web", "trasa", "info", "registrace", "administrace", "reklama",
            "o restauraci", "rozsirene informacace", "zobrazit plnou verzi",
        )):
            return True

        # Časy a tel. čísla nejsou ceny.
        if re.search(r"\b\d{1,2}:\d{2}\b", raw):
            return True
        if re.search(r"\+?\d{3}\s*\d{3}\s*\d{3}", raw):
            return True

        return False

    def is_probably_menu_title(line: str) -> bool:
        """Hrubý sanity check názvu jídla u externích zdrojů."""
        raw = clean_line(line)
        low = norm(raw)
        if looks_like_profile_or_address(raw):
            return False
        if len(raw) < 4 or len(raw) > 180:
            return False
        # Jídla obvykle obsahují aspoň jedno písmeno s českou/latinkovou abecedou.
        if not re.search(r"[A-Za-zÁ-Žá-ž]", raw):
            return False
        # Profilové fráze bez kuchařského významu.
        if any(x in low for x in (
            "family friendly", "platba kartou", "salonek", "zahradka",
            "parkoviste", "bezbarierove", "klimatizovano", "wifi",
            "cykliste vitani", "nabijeni elektromobilu", "opravit udaje",
            "uzivatel", "nahlasit", "pluxee", "prazdroj", "seznam pes",
        )):
            return False
        return True

    def is_section_heading(line: str) -> bool:
        low = norm(line)
        if PRICE_RE.search(line) or is_price(line):
            return False
        if canonical_day_from_line(line):
            return False
        if len(line) > 70:
            return False
        return (
            low in {"denni menu", "jidelni listek", "polevka", "polevky", "dezert"}
            or "delikates" in low
            or "z hrnce" in low
            or "dnesni menu" in low
            or "specialita" in low
        )

    def extract_external_price(line: str) -> tuple[str, str]:
        """Přísnější extrakce ceny pro agregátory/Zomato.

        Běžný PRICE_RE umí zachytit i text typu „/1,3,7,10,12/“ jako cenu
        „10,“. To u Zomato rozbíjelo Kandelábr. U externích zdrojů proto
        bereme inline cenu jen tehdy, když je jasně označená jako Kč/CZK nebo
        má tvar 175,-. Čistě číselné ceny řeší větev is_price(line), kde je
        cena na samostatném řádku.
        """
        raw = clean_line(line)
        m = re.search(r"(?P<price>(?:od\s*)?\d{2,4}\s*(?:,-|Kč|kč|CZK))\b", raw)
        if not m:
            return raw, ""
        price = m.group("price")
        title = clean_line((raw[:m.start()] + " " + raw[m.end():]).strip(" ,;:-"))
        return title, clean_line(price)

    def strip_zomato_numbering(value: str) -> str:
        return clean_line(re.sub(r"^\d+\.\s*", "", value))

    def mostly_uppercase(value: str) -> bool:
        letters = [ch for ch in value if ch.isalpha()]
        if len(letters) < 8:
            return False
        upper = sum(1 for ch in letters if ch.isupper())
        return upper / max(1, len(letters)) >= 0.72

    def pretty_food_title(value: str) -> str:
        """Sjednotí názvy z externích widgetů s ostatními kartami.

        Zomato u Kandelábru vrací celý text verzálkami. Dashboard pak sice
        funguje datově správně, ale vizuálně působí jinak než Palouček,
        Palatino, Klika nebo Bansethů. Převod děláme jen u textů, které jsou
        zjevně převážně uppercase, aby se nerozbila dobře naformátovaná menu
        z DnešníOběd.cz.
        """
        raw = clean_line(value)
        if not mostly_uppercase(raw):
            return raw
        s = raw.lower()
        # Typické zkratky a značky, které mají zůstat verzálkami.
        keep_upper = {
            "bbq": "BBQ",
            "cheddar": "cheddar",
        }
        # Zachovej kompaktní tvar gramáže: 150G -> 150g.
        s = re.sub(r"(\d+)\s*g\b", r"\1g", s, flags=re.I)
        # Velké písmeno na začátku a po úvodní gramáži.
        s = s[:1].upper() + s[1:] if s else s
        s = re.sub(
            r"^(\d+g\s+)([a-zá-ž])",
            lambda m: m.group(1) + m.group(2).upper(),
            s,
        )
        for src, dst in keep_upper.items():
            s = re.sub(rf"\b{re.escape(src)}\b", dst, s, flags=re.I)
        return clean_line(s)

    def normalize_external_item_title(value: str) -> tuple[str, str | None]:
        """Vrátí title + případnou sekci odvozenou z názvu.

        Kandelábr ze Zomata posílá polévku ve formátu
        „POLÉVKA-HOVĚZÍ VÝVAR...“. Pro dashboard je čitelnější samostatná
        sekce „Polévka“ a title bez prefixu.
        """
        title = strip_zomato_numbering(strip_allergens(strip_trailing_price_from_title(value)))
        derived_section = None
        m = re.match(r"^(?:pol[eé]vka)\s*[-–—:]\s*(.+)$", title, flags=re.I)
        if m:
            # Polévku necháváme jako běžnou položku bez samostatného štítku,
            # aby Kandelábr vizuálně nepřidával zbytečnou sekci navíc.
            title = clean_line(m.group(1))
        title = pretty_food_title(title)
        return title, derived_section

    def finish_pending(price_line: str) -> None:
        nonlocal pending_title
        if not pending_title:
            return
        title, derived_section = normalize_external_item_title(pending_title)
        item_section = derived_section or section
        if title and is_probably_menu_title(title):
            items.append(MenuItem(title=title, price=normalize_price(price_line), section=item_section))
        pending_title = ""

    # Najdi blok cílového dne. Když agregátor vrací jen dnešní den a skript
    # běží bez konkrétního --day, je to ideální. Při ručním --day mimo dostupný
    # den raději nevracíme cizí den, pokud existuje nějaký jasný nadpis dne.
    day_indices: list[tuple[int, str]] = []
    for i, line in enumerate(clean):
        day = line_day_marker(line)
        if day in DAYS:
            day_indices.append((i, day))

    start = None
    for i, day in day_indices:
        if day == target_day:
            start = i + 1
            break

    # Pokud není nadpis dne detekovaný, zkus start za textem polední/denní nabídky.
    # To pomůže u některých mirrorů, které denní nadpis vynechají.
    if start is None and not day_indices:
        for i, line in enumerate(clean):
            low = norm(line)
            if "poledni nabidka" in low or "denni menu" in low or "aktualni poledni menu" in low:
                start = i + 1
                break

    # Meníčka.cz někdy vrací stránku, kde je první použitelná položka až za názvem restaurace
    # a bez jasného denního nadpisu v textových řádcích. V takovém případě začneme před
    # první cenovou položkou a necháme parser složit název + cenu.
    if start is None and not day_indices:
        for i, line in enumerate(clean):
            if PRICE_RE.search(line) or is_price(line):
                start = max(0, i - 2)
                break

    if start is None:
        return []

    block: list[str] = []
    for raw in clean[start:]:
        if canonical_day_from_line(raw):
            # Další den = konec bloku.
            break
        if is_external_stop(raw):
            break
        low = norm(raw)
        if low in {"po", "ut", "st", "ct", "pa", "so", "ne", "zobrazit vse"}:
            continue
        if re.fullmatch(r"\d+[,.]?\d*\s*\(?\d*\)?", raw):
            continue
        block.append(raw)
        if len(block) > 80:
            break

    items: list[MenuItem] = []
    section = ""
    pending_title = ""

    for raw in block:
        line = clean_line(raw)
        if not line:
            continue
        low = norm(line)
        if is_section_heading(line):
            section = re.sub(r"^#+\s*", "", line).strip().title()
            pending_title = ""
            continue
        if is_price(line):
            finish_pending(line)
            if len(items) >= max_items:
                break
            continue
        title, price = extract_external_price(line)
        if price:
            if pending_title and title:
                title = clean_line(f"{pending_title} {title}")
            title, derived_section = normalize_external_item_title(title)
            item_section = derived_section or section
            if title and is_probably_menu_title(title):
                items.append(MenuItem(title=title, price=normalize_price(price), section=item_section))
            pending_title = ""
            if len(items) >= max_items:
                break
            continue
        # Firmy.cz/DnešníOběd/Zomato často dávají název a cenu na další řádek.
        # Zomato navíc umí jedno jídlo rozdělit do více textových řádků; proto
        # další textový řádek připojujeme, ne přepisujeme.
        if is_probably_menu_title(line) and not any(x in low for x in ("image", "rating", "navigovat", "zavrit")):
            line = strip_zomato_numbering(line) if not pending_title else line
            pending_title = clean_line(f"{pending_title} {line}" if pending_title else line)
        else:
            pending_title = ""

    cleaned: list[MenuItem] = []
    seen: set[tuple[str, str]] = set()
    for item in items:
        item.title, derived_section = normalize_external_item_title(item.title)
        if derived_section and not item.section:
            item.section = derived_section
        item.price = normalize_price(item.price)
        if not item.title or not item.price:
            continue
        if not is_probably_menu_title(item.title):
            continue
        if any(j in item.title.lower() for j in STOP_CONTAINS):
            continue
        key = (item.title.lower(), item.price.lower())
        if key in seen:
            continue
        seen.add(key)
        cleaned.append(item)
    return cleaned[:max_items]


def parse_kvetnice(lines: list[str], max_items: int, target_day: str) -> list[MenuItem]:
    """Speciální parser pro Na Květnici.

    Květnice má polední sekci přímo v homepage, ale před ní i za ní je hodně
    instagramového a obecného obsahu. Parser proto bere jen blok od „Polední
    nabídka 11:00 - 15:00“ po „Nápoje k menu“ a pracuje jen s položkami s cenou.
    Když cenové menu není dostupné, vrátí prázdno a dashboard ukáže hlášku.
    """

    def norm(value: str) -> str:
        return without_diacritics(clean_line(value))

    def is_stop(line: str) -> bool:
        low = norm(line)
        return any(stop in low for stop in (
            "napoje k menu", "vsechna masa", "euro prijimame", "platba kartou",
            "jidelni listek", "rezervace", "nakouknete pod poklicku", "galerie",
            "instagram", "template by", "nasi partneri", "kde nas najdete",
            "loading", "karneval", "zahradka", "free website templates", "o-nas-foto",
        ))

    def is_skip(line: str) -> bool:
        low = norm(line)
        if not line:
            return True
        if low.startswith("svatek"):
            return True
        if canonical_day_from_line(line):
            return True
        if re.fullmatch(r"\d{1,2}[./]\d{1,2}[./]\d{4}", low):
            return True
        if re.fullmatch(r"[*\.\s-]+", line):
            return True
        if low in {"zobrazit", "prectist cele", "restaurant na kvetnici", "restaurace"}:
            return True
        return False

    clean = [clean_line(x) for x in lines if clean_line(x)]
    if not clean:
        return []

    # Vyber jen polední blok. Na webu je teď zřetelně mezi „Polední nabídka“
    # a „Nápoje k menu“. Když se text slije, nouzově vytvoříme řádky podle cen.
    start_idx = None
    for i, line in enumerate(clean):
        low = norm(line)
        if "poledni nabidka" in low and ("11:00" in line or "15:00" in line or i < len(clean) - 3):
            start_idx = i
            break
    if start_idx is None:
        for i, line in enumerate(clean):
            if norm(line) in {"polevky", "poledni nabidka"}:
                start_idx = i
                break
    if start_idx is None:
        return []

    block: list[str] = []
    for raw in clean[start_idx:]:
        if block and is_stop(raw):
            break
        if is_skip(raw):
            continue
        block.append(raw)
        if len(block) > 90:
            break

    if not any(PRICE_RE.search(x) for x in block):
        blob = clean_line(" ".join(clean[start_idx:]))
        blob_norm = norm(blob)
        stop_pos = blob_norm.find(" napoje k menu ")
        if stop_pos > 0:
            blob = blob[:stop_pos]
        blob = re.sub(r"\b(Polévky|Polední nabídka|Dnešní menu|Specialita týdne)\b", r"\n\1\n", blob, flags=re.I)
        blob = re.sub(r"(\d{2,4}\s*Kč)", r"\1\n", blob, flags=re.I)
        block = [clean_line(x) for x in blob.split("\n") if clean_line(x)]

    items: list[MenuItem] = []
    section = ""

    def add_item(title: str, price: str, note: str = "", forced_section: str | None = None) -> None:
        title = strip_trailing_price_from_title(title)
        note = strip_trailing_price_from_title(note)
        if not title or not price:
            return
        low_title = norm(title)
        if any(j in low_title for j in STOP_CONTAINS):
            return
        if any(bad in low_title for bad in ("napoje", "coca-cola", "limonada", "natura", "kava dle vyberu")):
            return
        items.append(MenuItem(title=title, price=normalize_price(price), note=note, section=forced_section or section.title()))

    i = 0
    while i < len(block):
        raw = clean_line(block[i])
        low = norm(raw)
        if not raw or is_skip(raw):
            i += 1
            continue
        if is_stop(raw):
            break
        if "poledni nabidka" in low and not PRICE_RE.search(raw):
            section = "Polední nabídka"
            i += 1
            continue
        if low == "polevky":
            section = "Polévky"
            i += 1
            continue
        if low == "specialita tydne":
            section = "Specialita týdne"
            i += 1
            continue
        if low.startswith("dnesni menu"):
            title, price = extract_price(raw)
            if price:
                # Následující řádky u Dnešního menu jsou součástí setu. Na TV je
                # kvůli prostoru necháme jako jednu položku s cenou setu.
                add_item("Dnešní menu", price, forced_section="Dnešní menu")
            section = "Dnešní menu"
            i += 1
            continue

        title, price = extract_price(raw)
        if price:
            note = ""
            if i + 1 < len(block):
                nxt = clean_line(block[i + 1])
                if nxt and not PRICE_RE.search(nxt) and not is_skip(nxt) and not is_stop(nxt):
                    nxt_low = norm(nxt)
                    if nxt_low not in {"polevky", "poledni nabidka", "specialita tydne"} and not nxt_low.startswith("dnesni menu"):
                        note = nxt
                        i += 1
            add_item(title, price, note=note)
            if len(items) >= max_items:
                break
        i += 1

    cleaned: list[MenuItem] = []
    seen: set[tuple[str, str]] = set()
    for item in items:
        item.title = strip_trailing_price_from_title(item.title)
        item.note = strip_trailing_price_from_title(item.note)
        item.price = normalize_price(item.price)
        if not item.title or not item.price:
            continue
        key = (item.title.lower(), item.price.lower())
        if key in seen:
            continue
        seen.add(key)
        cleaned.append(item)
    return cleaned[:max_items]

def parse_paloucek(lines: list[str], max_items: int, target_day: str) -> list[MenuItem]:
    # Palouček má nahoře polévky a zvýhodněné menu, které v dashboardu nechceme.
    # Začínáme až od sekce DNES DOPORUČUJEME a pokračujeme přes POLEDNÍ NABÍDKU a DEZERT.
    compact: list[str] = []
    started = False
    for line in lines:
        low = line.lower()
        if "dnes doporučujeme" in low:
            started = True
            compact.append("Dnes doporučujeme")
            continue
        if not started:
            continue
        if any(stop in low for stop in ("aktuality", "kudy k nám", "rss", "click to open", "larger map", "copyright", "kontakt")):
            break
        if low in {"polévka", "polévky", "menu i.", "menu ii.", "menu iii."}:
            continue
        compact.append(line)
    return parse_items_from_lines(compact, max_items)


PARSERS: dict[str, Callable[[list[str], int, str], list[MenuItem]]] = {
    "generic": parse_generic,
    "weekly": parse_weekly,
    "palatino": parse_palatino,
    "klika": parse_klika,
    "external_daily": parse_external_daily,
    "kvetnice": parse_kvetnice,
    "paloucek": parse_paloucek,
}



def postprocess_restaurant_items(name: str, items: list[MenuItem]) -> list[MenuItem]:
    """Restaurant-specific cleanup after parsing.

    U Bansethů on DnešníOběd.cz sometimes emits category headings as separate
    rows without price. The generic parser then prepends that heading to the
    next priced dish, e.g. "Polévka je grunt Silný hovězí vývar...".
    For the TV dashboard we want only dish names and prices, without these
    long editorial category labels.
    """
    if name != "U Bansethů":
        return items

    pure_heading_norms = {
        "polevka je grunt",
        "dnesni delikatesy",
        "patecni klasika",
        "rizky rizky a zase rizky",
        "z hrnce nasich kucharskych mistru",
        "dezert",
        "dezerty",
        "stala nabidka",
        "dnesni menu",
    }

    # Ordered from longer/more specific to shorter. These labels may be glued
    # to the beginning of the actual dish title by parse_items_from_lines().
    heading_prefixes = [
        "Řízky, řízky a zase řízky",
        "Z hrnce našich kuchařských mistrů",
        "Polévka je grunt",
        "Páteční klasika",
        "Dnešní delikatesy",
        "Dezert",
        "Dezerty",
    ]

    def strip_bansethu_heading_prefix(title: str) -> str:
        value = clean_line(title)
        value_norm = without_diacritics(value).strip().lower()
        for prefix in heading_prefixes:
            prefix_norm = without_diacritics(prefix).strip().lower()
            if value_norm == prefix_norm:
                return ""
            if value_norm.startswith(prefix_norm + " "):
                # Use the original prefix length for a clean visible cut.
                value = clean_line(value[len(prefix):])
                value_norm = without_diacritics(value).strip().lower()
        return value

    cleaned: list[MenuItem] = []
    for item in items:
        title = strip_bansethu_heading_prefix(item.title)
        title_norm = without_diacritics(clean_line(title)).strip().lower()
        # Drop pure category headings if they accidentally entered as items.
        if not title or title_norm in pure_heading_norms:
            continue
        if not item.price:
            # On DnešníOběd.cz valid lunch rows have prices; unpriced rows tend
            # to be labels/navigation. Keep this conservative for Bansethů only.
            continue
        item.title = title
        item.section = ""
        cleaned.append(item)
    return cleaned

def get_menu(
    cfg: Restaurant,
    target_day: str,
    dump_dir: Path | None = None,
    cache: dict | None = None,
    use_cache: bool = True,
    cache_max_age_hours: int = 36,
    try_rss: bool = True,
) -> dict:
    errors: list[str] = []
    parser = PARSERS[cfg.parser]
    for url in cfg.sources:
        try:
            page = fetch_html(url)
            if cfg.parser == "kvetnice":
                lines = kvetnice_raw_lines(page)
                items = parser(lines, cfg.max_items, target_day)
                if not items:
                    lines = visible_lines(page)
                    items = parser(lines, cfg.max_items, target_day)
            else:
                # Kandelábr: oficiální stránka může v RSS/Visual Composeru nést
                # zakódovaný Zomato iframe. Pokud je iframe vidět už v HTML,
                # zkusíme ho stáhnout rovnou.
                items = []
                lines = visible_lines(page)
                for widget_url in extract_zomato_widget_urls(page):
                    try:
                        widget_html = fetch_html(widget_url, timeout=12)
                        widget_lines = visible_lines(widget_html)
                        widget_items = parser(widget_lines, cfg.max_items, target_day)
                        if widget_items:
                            lines = widget_lines
                            items = widget_items
                            url = widget_url
                            break
                    except Exception as widget_exc:  # noqa: BLE001
                        errors.append(f"Zomato widget {urlparse(widget_url).netloc}: {widget_exc}")
                if not items:
                    items = parser(lines, cfg.max_items, target_day)
            items = postprocess_restaurant_items(cfg.name, items)
            if dump_dir:
                dump_dir.mkdir(parents=True, exist_ok=True)
                safe = re.sub(r"[^A-Za-z0-9_-]+", "_", cfg.name.lower())
                host = re.sub(r"[^A-Za-z0-9_-]+", "_", urlparse(url).netloc)
                (dump_dir / f"{safe}_{host}.txt").write_text("\n".join(lines), encoding="utf-8")
            # U některých restaurací je v daný den jen polévka + jedno menu nebo položky bez cen.
            # Když parser našel aspoň jednu smysluplnou položku, bereme to jako úspěch.
            if items:
                if cache is not None:
                    cache_set(cache, cfg, target_day, url, items)
                return {
                    "name": cfg.name, "url": url, "items": items, "error": None,
                    "empty_ok": False, "cached": False, "source_type": "html",
                }

            if try_rss:
                rss_items, rss_url = try_parse_rss_fallback(
                    page, url, parser, cfg.max_items, target_day, errors, dump_dir, cfg.name
                )
                if rss_items and rss_url:
                    rss_items = postprocess_restaurant_items(cfg.name, rss_items)
                    if not rss_items:
                        errors.append(f"RSS {urlparse(rss_url).netloc}: pouze sekční nadpisy / bez položek")
                    else:
                        if cache is not None:
                            cache_set(cache, cfg, target_day, rss_url, rss_items)
                        return {
                            "name": cfg.name, "url": rss_url, "items": rss_items, "error": None,
                            "empty_ok": False, "cached": False, "source_type": "rss",
                        }

            if cfg.empty_is_ok or contains_empty_marker(lines):
                # Důležité: u restaurací s více zdroji nesmíme skončit hned na prvním
                # prázdném zdroji. Přesně to blokovalo Kandelábr: Firmy.cz nic
                # nevrátily a skript se už nedostal k Meníčka.cz.
                errors.append(f"{urlparse(url).netloc}: prázdný zdroj / menu pro {DAY_TITLE[target_day].lower()} nenalezeno")
                continue
            errors.append(f"{urlparse(url).netloc}: menu pro {DAY_TITLE[target_day].lower()} nenalezeno / málo položek")
        except Exception as exc:  # noqa: BLE001
            errors.append(f"{urlparse(url).netloc}: {exc}")

    if use_cache and cache is not None:
        cached = cache_get(cache, cfg, target_day, cache_max_age_hours)
        if cached:
            cached["error"] = "Použito poslední úspěšně načtené menu, protože aktuální zdroj selhal."
            return cached

    return {
        "name": cfg.name, "url": cfg.sources[0], "items": [],
        "error": "; ".join(errors), "empty_ok": cfg.empty_is_ok,
        "cached": False, "source_type": "none",
    }




def resolve_output_path(value: str) -> Path:
    """Vrátí cestu k výstupu.

    Relativní cesta se ukládá vedle tohoto skriptu, ne do aktuální pracovní
    složky terminálu. Díky tomu se dashboard.html objeví u .py souboru i při
    spuštění z jiné složky nebo přes zástupce.
    """
    p = Path(value).expanduser()
    if p.is_absolute():
        return p.resolve()
    return (Path(__file__).resolve().parent / p).resolve()


def write_report(results: Iterable[dict], output: Path, target_day: str) -> None:
    lines = [f"# Polední menu debug report – {DAY_TITLE[target_day]}", ""]
    for r in results:
        status = "OK" if r.get("items") else ("EMPTY_OK" if r.get("empty_ok") and not r.get("error") else "ERROR")
        if r.get("cached"):
            status = "CACHE"
        lines.extend([
            f"## {r.get('name')}",
            f"- Status: {status}",
            f"- Zdroj: {r.get('source_type')}",
            f"- URL: {r.get('url')}",
            f"- Položek: {len(r.get('items') or [])}",
        ])
        if r.get("cache_updated_at"):
            lines.append(f"- Cache z: {r.get('cache_updated_at')}")
        if r.get("error"):
            lines.append(f"- Poznámka/chyba: {r.get('error')}")
        if r.get("items"):
            lines.append("- Nalezené položky:")
            for item in r.get("items") or []:
                price = f" — {item.price}" if item.price else ""
                section = f" [{item.section}]" if item.section else ""
                lines.append(f"  - {item.title}{price}{section}")
        lines.append("")
    output.write_text("\n".join(lines), encoding="utf-8")

def render_dashboard(results: Iterable[dict], output: Path, refresh_seconds: int, target_day: str) -> None:
    now = datetime.now().strftime("%d. %m. %Y %H:%M")
    cards: list[str] = []
    for r in results:
        name = html.escape(r["name"])
        source_url = r.get("url") or ""
        host = html.escape(urlparse(source_url).netloc.replace("www.", ""))
        if r.get("source_type") == "rss":
            host = f"{host} · RSS"
        if r.get("cached"):
            host = f"{host} · cache"
        items: list[MenuItem] = r.get("items") or []
        if items:
            rows: list[str] = []
            last_section = None
            # Na TV zbytečně zabírají místo dlouhé sekční štítky u restaurací,
            # kde jsou spíš navigační než informační. Palatino/Klika/Kandelábr
            # je necháváme, pokud je parser skutečně potřebuje.
            suppress_sections = r.get("name") in {"Na Paloučku", "U Bansethů"}
            for item in items:
                if item.section and item.section != last_section and not suppress_sections:
                    rows.append(f"<div class='section-label'>{html.escape(item.section)}</div>")
                    last_section = item.section
                price = f"<span class='price'>{html.escape(item.price)}</span>" if item.price else ""
                note = f"<div class='note'>{html.escape(item.note)}</div>" if item.note else ""
                rows.append(
                    "<div class='dish'>"
                    "<div class='dish-main'>"
                    f"<div class='dish-title'>{html.escape(item.title)}</div>"
                    f"{price}"
                    "</div>"
                    f"{note}"
                    "</div>"
                )
            body = "\n".join(rows)
        elif r.get("empty_ok") and not r.get("error"):
            body = "<div class='empty'>Dnes zatím bez zveřejněného poledního menu.</div>"
        elif r.get("empty_ok"):
            body = f"<div class='empty'>Menu není dostupné.<br><span>{html.escape(r.get('error') or '')}</span></div>"
        else:
            body = f"<div class='error'>Nepodařilo se načíst menu.<br>{html.escape(r.get('error') or '')}</div>"
        cards.append(
            f"""
            <section class="card">
              <header>
                <h2>{name}</h2>
                <a href="{html.escape(source_url)}">{host}</a>
              </header>
              <div class="menu-list">{body}</div>
            </section>
            """
        )

    html_doc = f"""<!doctype html>
<html lang="cs">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta http-equiv="refresh" content="{refresh_seconds}">
<title>Polední menu – {html.escape(DAY_TITLE[target_day])}</title>
<style>
/* TV-safe CSS: záměrně bez CSS variables, clamp(), gridu a gradientů.
   Některé smart TV prohlížeče jsou starší a moderní CSS ignorují. */
* {{ box-sizing: border-box; }}
html, body {{
  margin: 0;
  padding: 0;
  width: 100%;
  min-height: 100%;
}}
body {{
  padding: 14px;
  background: #f4efe7;
  color: #1c1917;
  font-family: Arial, Helvetica, sans-serif;
}}
.topbar {{
  display: table;
  width: 100%;
  margin-bottom: 10px;
}}
.topbar > div {{
  display: table-cell;
  vertical-align: bottom;
}}
.topbar > div:last-child {{
  text-align: right;
}}
h1 {{
  margin: 0;
  font-size: 46px;
  line-height: 0.95;
  letter-spacing: -1px;
}}
.subtitle {{
  margin-top: 3px;
  color: #8b3f1d;
  font-size: 23px;
  font-weight: 800;
}}
.timestamp {{
  color: #766f66;
  font-size: 14px;
  white-space: nowrap;
}}
.grid {{
  display: block;
  width: 100%;
  font-size: 0;
}}
.card {{
  display: inline-block;
  vertical-align: top;
  width: 32.45%;
  min-height: 0;
  margin: 0 0.9% 10px 0;
  padding: 11px 13px 10px;
  background: #fffdf8;
  border: 1px solid #e6ded2;
  border-radius: 16px;
  box-shadow: 0 8px 22px rgba(61,45,30,0.10);
  overflow: hidden;
  font-size: 16px;
}}
.card:nth-child(3n) {{
  margin-right: 0;
}}
.card header {{
  display: table;
  width: 100%;
  padding-bottom: 6px;
  margin-bottom: 6px;
  border-bottom: 1px solid #e6ded2;
}}
.card header h2, .card header a {{
  display: table-cell;
  vertical-align: baseline;
}}
h2 {{
  margin: 0;
  font-size: 23px;
  line-height: 1.05;
  letter-spacing: -1px;
}}
a {{
  color: #766f66;
  text-decoration: none;
  font-size: 12px;
  text-align: right;
  white-space: nowrap;
}}
.section-label {{
  display: inline-block;
  margin: 2px 0 4px;
  padding: 3px 7px;
  border-radius: 999px;
  background: #fbf3e7;
  color: #8b3f1d;
  font-weight: 800;
  font-size: 11px;
  text-transform: uppercase;
  letter-spacing: 0.04em;
}}
.dish {{
  display: block;
  width: 100%;
  padding: 4px 0;
  border-bottom: 1px dashed #eadfce;
}}
.dish:last-child {{ border-bottom: 0; }}
.dish-main {{
  display: table;
  width: 100%;
}}
.dish-title {{
  display: table-cell;
  vertical-align: top;
  padding-right: 8px;
  font-size: 15px;
  line-height: 1.15;
  font-weight: 650;
}}
.price {{
  display: table-cell;
  vertical-align: top;
  color: #111827;
  font-size: 15px;
  line-height: 1.1;
  font-weight: 900;
  white-space: nowrap;
  text-align: right;
}}
.note {{
  display: block;
  color: #766f66;
  font-size: 12px;
  line-height: 1.18;
  margin-top: 2px;
  padding-right: 42px;
}}
.error, .empty {{
  color: #766f66;
  font-size: 15px;
  line-height: 1.25;
  padding: 12px 0;
}}
.empty {{ opacity: 0.75; }}
.empty span {{ font-size: 13px; }}
@media (max-width: 1200px) {{
  .card {{ width: 48.5%; }}
  .card:nth-child(3n) {{ margin-right: 1.3%; }}
  .card:nth-child(2n) {{ margin-right: 0; }}
}}
@media (max-width: 760px) {{
  body {{ padding: 14px; }}
  .topbar, .topbar > div {{ display: block; text-align: left; }}
  .timestamp {{ margin-top: 8px; }}
  h1 {{ font-size: 42px; }}
  .subtitle {{ font-size: 24px; }}
  .card {{ display: block; width: 100%; min-height: auto; margin-right: 0; }}
}}
</style>
</head>
<body>
  <div class="topbar">
    <div><h1>Polední menu</h1><div class="subtitle">{html.escape(DAY_TITLE[target_day])}</div></div>
    <div class="timestamp">Aktualizováno {html.escape(now)} · refresh {refresh_seconds // 60} min</div>
  </div>
  <main class="grid">{''.join(cards)}</main>
</body>
</html>
"""
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(html_doc, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Polední menu dashboard v5.7")
    ap.add_argument("--day", default=None, help="pondeli, utery, streda, ctvrtek nebo patek. Výchozí je dnešní pracovní den.")
    ap.add_argument("--output", default="dashboard.html", help="Kam uložit HTML. Relativní cesta se ukládá vedle skriptu.")
    ap.add_argument("--refresh", type=int, default=1800, help="Auto-refresh v sekundách")
    ap.add_argument("--dump", action="store_true", help="Uloží vyčištěné texty zdrojových stránek do ./debug_dump")
    ap.add_argument("--report", default=None, help="Volitelně uloží markdown report se stavem parseru")
    ap.add_argument("--cache-file", default=".lunch_menu_cache.json", help="Soubor s cache posledních úspěšných menu")
    ap.add_argument("--cache-max-age-hours", type=int, default=36, help="Maximální stáří cache, která se použije při výpadku")
    ap.add_argument("--no-cache", action="store_true", help="Vypne použití i ukládání cache")
    ap.add_argument("--no-rss", action="store_true", help="Vypne RSS/Atom fallback")
    ap.add_argument("--no-open", action="store_true", help="Po vytvoření dashboard automaticky neotevře v prohlížeči")
    args = ap.parse_args(argv)

    target_day = normalize_day(args.day)
    dump_dir = Path("debug_dump") if args.dump else None
    cache_path = Path(args.cache_file)
    cache = None if args.no_cache else load_cache(cache_path)

    results = []
    for cfg in RESTAURANTS:
        print(f"Stahuji: {cfg.name}", file=sys.stderr)
        results.append(get_menu(
            cfg,
            target_day=target_day,
            dump_dir=dump_dir,
            cache=cache,
            use_cache=not args.no_cache,
            cache_max_age_hours=args.cache_max_age_hours,
            try_rss=not args.no_rss,
        ))

    if cache is not None:
        save_cache(cache_path, cache)

    out = resolve_output_path(args.output)
    render_dashboard(results, out, args.refresh, target_day)
    print(f"Hotovo: {out}")
    print(f"HTML soubor: {out}")
    if not args.no_open:
        try:
            webbrowser.open(out.as_uri())
        except Exception as exc:  # noqa: BLE001
            print(f"Dashboard se nepodařilo automaticky otevřít: {exc}", file=sys.stderr)
    if dump_dir:
        print(f"Debug dump: {dump_dir.resolve()}")
    if args.report:
        report_path = resolve_output_path(args.report)
        write_report(results, report_path, target_day)
        print(f"Report: {report_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
