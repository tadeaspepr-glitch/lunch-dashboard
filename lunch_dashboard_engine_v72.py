#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Polední menu dashboard v7.2
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
import os
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
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36 lunch-dashboard/6.6"
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
            # v6.9: web přešel na jednostránkovou verzi, polední nabídka je
            # přímo na homepage v sekci #poledni. Stará podstránka vrací 404.
            "https://www.restpaloucek.cz/",
            "https://restpaloucek.cz/",
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
        "U Bansethů / Pivovar Bašta",
        [
            # Primární zdroj. V GitHub Actions někdy zlobí www/IPv6, proto jsou
            # hned pod ním připravené non-www a HTTP varianty stejné stránky.
            "https://www.dnesniobed.cz/restaurace-hospoda/nusle_u-bansethu-a-basta",
            "https://dnesniobed.cz/restaurace-hospoda/nusle_u-bansethu-a-basta",
            "http://www.dnesniobed.cz/restaurace-hospoda/nusle_u-bansethu-a-basta",
            "http://dnesniobed.cz/restaurace-hospoda/nusle_u-bansethu-a-basta",
            # v6.9: odlehčený iframe, který DnešníOběd.cz vkládá na web
            # ubansethu.cz/poledni-nabidka/. Stejná data, menší stránka.
            "https://www.dnesniobed.cz/jidelnicek/frame/frame.php/2301_1",
            # Zdroje na jiných serverech – pomohou, když DnešníOběd.cz neodpovídá.
            # Firmy.cz (Seznam) ukazuje menu s datem; parser bere jen dnešní den,
            # takže neaktualizované menu z jiného dne se nezobrazí.
            "https://www.firmy.cz/detail/684629-restaurace-u-bansethu-praha-nusle.html",
            "https://www.menicka.cz/4439-u-bansethu.html",
        ],
        "dnesniobed",
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
        "zomato_daily",
        10,
        empty_is_ok=True,
    ),
    Restaurant(
        "Na Květnici",
        [
            # Oficiální web je první volba. V některých requestech ale vrací jen
            # homepage bez cenové polední sekce, zatímco v prohlížeči je menu vidět.
            "https://www.nakvetnici.cz/cs/",
            # Záložní zrcadlo stejné polední nabídky; vrací čistý textový blok
            # s dnešním menu a cenami, bez stálého jídelního lístku.
            "https://www.dnesniobed.cz/restaurace-hospoda/nusle_na-kvetnici",
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


CONNECT_TIMEOUT = 8


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
                # (connect, read): nedostupný server (typicky DnešníOběd.cz z
                # GitHub Actions) selže do pár sekund a skript přejde na další zdroj.
                timeout=(CONNECT_TIMEOUT, timeout),
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


def parse_dnesniobed_daily(lines: list[str], max_items: int, target_day: str) -> list[MenuItem]:
    """Parser pro stránky DnešníOběd.cz.

    DnešníOběd.cz vrací menu jako čisté řádky: nadpis dne, sekce, položka,
    cena. Obecný parser občas část nabídky zahodil, protože sekční titulky
    vyhodnocoval různě podle obsahu. Tady proto používáme jednodušší a
    předvídatelnější párování: jeden nebo více řádků názvu + následující cena.
    """
    clean = [clean_line(x) for x in lines if clean_line(x)]
    if not clean:
        return []

    def norm(value: str) -> str:
        return without_diacritics(clean_line(value))

    section_headings = {
        "polevka je grunt", "dnesni delikatesy", "patecni klasika",
        "z hrnce nasich kucharskych mistru", "rizky rizky a zase rizky",
        "polevky", "poledni nabidka", "denni menu", "dnesni menu",
        "specialita tydne", "dezert", "dezerty",
        "polevka", "hlavni jidla", "hlavni jidlo", "menu", "salaty",
    }
    weekday_tabs = {"po", "ut", "st", "ct", "pa", "so", "ne"}
    stop_fragments = (
        "zobrazit vice", "odkazy", "web restaurace", "ukaz na mape", "tel:",
        "detail restaurace", "nahlasit chybu", "predstaveni", "zobrazit dalsi restaurace",
        "nacitam", "mapu", "zavrit okno", "oblibene restaurace", "recenze na google",
        "nahoru", "provozujete tuto restauraci", "aktualizovano",
    )

    start = None
    for i, line in enumerate(clean):
        if canonical_day_from_line(line) == target_day:
            start = i + 1
            break
    if start is None:
        # Pokud stránka obsahuje datovaný nadpis JINÉHO dne (např. "Pondělí 21. 9."
        # na Firmy.cz, když restaurace menu neaktualizovala), nechceme ukázat
        # staré menu jako dnešní.
        dated_other_day = re.compile(
            r"^(pondeli|utery|streda|ctvrtek|patek|sobota|nedele)\s+\d{1,2}\.\s*\d{1,2}\.",
        )
        if any(dated_other_day.match(norm(x)) for x in clean):
            return []
        # fallback pro dnešní zrcadla bez explicitního nadpisu dne
        for i, line in enumerate(clean):
            low = norm(line)
            if "poledni nabidka" in low and ("11:00" in line or "15:00" in line):
                start = i + 1
                break
    if start is None:
        return []

    items: list[MenuItem] = []
    pending_parts: list[str] = []
    # Alergeny bez závorek, jak je píšou Firmy.cz: "1, 3, 7, 9" nebo "1, 3, 7 |".
    allergen_only = re.compile(r"^[\d\s,.;|/()]*$")
    zero_price = re.compile(r"(?:^|[|\s])0\s*(?:,-|kč|czk)\s*$", re.I)
    weight_prefix = re.compile(r"^\d+(?:[,.]\d+)?\s*(?:g|kg|ml|dcl|l|ks)\b\s*", re.I)

    def flush(price_line: str) -> None:
        nonlocal pending_parts
        pending_parts = [p for p in pending_parts if not allergen_only.match(p)]
        if not pending_parts:
            return
        title = clean_line(" ".join(pending_parts))
        title = clean_line(re.sub(r"^\d{1,2}\s*[.)]\s*", "", title))  # číslování "1." z Meníčka.cz
        title = clean_line(weight_prefix.sub("", title))
        title = strip_allergens(strip_trailing_price_from_title(title))
        # Odstraň případný přilepený sekční nadpis na začátku.
        for h in sorted(section_headings, key=len, reverse=True):
            visible = h.replace("polevka", "Polévka")
            title_norm = norm(title)
            if title_norm == h:
                title = ""
                break
            if title_norm.startswith(h + " "):
                title = clean_line(title.split(" ", len(h.split()))[-1])
        if title and len(title) >= 3:
            items.append(MenuItem(title=title, price=normalize_price(price_line), section=""))
        pending_parts = []

    for raw in clean[start:]:
        line = clean_line(raw)
        low = norm(line)
        if not line:
            continue
        if canonical_day_from_line(line):
            break
        if any(stop in low for stop in stop_fragments):
            break
        if low in weekday_tabs or low in section_headings:
            # Nadpis sekce není součást názvu další položky.
            continue
        if re.fullmatch(r"\d+[,.]?\d*\s*\(?\d*\)?", line):
            continue
        if zero_price.search(line):
            # "Domácí koláč … | 0 Kč" – položka bez ceny, uzavřeme ji a zahodíme,
            # aby se nepřilepila k dalšímu jídlu.
            pending_parts = []
            continue
        if allergen_only.match(line):
            continue
        if is_price(line):
            flush(line)
            if len(items) >= max_items:
                break
            continue
        if PRICE_RE.search(line):
            title, price = extract_price(line)
            title = clean_line(title.strip(" |"))
            if title and not allergen_only.match(title):
                pending_parts.append(title)
            flush(price)
            if len(items) >= max_items:
                break
            continue
        # Profilové/obecné řádky před menu nebo po menu.
        if any(bad in low for bad in ("toggle navigation", "zobrazit vse", "pro restaurace", "vyberte si restauraci", "kliknete zde", "tabor", "nusle", "na kvetnici", "u bansethu")):
            continue
        # Název jídla, případně druhý řádek dezertu před cenou.
        pending_parts.append(line)

    return items[:max_items]


def parse_zomato_daily(lines: list[str], max_items: int, target_day: str) -> list[MenuItem]:
    """Parser pro Zomato daily_menu widget Kandelábru."""
    clean = [clean_line(x) for x in lines if clean_line(x)]
    if not clean:
        return []

    def mostly_uppercase(value: str) -> bool:
        letters = [ch for ch in value if ch.isalpha()]
        if len(letters) < 8:
            return False
        return sum(1 for ch in letters if ch.isupper()) / max(1, len(letters)) >= 0.70

    def pretty_title(value: str) -> str:
        title = strip_allergens(strip_trailing_price_from_title(value))
        title = re.sub(r"^\d+\.\s*", "", title)
        title = re.sub(r"^pol[eé]vka\s*[-–—:]\s*", "", title, flags=re.I)
        title = re.sub(r"(\d+)\s*G\b", r"\1g", title)
        title = clean_line(title)
        if mostly_uppercase(title):
            title = title.lower()
            title = re.sub(r"(\d+)g", lambda m: m.group(1) + "g", title)
            title = title[:1].upper() + title[1:] if title else title
            title = re.sub(r"^(\d+g\s+)([a-zá-ž])", lambda m: m.group(1) + m.group(2).upper(), title)
            title = re.sub(r"\bbbq\b", "BBQ", title, flags=re.I)
        return clean_line(title)

    start = None
    for i, line in enumerate(clean):
        if canonical_day_from_line(line) == target_day:
            start = i + 1
            break
    if start is None:
        return []

    items: list[MenuItem] = []
    pending_parts: list[str] = []
    for raw in clean[start:]:
        line = clean_line(raw)
        if not line:
            continue
        if canonical_day_from_line(line):
            break
        low = without_diacritics(line)
        if "zobrazit na zomatu" in low:
            break
        if low in {"restauracni pruvodce", "denni menu"}:
            continue
        if is_price(line):
            if pending_parts:
                title = pretty_title(" ".join(pending_parts))
                if title:
                    items.append(MenuItem(title=title, price=normalize_price(line), section=""))
                pending_parts = []
                if len(items) >= max_items:
                    break
            continue
        title, price = re.match(r"^(.*?)(\d{2,4}\s*(?:Kč|kč|CZK|,-))$", line).groups() if re.match(r"^(.*?)(\d{2,4}\s*(?:Kč|kč|CZK|,-))$", line) else ("", "")
        if price:
            if title:
                pending_parts.append(title)
            title = pretty_title(" ".join(pending_parts))
            if title:
                items.append(MenuItem(title=title, price=normalize_price(price), section=""))
            pending_parts = []
            if len(items) >= max_items:
                break
            continue
        pending_parts.append(line)
    return items[:max_items]


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

    def fallback_unpriced_items(source_lines: list[str]) -> list[MenuItem]:
        """Květnice: bez cenového poledního bloku raději nezobrazujeme nic.

        Řádky typu „Vepřové koleno“, „Kuřecí křidélka“ nebo „Kuřecí paličky"
        jsou položky stálého jídelního lístku, ne denní menu. Proto je jako
        fallback nepoužíváme; dashboard pak zobrazí hlášku o nedostupném menu.
        """
        return []
        bad_fragments = (
            "existuji mista", "zitra to", "krome nasich", "hokeji",
            "doma ti", "manzelka", "serial", "cas pod", "free website",
            "template", "karneval", "restaurace", "zahradka", "o-nas-foto",
            "loading", "instagram", "facebook", "rezervace", "kontakt",
        )
        food_words = (
            "polévka", "vývar", "dršťkov", "koleno", "kuřec", "hovězí",
            "vepř", "sýr", "salát", "burger", "křidél", "paličk",
            "utopenec", "hermelín", "brambor", "řízek", "guláš",
        )
        out: list[MenuItem] = []
        seen: set[str] = set()
        for raw in source_lines:
            line = strip_trailing_price_from_title(raw)
            low = norm(line)
            if not line or is_skip(line):
                continue
            if "loading" in low:
                break
            if is_stop(line):
                break
            if any(bad in low for bad in bad_fragments):
                continue
            if "..." in line or len(line) > 95 or len(line) < 4:
                continue
            if PRICE_RE.search(line):
                continue
            # Ponech jen řádky, které opravdu vypadají jako jídlo, ne jako
            # headline nebo obecný text webu.
            if not any(word in line.lower() for word in food_words):
                continue
            key = low
            if key in seen:
                continue
            seen.add(key)
            out.append(MenuItem(title=line, section=""))
            if len(out) >= min(max_items, 6):
                break
        return out

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
        return fallback_unpriced_items(clean)

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
    pending_title = ""

    def looks_like_kvetnice_note(line: str) -> bool:
        """Pozná doplňující popis položky Květnice.

        Web Květnice posílá strukturu: název → cena → popis → další název.
        Starší parser bral popis jako začátek další položky a řádky se pak
        slepovaly. Poznámky typicky začínají malým písmenem nebo spojkami typu
        „s/se“, „vařené“, „sypaná“.
        """
        t = clean_line(line)
        if not t or PRICE_RE.search(t) or is_price(t):
            return False
        low = norm(t)
        if is_stop(t) or is_skip(t):
            return False
        if low in {"polevky", "poledni nabidka", "dnesni menu", "specialita tydne"}:
            return False
        note_starts = (
            "s ", "se ", "v ", "ve ", "na ", "podavane", "servirovane",
            "varene", "varenymi", "sypana", "sypane", "se skorici",
            "classic", "neperliva", "jemne perliva", "pomerancova", "citronova",
        )
        return t[:1].islower() or low.startswith(note_starts)

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
        # Kompozitní „Dnešní menu“ na webu rozepisuje již uvedené položky,
        # proto ho v TV přehledu raději nepřidáváme jako samostatné jídlo.
        if low_title == "dnesni menu":
            return
        items.append(MenuItem(title=title, price=normalize_price(price), note=note, section=forced_section or section.title()))

    # Květnice vrací strukturu název → cena → volitelný popis. Popis patří
    # k právě přidané položce, ne k další položce.
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
            pending_title = ""
            i += 1
            continue
        if low == "polevky":
            section = "Polévky"
            pending_title = ""
            i += 1
            continue
        if low == "specialita tydne":
            section = "Specialita týdne"
            pending_title = ""
            i += 1
            continue
        if low.startswith("dnesni menu") and not PRICE_RE.search(raw):
            section = "Dnešní menu"
            pending_title = "Dnešní menu"
            i += 1
            continue

        if is_price(raw):
            if pending_title:
                add_item(pending_title, raw)
                pending_title = ""
            i += 1
            if len(items) >= max_items:
                break
            continue

        title, price = extract_price(raw)
        if price:
            add_item(title, price)
            pending_title = ""
            if len(items) >= max_items:
                break
            i += 1
            continue

        # Popis po ceně připoj k poslední položce jako note. Tím se zabrání
        # slepování „s masem... Hráškový krém“ do jednoho názvu.
        if not pending_title and items and not items[-1].note and looks_like_kvetnice_note(raw):
            items[-1].note = raw
            i += 1
            continue

        # Řádek bez ceny je název položky, který má typicky cenu na dalším řádku.
        # Když se název výjimečně zlomí před cenou, spojíme ho.
        if pending_title:
            pending_title = clean_line(f"{pending_title} {raw}")
        else:
            pending_title = raw
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
    if cleaned:
        return cleaned[:max_items]
    return fallback_unpriced_items(clean)[:max_items]

PALOUCEK_WEIGHT_RE = re.compile(r"^\d+(?:[,.]\d+)?\s*(?:g|kg|ml|dcl|l|ks)\b\s*", re.I)


def paloucek_raw_lines(page_html: str) -> list[str]:
    """Textové řádky polední sekce nového webu restpaloucek.cz.

    Od září 2026 je web jednostránkový a polední nabídka je v sekci #poledni
    na homepage. Obecný visible_lines() tu nestačí: bere jen první <main>/
    <article> a JUNK filtr by vyhodil i část textu. Gramáž bývá v samostatném
    <span> hned před názvem ("350gŠpagety…"), proto ji oddělujeme.
    """
    soup = BeautifulSoup(page_html, "html.parser")
    for tag in soup(["script", "style", "noscript", "svg", "iframe"]):
        tag.decompose()

    root = None
    anchor = soup.find(id="poledni")
    if anchor is not None:
        # id může být na prázdné kotvě; v tom případě vezmeme nejbližšího
        # rodiče, který obsahuje celou nabídku.
        node = anchor
        while node is not None and "doporuč" not in node.get_text(" ").lower():
            node = node.parent
        root = node
    if root is None:
        root = soup.body or soup

    lines: list[str] = []
    prev = ""
    for part in root.get_text("\n").splitlines():
        line = clean_line(part)
        if not line:
            continue
        # "350gŠpagety" / "3,3 dclGulášová" -> "350g Špagety" / "3,3 dcl Gulášová"
        line = re.sub(r"^(\d+(?:[,.]\d+)?\s*(?:g|kg|ml|dcl|l|ks))(?=[^\W\d_])", r"\1 ", line)
        if line == prev:
            continue
        lines.append(line)
        prev = line
    return lines


def parse_paloucek(lines: list[str], max_items: int, target_day: str) -> list[MenuItem]:
    """Palouček: bereme DNES DOPORUČUJEME + POLEDNÍ NABÍDKA (+ DEZERT).

    Polévky a MENU I./II. (polévka + jídlo za jednu cenu) v dashboardu
    nechceme, stejně jako v dřívějších verzích. Gramáž nezobrazujeme, aby
    karta vypadala stejně jako u ostatních restaurací.
    """
    # Kontrola dne: web píše "Denní menu — Středa". Když nadpis patří jinému
    # dni, jde o neaktualizovanou nabídku a nechceme ji ukázat jako dnešní.
    for line in lines:
        m = re.match(r"^denn[íi]\s+menu\s*[—–:\-]\s*(.+)$", line.strip(), re.I)
        if m:
            day = canonical_day_from_line(m.group(1))
            if day and day != target_day:
                return []
            break

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
        if any(stop in low for stop in (
            "se každý den mění", "aktuální menu", "sdělíme telefonicky",
            "stálý", "jídelní lístek", "nápojový", "aktuality", "kudy k nám",
            "rezervace", "kontakt", "copyright",
        )):
            break
        if low in {"polévka", "polévky", "menu i.", "menu ii.", "menu iii.", "polévka v ceně menu"}:
            continue
        # Samostatný řádek s gramáží zahodíme, gramáž na začátku názvu odřízneme.
        if PALOUCEK_WEIGHT_RE.fullmatch(line):
            continue
        line = clean_line(PALOUCEK_WEIGHT_RE.sub("", line))
        if line:
            compact.append(line)
    return parse_items_from_lines(compact, max_items)


PARSERS: dict[str, Callable[[list[str], int, str], list[MenuItem]]] = {
    "generic": parse_generic,
    "weekly": parse_weekly,
    "palatino": parse_palatino,
    "klika": parse_klika,
    "external_daily": parse_external_daily,
    "dnesniobed": parse_dnesniobed_daily,
    "zomato_daily": parse_zomato_daily,
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
    if not name.startswith("U Bansethů"):
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
            if cfg.parser == "paloucek":
                lines = paloucek_raw_lines(page)
                items = parser(lines, cfg.max_items, target_day)
            elif cfg.parser == "kvetnice":
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

# ---------------------------------------------------------------------------
# v7.0: druhá obrazovka pro TV – počasí, svátek a odjezdy MHD
# ---------------------------------------------------------------------------
# Obrazovky se střídají přímo v prohlížeči televize (JavaScript), počasí a
# odjezdy se načítají živě z API, takže fungují i odpoledne, kdy GitHub
# workflow už dashboard negeneruje. JavaScript je záměrně ve stylu ES5
# (var, function, XMLHttpRequest), aby běžel i ve starším prohlížeči Samsung.

OFFICE_LAT = 50.0571
OFFICE_LON = 14.4330

# Jmeniny: data z balíčku namedays-cs (MIT, Roman Ožana), klíč MM-DD.
NAMEDAYS_CS = json.loads('{"01-02":["Karina"],"01-03":["Radmila","Radomil"],"01-04":["Diana"],"01-05":["Dalimil"],"01-06":["Kašpar","Melichar","Baltazar"],"01-07":["Vilma"],"01-08":["Čestmír"],"01-09":["Vladan","Valtr"],"01-10":["Břetislav"],"01-11":["Bohdana"],"01-12":["Pravoslav"],"01-13":["Edita"],"01-14":["Radovan"],"01-15":["Alice"],"01-16":["Ctirad"],"01-17":["Drahoslav"],"01-18":["Vladislav","Vladislava"],"01-19":["Doubravka"],"01-20":["Ilona","Sebastián"],"01-21":["Běla"],"01-22":["Slavomír","Slavomíra"],"01-23":["Zdeněk"],"01-24":["Milena"],"01-25":["Miloš"],"01-26":["Zora"],"01-27":["Ingrid"],"01-28":["Otýlie"],"01-29":["Zdislava"],"01-30":["Robin","Erna"],"01-31":["Marika","Spytihněv"],"02-01":["Hynek"],"02-02":["Nela","Hromnice"],"02-03":["Blažej"],"02-04":["Jarmila"],"02-05":["Dobromila"],"02-06":["Vanda"],"02-07":["Veronika"],"02-08":["Milada"],"02-09":["Apolena"],"02-10":["Mojmír"],"02-11":["Božena"],"02-12":["Slavěna","Slávka"],"02-13":["Věnceslav","Věnceslava"],"02-14":["Valentýn","Valentýna"],"02-15":["Jiřina"],"02-16":["Ljuba"],"02-17":["Miloslava"],"02-18":["Gizela"],"02-19":["Patrik"],"02-20":["Oldřich"],"02-21":["Lenka","Eleonora"],"02-22":["Petr"],"02-23":["Svatopluk"],"02-24":["Matěj","Matyáš"],"02-25":["Liliana"],"02-26":["Dorota"],"02-27":["Alexandr"],"02-28":["Lumír"],"02-29":["Horymír"],"03-01":["Bedřich","Bedřiška"],"03-02":["Anežka"],"03-03":["Kamil","Kunhuta"],"03-04":["Stela"],"03-05":["Kazimír"],"03-06":["Miroslav"],"03-07":["Tomáš"],"03-08":["Gabriela","Zoltán"],"03-09":["Františka"],"03-10":["Viktorie"],"03-11":["Anděla"],"03-12":["Řehoř"],"03-13":["Růžena"],"03-14":["Rút","Matylda"],"03-15":["Ida"],"03-16":["Elena","Herbert"],"03-17":["Vlastimil","Vlastimila"],"03-18":["Eduard"],"03-19":["Josef","Josefa"],"03-20":["Světlana"],"03-21":["Radek"],"03-22":["Leona","Leontina","Lea"],"03-23":["Ivona"],"03-24":["Gabriel"],"03-25":["Marián"],"03-26":["Emanuel"],"03-27":["Dita"],"03-28":["Soňa"],"03-29":["Taťána"],"03-30":["Arnošt","Ernest"],"03-31":["Kvido"],"04-01":["Hugo"],"04-02":["Erika"],"04-03":["Richard"],"04-04":["Ivana"],"04-05":["Miroslava","Mirka"],"04-06":["Vendula","Venuše"],"04-07":["Heřman","Hermína"],"04-08":["Ema"],"04-09":["Dušan"],"04-10":["Darja"],"04-11":["Izabela"],"04-12":["Julius"],"04-13":["Aleš"],"04-14":["Vincenc"],"04-15":["Anastázie"],"04-16":["Irena","Bernadeta"],"04-17":["Rudolf"],"04-18":["Valérie"],"04-19":["Rostislav"],"04-20":["Marcela"],"04-21":["Alexandra"],"04-22":["Evženie"],"04-23":["Vojtěch"],"04-24":["Jiří"],"04-25":["Marek"],"04-26":["Oto"],"04-27":["Jaroslav"],"04-28":["Vlastislav"],"04-29":["Robert"],"04-30":["Blahoslav"],"05-02":["Zikmund"],"05-03":["Alexej","Alex"],"05-04":["Květoslav"],"05-05":["Klaudie"],"05-06":["Radoslav"],"05-07":["Stanislav"],"05-09":["Ctibor"],"05-10":["Blažena"],"05-11":["Svatava"],"05-12":["Pankrác"],"05-13":["Servác"],"05-14":["Bonifác"],"05-15":["Žofie","Sofie"],"05-16":["Přemysl"],"05-17":["Aneta"],"05-18":["Nataša"],"05-19":["Ivo"],"05-20":["Zbyšek"],"05-21":["Monika"],"05-22":["Emil"],"05-23":["Vladimír","Vladimíra"],"05-24":["Jana","Vanesa"],"05-25":["Viola"],"05-26":["Filip"],"05-27":["Valdemar"],"05-28":["Vilém"],"05-29":["Maxmilián","Maxim"],"05-30":["Ferdinand"],"05-31":["Kamila"],"06-01":["Laura"],"06-02":["Jarmil"],"06-03":["Tamara","Kevin"],"06-04":["Dalibor"],"06-05":["Dobroslav","Dobroslava"],"06-06":["Norbert"],"06-07":["Iveta","Slavoj"],"06-08":["Medard"],"06-09":["Stanislava"],"06-10":["Gita","Margita"],"06-11":["Bruno"],"06-12":["Antonie"],"06-13":["Antonín"],"06-14":["Roland","Herta"],"06-15":["Vít"],"06-16":["Zbyněk"],"06-17":["Adolf"],"06-18":["Milan","Milana"],"06-19":["Leoš","Leo"],"06-20":["Květa","Květuše"],"06-21":["Alois","Aloisie"],"06-22":["Pavla"],"06-23":["Zdeňka"],"06-24":["Jan"],"06-25":["Ivan"],"06-26":["Adriana","Adrian"],"06-27":["Ladislav","Ladislava"],"06-28":["Lubomír"],"06-29":["Petr","Pavel"],"06-30":["Šárka"],"07-01":["Jaroslava"],"07-02":["Patricie"],"07-03":["Radomír","Radomíra"],"07-04":["Prokop"],"07-05":["Cyril","Metoděj"],"07-07":["Bohuslava"],"07-08":["Nora"],"07-09":["Drahoslava","Drahuše"],"07-10":["Libuše","Amálie"],"07-11":["Olga","Helga"],"07-12":["Bořek"],"07-13":["Markéta"],"07-14":["Karolína"],"07-15":["Jindřich"],"07-16":["Luboš"],"07-17":["Martina"],"07-18":["Drahomíra","Drahomír"],"07-19":["Čeněk"],"07-20":["Ilja"],"07-21":["Vítězslav","Vítězslava"],"07-22":["Magdaléna","Magda"],"07-23":["Libor"],"07-24":["Kristýna"],"07-25":["Jakub"],"07-26":["Anna","Anita"],"07-27":["Věroslav"],"07-28":["Viktor","Alina"],"07-29":["Marta"],"07-30":["Bořivoj"],"07-31":["Ignác"],"08-01":["Oskar"],"08-02":["Gustav"],"08-03":["Miluše"],"08-04":["Dominik","Dominika"],"08-05":["Kristián"],"08-06":["Oldřiška"],"08-07":["Lada"],"08-08":["Soběslav"],"08-09":["Roman"],"08-10":["Vavřinec"],"08-11":["Zuzana"],"08-12":["Klára"],"08-13":["Alena"],"08-14":["Alan"],"08-15":["Hana"],"08-16":["Jáchym"],"08-17":["Petra"],"08-18":["Helena","Jelena"],"08-19":["Ludvík"],"08-20":["Bernard"],"08-21":["Johana"],"08-22":["Bohuslav"],"08-23":["Sandra"],"08-24":["Bartoloměj"],"08-25":["Radim"],"08-26":["Luděk"],"08-27":["Otakar"],"08-28":["Augustýn"],"08-29":["Evelína"],"08-30":["Vladěna"],"08-31":["Pavlína"],"09-01":["Linda","Samuel"],"09-02":["Adéla"],"09-03":["Bronislav","Bronislava"],"09-04":["Jindřiška","Rozálie"],"09-05":["Boris"],"09-06":["Boleslav"],"09-07":["Regína"],"09-08":["Mariana"],"09-09":["Daniela"],"09-10":["Irma"],"09-11":["Denisa","Denis"],"09-12":["Marie"],"09-13":["Lubor"],"09-14":["Radka"],"09-15":["Jolana"],"09-16":["Ludmila","Lidmila"],"09-17":["Naděžda","Naďa"],"09-18":["Kryštof"],"09-19":["Zita"],"09-20":["Oleg"],"09-21":["Matouš"],"09-22":["Darina"],"09-23":["Berta"],"09-24":["Jaromír","Jaromíra"],"09-25":["Zlata","Zlatuše"],"09-26":["Andrea"],"09-27":["Jonáš"],"09-28":["Václav","Václava"],"09-29":["Michal","Michael"],"09-30":["Jeroným","Ráchel"],"10-01":["Igor"],"10-02":["Olívie","Oliver"],"10-03":["Bohumil"],"10-04":["František"],"10-05":["Eliška"],"10-06":["Hanuš"],"10-07":["Justýna"],"10-08":["Věra"],"10-09":["Štefan","Sára"],"10-10":["Marina"],"10-11":["Andrej"],"10-12":["Marcel"],"10-13":["Renáta"],"10-14":["Agáta"],"10-15":["Tereza","Terezie"],"10-16":["Havel","Galina"],"10-17":["Hedvika"],"10-18":["Lukáš"],"10-19":["Michaela","Michala"],"10-20":["Vendelín"],"10-21":["Brigita"],"10-22":["Sabina"],"10-23":["Teodor"],"10-24":["Nina"],"10-25":["Beáta"],"10-26":["Erik"],"10-27":["Šarlota","Zoe"],"10-28":["Jidáš","Alfréd"],"10-29":["Silvie","Sylva"],"10-30":["Tadeáš"],"10-31":["Štěpánka"],"11-01":["Felix"],"11-02":["Tobiáš"],"11-03":["Hubert"],"11-04":["Karel","Karla"],"11-05":["Miriam"],"11-06":["Liběna","Leonard"],"11-07":["Saskie"],"11-08":["Bohumír","Bohumíra"],"11-09":["Bohdan"],"11-10":["Evžen"],"11-11":["Martin"],"11-12":["Benedikt"],"11-13":["Tibor"],"11-14":["Sáva"],"11-15":["Leopold"],"11-16":["Otmar"],"11-17":["Mahulena","Gertruda"],"11-18":["Romana"],"11-19":["Alžběta"],"11-20":["Nikola"],"11-21":["Albert"],"11-22":["Cecílie"],"11-23":["Klement"],"11-24":["Emílie"],"11-25":["Kateřina"],"11-26":["Artur"],"11-27":["Xenie"],"11-28":["René"],"11-29":["Zina"],"11-30":["Ondřej"],"12-01":["Iva"],"12-02":["Blanka"],"12-03":["Svatoslav"],"12-04":["Barbora"],"12-05":["Jitka"],"12-06":["Mikuláš"],"12-07":["Ambrož","Benjamín"],"12-08":["Květoslava"],"12-09":["Vratislav"],"12-10":["Julie"],"12-11":["Dana","Danuše"],"12-12":["Simona"],"12-13":["Lucie"],"12-14":["Lýdie"],"12-15":["Radana","Radan"],"12-16":["Albína"],"12-17":["Daniel"],"12-18":["Miloslav"],"12-19":["Ester"],"12-20":["Dagmar"],"12-21":["Natálie"],"12-22":["Šimon"],"12-23":["Vlasta"],"12-24":["Adam","Eva"],"12-26":["Štěpán"],"12-27":["Žaneta"],"12-28":["Bohumila"],"12-29":["Judita"],"12-30":["David"],"12-31":["Silvestr"]}')


DEFAULT_SCHEDULE = "10:30=20/60,13:00=60/20,14:00=15/60"


def parse_rotation_schedule(value: str) -> list[dict]:
    """"10:30=20/60,13:00=60/20,14:00=15/60" -> fáze střídání obrazovek.

    Každá fáze platí DO uvedeného času: menu svítí první číslo sekund,
    informace druhé. Menu 0 = v té fázi jen informace. Po poslední fázi
    televize ukazuje už jen informace.
    """
    phases: list[dict] = []
    for part in (value or "").split(","):
        part = part.strip()
        if not part:
            continue
        m = re.fullmatch(r"(\d{1,2}):(\d{2})\s*=\s*(\d+)\s*/\s*(\d+)", part)
        if not m:
            raise ValueError(f"Neplatná fáze rozvrhu: {part!r} (očekávám např. 10:30=20/60)")
        h, mi, menu_s, info_s = (int(x) for x in m.groups())
        phases.append({"until": h * 60 + mi, "menu": menu_s, "info": max(5, info_s)})
    phases.sort(key=lambda x: x["until"])
    return phases


def info_screen_config(args) -> dict:
    stops = [s.strip() for s in (args.stops or "").split(",") if s.strip()]
    schedule = parse_rotation_schedule(args.schedule)
    return {
        "golemioKey": args.golemio_key or "",
        "stops": stops,
        "stopLabel": " · ".join(stops),
        "walkMinutes": max(0, args.walk_minutes),
        "lat": args.lat,
        "lon": args.lon,
        # Fáze dne: do daného času (minuty od půlnoci) svítí menu X s a info Y s.
        # Po poslední fázi už jen informační obrazovka.
        "schedule": schedule,
    }


INFO_CSS = """
.screen { display: none; opacity: 1; -webkit-transition: opacity 0.7s ease; transition: opacity 0.7s ease; }
.screen.active { display: block; }
.screen.faded { opacity: 0; }
.clock { color: #171412; font-size: 30px; font-weight: 900; letter-spacing: -0.5px; margin-left: 14px; }
/* Velikosti v kartách jsou v em a základ se odvozuje od výšky obrazovky,
   takže obrazovka vypadá stejně na 720p i 1080p televizi. */
.info-grid { display: block; width: 100%; height: calc(100vh - 58px); font-size: 0; }
.info-col { display: inline-block; vertical-align: top; height: 100%; font-size: 2.3vh; }
.info-left { width: 42.5%; margin-right: 0.75%; }
.info-right { width: 56.75%; }
.info-card {
  display: block; width: 100%; padding: 0.75em 1em 0.6em; background: #fffdf8;
  border: 1px solid #d8cdbc; border-radius: 13px; overflow: hidden; margin-bottom: 7px;
}
.info-card header {
  display: table; width: 100%; padding-bottom: 0.35em; margin-bottom: 0.5em; border-bottom: 2px solid #e4d8c7;
}
.info-card header h2, .info-card header .src { display: table-cell; vertical-align: baseline; }
.info-card header h2 { font-size: 1.3em; }
.info-card header .src { color: #6c655d; font-size: 0.72em; text-align: right; white-space: nowrap; }
.weather-card { height: calc((100vh - 72px) * 0.64); }
.nameday-card { height: calc((100vh - 72px) * 0.36); margin-bottom: 0; }
.transit-card { height: calc(100vh - 65px); margin-bottom: 0; }

.wx-now { display: table; width: 100%; }
.wx-now > div { display: table-cell; vertical-align: middle; }
.wx-icon { width: 5.6em; }
.wx-icon svg { width: 5.4em; height: 5.4em; display: block; }
.wx-temp { font-size: 4.2em; font-weight: 900; letter-spacing: -0.03em; line-height: 1; padding: 0 0.2em 0 0.08em; white-space: nowrap; }
.wx-desc { font-size: 1.45em; font-weight: 700; line-height: 1.15; }
.wx-sub { color: #625b52; font-size: 0.88em; margin-top: 0.25em; line-height: 1.35; }
.wx-hours { display: table; width: 100%; table-layout: fixed; margin-top: 0.7em; border-top: 1px solid #eadfce; padding-top: 0.5em; }
.wx-hour { display: table-cell; text-align: center; vertical-align: top; }
.wx-hour .h { color: #625b52; font-size: 0.82em; font-weight: 700; }
.wx-hour svg { width: 2.2em; height: 2.2em; display: block; margin: 0.15em auto 0.1em; }
.wx-hour .t { font-size: 1.1em; font-weight: 900; }
.wx-hour .p { color: #2f6ea5; font-size: 0.78em; font-weight: 700; min-height: 1em; }
.wx-tip { margin-top: 0.6em; padding: 0.5em 0.65em; background: #f6efe4; border-radius: 9px; font-size: 1em; font-weight: 700; line-height: 1.25; }
.wx-tip.rain { background: #e3eef8; color: #1d4f7a; }
.wx-tomorrow { display: table; width: 100%; margin-top: 0.6em; padding-top: 0.5em; border-top: 1px solid #eadfce; }
.wx-tomorrow > div { display: table-cell; vertical-align: middle; }
.wx-tomorrow svg { width: 2.4em; height: 2.4em; display: block; }
.wx-tomorrow .lbl { color: #625b52; font-size: 0.82em; font-weight: 700; text-transform: uppercase; letter-spacing: 0.04em; }
.wx-tomorrow .val { font-size: 1.1em; font-weight: 700; padding-left: 0.5em; }

.nd-today { font-size: 2.5em; font-weight: 900; letter-spacing: -0.02em; line-height: 1.05; color: #8b3f1d; }
.nd-label { color: #625b52; font-size: 0.82em; font-weight: 700; text-transform: uppercase; letter-spacing: 0.04em; }
.nd-tomorrow { font-size: 1.05em; margin-top: 0.35em; }
.nd-holiday { font-size: 0.92em; margin-top: 0.6em; padding-top: 0.5em; border-top: 1px solid #eadfce; line-height: 1.3; }
.nd-holiday b { color: #8b3f1d; }

.dep-row { display: table; width: 100%; padding: 0.5em 0; border-bottom: 1px solid #eadfce; }
.dep-row:last-child { border-bottom: 0; }
.dep-row > div { display: table-cell; vertical-align: middle; }
.dep-badge-cell { width: 4.3em; }
.dep-badge {
  display: inline-block; min-width: 2.3em; padding: 0.22em 0.3em; border-radius: 8px; text-align: center;
  color: #fff; font-size: 1.45em; font-weight: 900; line-height: 1;
}
.dep-head { font-size: 1.45em; font-weight: 700; padding-left: 0.2em; line-height: 1.1; }
.dep-head .plat { color: #857c72; font-size: 0.55em; font-weight: 400; margin-left: 0.4em; }
.dep-times { text-align: right; white-space: nowrap; font-size: 1.6em; font-weight: 900; }
.dep-times span { color: #857c72; font-size: 0.7em; font-weight: 700; margin-left: 0.55em; }
.dep-times small { color: #625b52; font-size: 0.55em; font-weight: 700; margin-left: 0.15em; }
.dep-msg { color: #625b52; font-size: 1.1em; line-height: 1.3; padding: 1em 0; }
.dep-alert { margin-top: 0.6em; padding: 0.5em 0.65em; background: #fbe9e3; color: #7a2a12; border-radius: 9px; font-size: 0.9em; line-height: 1.3; }
.dep-foot { color: #857c72; font-size: 0.72em; margin-top: 0.5em; }
"""


INFO_HTML = """
<div id="screen-info" class="screen">
  <div class="topbar">
    <div><h1>Dnes v kanceláři</h1><div class="subtitle" id="info-date"></div></div>
    <div><span class="timestamp" id="info-updated"></span><span class="clock" id="info-clock"></span></div>
  </div>
  <div class="info-grid">
    <div class="info-col info-left">
      <section class="info-card weather-card">
        <header><h2>Počasí</h2><span class="src">Praha 4 – Nusle · Open-Meteo</span></header>
        <div id="wx-body"><div class="dep-msg">Načítám počasí…</div></div>
      </section>
      <section class="info-card nameday-card">
        <header><h2>Svátek</h2><span class="src" id="nd-date"></span></header>
        <div id="nd-body"></div>
      </section>
    </div>
    <div class="info-col info-right">
      <section class="info-card transit-card">
        <header><h2>Odjezdy MHD</h2><span class="src" id="dep-stop"></span></header>
        <div id="dep-body"><div class="dep-msg">Načítám odjezdy…</div></div>
      </section>
    </div>
  </div>
</div>
"""


INFO_JS = r"""
(function () {
  var CFG = __CFG__;
  var MENU_DATE = __MENU_DATE__;
  var NAMEDAYS = __NAMEDAYS__;

  var DAYS = ["neděle", "pondělí", "úterý", "středa", "čtvrtek", "pátek", "sobota"];
  var DAYS_TITLE = ["Neděle", "Pondělí", "Úterý", "Středa", "Čtvrtek", "Pátek", "Sobota"];
  var MONTHS_GEN = ["ledna", "února", "března", "dubna", "května", "června", "července",
                    "srpna", "září", "října", "listopadu", "prosince"];

  function $(id) { return document.getElementById(id); }
  function pad(n) { return (n < 10 ? "0" : "") + n; }
  function esc(s) {
    return String(s == null ? "" : s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
  }
  function isoDate(d) { return d.getFullYear() + "-" + pad(d.getMonth() + 1) + "-" + pad(d.getDate()); }
  function hhmm(d) { return pad(d.getHours()) + ":" + pad(d.getMinutes()); }
  function addDays(d, n) { var x = new Date(d.getFullYear(), d.getMonth(), d.getDate()); x.setDate(x.getDate() + n); return x; }

  // ISO čas s posunem ("2026-09-23T13:40:00+02:00") – vlastní parser, starší TV prohlížeče to neumí spolehlivě.
  function parseIsoOffset(s) {
    var m = /^(\d{4})-(\d\d)-(\d\d)T(\d\d):(\d\d)(?::(\d\d)(?:\.\d+)?)?(Z|([+-])(\d\d):?(\d\d))?$/.exec(s || "");
    if (!m) { return null; }
    var t = Date.UTC(+m[1], +m[2] - 1, +m[3], +m[4], +m[5], +(m[6] || 0));
    if (m[7] && m[7] !== "Z") {
      var off = (+m[9] * 60 + +m[10]) * 60000;
      t = m[8] === "+" ? t - off : t + off;
    } else if (!m[7]) {
      return new Date(+m[1], +m[2] - 1, +m[3], +m[4], +m[5], +(m[6] || 0)).getTime();
    }
    return t;
  }

  function getJSON(url, headers, ok, fail) {
    try {
      var x = new XMLHttpRequest();
      x.open("GET", url, true);
      x.timeout = 20000;
      for (var k in headers) { if (headers.hasOwnProperty(k)) { x.setRequestHeader(k, headers[k]); } }
      x.onreadystatechange = function () {
        if (x.readyState !== 4) { return; }
        if (x.status === 200) {
          var data;
          try { data = JSON.parse(x.responseText); } catch (e) { fail("neplatná odpověď"); return; }
          ok(data);
        } else {
          fail("HTTP " + x.status);
        }
      };
      x.ontimeout = function () { fail("timeout"); };
      x.send();
    } catch (e) { fail(String(e)); }
  }

  // ---------------------------------------------------------------- střídání obrazovek
  var screens = { menu: $("screen-menu"), info: $("screen-info") };
  var current = "menu";

  // Aktuální fáze rozvrhu; null = jen informační obrazovka.
  function currentPhase() {
    var now = new Date();
    if (!MENU_DATE || MENU_DATE !== isoDate(now)) { return null; }
    var mins = now.getHours() * 60 + now.getMinutes();
    for (var i = 0; i < CFG.schedule.length; i++) {
      if (mins < CFG.schedule[i].until) {
        return CFG.schedule[i].menu > 0 ? CFG.schedule[i] : null;
      }
    }
    return null;
  }
  var FADE_MS = 700;
  function show(name, animate) {
    var prev = current;
    current = name;
    if (!animate || prev === name) {
      screens.menu.className = "screen" + (name === "menu" ? " active" : "");
      screens.info.className = "screen" + (name === "info" ? " active" : "");
      return;
    }
    // Plynulé zhasnutí staré obrazovky a rozsvícení nové.
    screens[prev].className = "screen active faded";
    setTimeout(function () {
      screens[prev].className = "screen";
      var el = screens[name];
      el.className = "screen active faded";
      void el.offsetWidth; // vynutí překreslení, aby přechod proběhl
      el.className = "screen active";
    }, FADE_MS);
  }
  function cycle() {
    var ph = currentPhase(), next, secs;
    if (!ph) { next = "info"; secs = 30; }
    else {
      next = current === "menu" ? "info" : "menu";
      secs = next === "menu" ? ph.menu : ph.info;
    }
    show(next, true);
    setTimeout(cycle, secs * 1000);
  }

  // ---------------------------------------------------------------- hodiny a datum
  function tickClock() {
    var now = new Date();
    $("info-clock").innerHTML = hhmm(now);
    $("info-date").innerHTML = esc(DAYS_TITLE[now.getDay()] + " " + now.getDate() + ". " + MONTHS_GEN[now.getMonth()]);
  }

  // ---------------------------------------------------------------- svátky
  function easterSunday(y) {
    var a = y % 19, b = Math.floor(y / 100), c = y % 100, d = Math.floor(b / 4), e = b % 4;
    var f = Math.floor((b + 8) / 25), g = Math.floor((b - f + 1) / 3);
    var h = (19 * a + b - d - g + 15) % 30, i = Math.floor(c / 4), k = c % 4;
    var l = (32 + 2 * e + 2 * i - h - k) % 7, m = Math.floor((a + 11 * h + 22 * l) / 451);
    var month = Math.floor((h + l - 7 * m + 114) / 31), day = ((h + l - 7 * m + 114) % 31) + 1;
    return new Date(y, month - 1, day);
  }
  var FIXED_HOLIDAYS = {
    "01-01": "Den obnovy samostatného českého státu, Nový rok",
    "05-01": "Svátek práce",
    "05-08": "Den vítězství",
    "07-05": "Den slovanských věrozvěstů Cyrila a Metoděje",
    "07-06": "Den upálení mistra Jana Husa",
    "09-28": "Den české státnosti",
    "10-28": "Den vzniku samostatného československého státu",
    "11-17": "Den boje za svobodu a demokracii",
    "12-24": "Štědrý den",
    "12-25": "1. svátek vánoční",
    "12-26": "2. svátek vánoční"
  };
  function mmdd(d) { return pad(d.getMonth() + 1) + "-" + pad(d.getDate()); }
  function holidayName(d) {
    var e = easterSunday(d.getFullYear());
    var gf = addDays(e, -2), em = addDays(e, 1);
    if (isoDate(d) === isoDate(gf)) { return "Velký pátek"; }
    if (isoDate(d) === isoDate(em)) { return "Velikonoční pondělí"; }
    return FIXED_HOLIDAYS[mmdd(d)] || "";
  }
  function namesFor(d) { return NAMEDAYS[mmdd(d)] || []; }
  function joinNames(list) {
    if (list.length <= 1) { return list.join(""); }
    return list.slice(0, -1).join(", ") + " a " + list[list.length - 1];
  }
  function renderNameday() {
    var today = new Date(), tomorrow = addDays(today, 1);
    var t = namesFor(today), z = namesFor(tomorrow), hol = holidayName(today);
    var html = "";
    html += "<div class='nd-label'>Dnes má svátek</div>";
    html += "<div class='nd-today'>" + esc(t.length ? joinNames(t) : (hol || "—")) + "</div>";
    html += "<div class='nd-tomorrow'>Zítra: <b>" + esc(z.length ? joinNames(z) : (holidayName(tomorrow) || "—")) + "</b></div>";
    if (hol) {
      html += "<div class='nd-holiday'>Dnes je státní svátek: <b>" + esc(hol) + "</b></div>";
    } else {
      for (var n = 1; n <= 366; n++) {
        var d = addDays(today, n), name = holidayName(d);
        if (name) {
          var when = n === 1 ? "zítra" : "za " + n + " " + (n < 5 ? "dny" : "dní");
          html += "<div class='nd-holiday'>Nejbližší státní svátek: <b>" + esc(name) + "</b><br>" +
                  esc(DAYS[d.getDay()] + " " + d.getDate() + ". " + (d.getMonth() + 1) + ". · " + when) + "</div>";
          break;
        }
      }
    }
    $("nd-body").innerHTML = html;
    $("nd-date").innerHTML = esc(today.getDate() + ". " + MONTHS_GEN[today.getMonth()]);
  }

  // ---------------------------------------------------------------- počasí (Open-Meteo, bez klíče)
  var WMO = {
    0: ["Jasno", "sun"], 1: ["Skoro jasno", "sun"], 2: ["Polojasno", "part"], 3: ["Zataženo", "cloud"],
    45: ["Mlha", "fog"], 48: ["Mlha s námrazou", "fog"],
    51: ["Slabé mrholení", "drizzle"], 53: ["Mrholení", "drizzle"], 55: ["Silné mrholení", "drizzle"],
    56: ["Mrznoucí mrholení", "drizzle"], 57: ["Mrznoucí mrholení", "drizzle"],
    61: ["Slabý déšť", "rain"], 63: ["Déšť", "rain"], 65: ["Silný déšť", "rain"],
    66: ["Mrznoucí déšť", "rain"], 67: ["Mrznoucí déšť", "rain"],
    71: ["Slabé sněžení", "snow"], 73: ["Sněžení", "snow"], 75: ["Silné sněžení", "snow"], 77: ["Sněhová zrna", "snow"],
    80: ["Slabé přeháňky", "rain"], 81: ["Přeháňky", "rain"], 82: ["Silné přeháňky", "rain"],
    85: ["Sněhové přeháňky", "snow"], 86: ["Silné sněhové přeháňky", "snow"],
    95: ["Bouřka", "storm"], 96: ["Bouřka s kroupami", "storm"], 99: ["Silná bouřka s kroupami", "storm"]
  };
  function wmo(code) { return WMO[code] || ["", "cloud"]; }

  function icon(kind, isDay) {
    var sun = "<circle cx='32' cy='32' r='11' fill='#f2b01e'/>" +
      "<g stroke='#f2b01e' stroke-width='4' stroke-linecap='round'>" +
      "<line x1='32' y1='6' x2='32' y2='13'/><line x1='32' y1='51' x2='32' y2='58'/>" +
      "<line x1='6' y1='32' x2='13' y2='32'/><line x1='51' y1='32' x2='58' y2='32'/>" +
      "<line x1='13.6' y1='13.6' x2='18.5' y2='18.5'/><line x1='45.5' y1='45.5' x2='50.4' y2='50.4'/>" +
      "<line x1='13.6' y1='50.4' x2='18.5' y2='45.5'/><line x1='45.5' y1='18.5' x2='50.4' y2='13.6'/></g>";
    var moon = "<path d='M40 10a22 22 0 1 0 14 34A18 18 0 0 1 40 10z' fill='#8f9bb3'/>";
    var cloud = function (fill, dy) {
      dy = dy || 0;
      return "<path transform='translate(0," + dy + ")' d='M18 46h28a10 10 0 0 0 0-20 14 14 0 0 0-26-3 11 11 0 0 0-2 23z' fill='" + fill + "' stroke='#8d98a3' stroke-width='2'/>";
    };
    var body = "";
    if (kind === "sun") { body = isDay ? sun : moon; }
    else if (kind === "part") {
      body = "<g transform='translate(-8,-8) scale(0.8)'>" + (isDay ? sun : moon) + "</g>" + cloud("#eef1f4", 4);
    }
    else if (kind === "cloud") { body = cloud("#d9dee3", 0); }
    else if (kind === "fog") {
      body = cloud("#e3e6e9", -6) + "<g stroke='#8d98a3' stroke-width='3' stroke-linecap='round'>" +
        "<line x1='14' y1='50' x2='50' y2='50'/><line x1='20' y1='57' x2='44' y2='57'/></g>";
    }
    else if (kind === "drizzle" || kind === "rain") {
      var n = kind === "rain" ? 3 : 2, drops = "";
      for (var i = 0; i < n; i++) {
        var x = 22 + i * (n === 3 ? 10 : 14);
        drops += "<line x1='" + x + "' y1='48' x2='" + (x - 4) + "' y2='58'/>";
      }
      body = cloud("#d9dee3", -6) + "<g stroke='#2f7fc1' stroke-width='3.5' stroke-linecap='round'>" + drops + "</g>";
    }
    else if (kind === "snow") {
      body = cloud("#e8ecef", -6) + "<g fill='#6aa8d8'><circle cx='22' cy='52' r='3'/><circle cx='32' cy='57' r='3'/><circle cx='42' cy='52' r='3'/></g>";
    }
    else if (kind === "storm") {
      body = cloud("#c9cfd6", -6) + "<path d='M34 40l-9 12h7l-4 10 12-14h-7l4-8z' fill='#f2b01e'/>";
    }
    return "<svg viewBox='0 0 64 64' xmlns='http://www.w3.org/2000/svg'>" + body + "</svg>";
  }

  function loadWeather() {
    var url = "https://api.open-meteo.com/v1/forecast?latitude=" + CFG.lat + "&longitude=" + CFG.lon +
      "&current=temperature_2m,apparent_temperature,weather_code,wind_speed_10m,is_day" +
      "&hourly=temperature_2m,precipitation_probability,weather_code,is_day" +
      "&daily=temperature_2m_max,temperature_2m_min,sunset,weather_code,precipitation_probability_max" +
      "&timezone=Europe%2FPrague&forecast_days=2";
    getJSON(url, {}, renderWeather, function (err) {
      if (!$("wx-body").getAttribute("data-ok")) {
        $("wx-body").innerHTML = "<div class='dep-msg'>Počasí se nepodařilo načíst (" + esc(err) + ").</div>";
      }
    });
  }

  function renderWeather(d) {
    var cur = d.current || {}, hr = d.hourly || {}, day = d.daily || {};
    var w = wmo(cur.weather_code);
    var nowKey = String(cur.time || "").slice(0, 13); // "2026-09-23T13"
    var start = 0, times = hr.time || [];
    for (var i = 0; i < times.length; i++) { if (times[i].slice(0, 13) > nowKey) { start = i; break; } }

    var html = "<div class='wx-now'>" +
      "<div class='wx-icon'>" + icon(w[1], cur.is_day !== 0) + "</div>" +
      "<div class='wx-temp'>" + Math.round(cur.temperature_2m) + "°</div>" +
      "<div><div class='wx-desc'>" + esc(w[0]) + "</div>" +
      "<div class='wx-sub'>pocitově " + Math.round(cur.apparent_temperature) + "° · vítr " + Math.round(cur.wind_speed_10m) + " km/h<br>" +
      "dnes " + Math.round((day.temperature_2m_min || [0])[0]) + "° až " + Math.round((day.temperature_2m_max || [0])[0]) + "°" +
      ((day.sunset && day.sunset[0]) ? " · západ slunce " + esc(day.sunset[0].slice(11, 16)) : "") +
      "</div></div></div>";

    html += "<div class='wx-hours'>";
    for (var j = start; j < Math.min(start + 7, times.length); j++) {
      var p = (hr.precipitation_probability || [])[j];
      html += "<div class='wx-hour'><div class='h'>" + esc(times[j].slice(11, 13)) + ":00</div>" +
        icon(wmo(hr.weather_code[j])[1], (hr.is_day || [])[j] !== 0) +
        "<div class='t'>" + Math.round(hr.temperature_2m[j]) + "°</div>" +
        "<div class='p'>" + (p >= 20 ? p + " %" : "") + "</div></div>";
    }
    html += "</div>";

    // Tip na zbytek pracovního dne (do 19:00, nebo aspoň 6 hodin dopředu).
    var worst = -1, worstIdx = -1, todayKey = nowKey.slice(0, 10);
    for (var k = start; k < Math.min(start + 12, times.length); k++) {
      var hour = +times[k].slice(11, 13);
      if (times[k].slice(0, 10) !== todayKey || (hour > 19 && k - start >= 6)) { break; }
      var pp = (hr.precipitation_probability || [])[k];
      if (pp > worst) { worst = pp; worstIdx = k; }
    }
    var tip, cls = "wx-tip";
    if (worst >= 50) {
      tip = "Kolem " + times[worstIdx].slice(11, 13) + ":00 pravděpodobně zaprší (" + worst + " %). Vezměte si deštník.";
      cls += " rain";
    } else if (worst >= 30) {
      tip = "Kolem " + times[worstIdx].slice(11, 13) + ":00 hrozí přeháňka (" + worst + " %). Deštník se může hodit.";
      cls += " rain";
    } else if (worst >= 0) {
      tip = "Do večera by pršet nemělo.";
    } else {
      tip = "";
    }
    if (tip) { html += "<div class='" + cls + "'>" + esc(tip) + "</div>"; }

    // Zítřek
    if (day.temperature_2m_max && day.temperature_2m_max.length > 1) {
      var tw = wmo((day.weather_code || [])[1]), tp = (day.precipitation_probability_max || [])[1];
      var tmr = addDays(new Date(), 1);
      html += "<div class='wx-tomorrow'><div style='width:2.6em'>" + icon(tw[1], true) + "</div>" +
        "<div class='val'><span class='lbl'>Zítra · " + esc(DAYS[tmr.getDay()]) + "</span><br>" +
        esc(tw[0]) + ", " + Math.round(day.temperature_2m_min[1]) + "° až " + Math.round(day.temperature_2m_max[1]) + "°" +
        (tp >= 20 ? " · srážky " + tp + " %" : "") + "</div></div>";
    }

    $("wx-body").innerHTML = html;
    $("wx-body").setAttribute("data-ok", "1");
  }

  // ---------------------------------------------------------------- odjezdy (Golemio / PID)
  var deps = null, depsError = "", depsLoadedAt = null, infotexts = [];

  function routeColor(r) {
    var n = String(r.short_name || "").toUpperCase();
    if (n === "A") { return "#00a562"; }
    if (n === "B") { return "#f8b322"; }
    if (n === "C") { return "#cf003d"; }
    if (r.type === 0) { return n.charAt(0) === "9" && n.length === 2 ? "#1d1d1b" : "#7a0603"; }
    if (r.type === 11) { return "#80166f"; }
    if (r.type === 2) { return "#0c3b7c"; }
    if (r.type === 3) { return n.charAt(0) === "9" && n.length === 3 ? "#1d1d1b" : "#007da8"; }
    return "#555";
  }

  function loadDepartures() {
    if (!CFG.golemioKey) {
      $("dep-body").innerHTML = "<div class='dep-msg'>Chybí API klíč Golemio.<br>" +
        "Zdarma na api.golemio.cz/api-keys, pak ho vložte do GitHub Secrets jako GOLEMIO_API_KEY.</div>";
      return;
    }
    var h = new Date().getHours();
    if (h < 5 || h >= 22) { return; } // v noci nešetříme limit API zbytečně
    var q = [];
    for (var i = 0; i < CFG.stops.length; i++) { q.push("names=" + encodeURIComponent(CFG.stops[i])); }
    q.push("minutesAfter=60", "limit=40", "preferredTimezone=Europe%2FPrague", "includeMetroTrains=true");
    getJSON("https://api.golemio.cz/v2/pid/departureboards?" + q.join("&"),
      { "x-access-token": CFG.golemioKey },
      function (data) {
        deps = data.departures || [];
        infotexts = data.infotexts || [];
        depsError = "";
        depsLoadedAt = new Date();
        renderDepartures();
      },
      function (err) { depsError = err; renderDepartures(); });
  }

  function renderDepartures() {
    var body = $("dep-body");
    if (deps === null) {
      body.innerHTML = "<div class='dep-msg'>Odjezdy se nepodařilo načíst (" + esc(depsError) + ").</div>";
      return;
    }
    var now = new Date().getTime();
    var groups = [], byKey = {};
    for (var i = 0; i < deps.length; i++) {
      var d = deps[i], ts = d.departure_timestamp || {};
      var t = parseIsoOffset(ts.predicted || ts.scheduled);
      if (t === null) { continue; }
      var mins = Math.floor((t - now) / 60000);
      if (mins < CFG.walkMinutes) { continue; }
      var route = d.route || {}, trip = d.trip || {};
      var key = route.short_name + "|" + trip.headsign;
      if (!byKey[key]) {
        byKey[key] = { route: route, headsign: trip.headsign, platform: (d.stop || {}).platform_code, times: [] };
        groups.push(byKey[key]);
      }
      if (byKey[key].times.length < 3) { byKey[key].times.push(mins); }
    }
    if (!groups.length) {
      body.innerHTML = "<div class='dep-msg'>V příští hodině nic neodjíždí.</div>";
      return;
    }
    var html = "";
    for (var g = 0; g < Math.min(groups.length, 8); g++) {
      var gr = groups[g], tm = gr.times;
      var first = tm[0] < 1 ? "teď" : tm[0] + "<small>min</small>";
      var rest = "";
      for (var r = 1; r < tm.length; r++) { rest += "<span>" + tm[r] + "</span>"; }
      html += "<div class='dep-row'>" +
        "<div class='dep-badge-cell'><span class='dep-badge' style='background:" + routeColor(gr.route) + "'>" + esc(gr.route.short_name) + "</span></div>" +
        "<div class='dep-head'>" + esc(gr.headsign) + (gr.platform && !/^[ABC]$/.test(gr.route.short_name) ? "<span class='plat'>stan. " + esc(gr.platform) + "</span>" : "") + "</div>" +
        "<div class='dep-times'>" + first + rest + "</div></div>";
    }
    var alerts = [];
    for (var a = 0; a < infotexts.length && alerts.length < 2; a++) {
      if (infotexts[a] && infotexts[a].text) { alerts.push(esc(infotexts[a].text)); }
    }
    if (alerts.length) { html += "<div class='dep-alert'>" + alerts.join("<br>") + "</div>"; }
    html += "<div class='dep-foot'>Data PID / Golemio · načteno " + hhmm(depsLoadedAt) +
      (depsError ? " · poslední pokus selhal" : "") +
      (CFG.walkMinutes ? " · spoje dřív než za " + CFG.walkMinutes + " min vynechány" : "") + "</div>";
    body.innerHTML = html;
  }

  // ---------------------------------------------------------------- start
  $("dep-stop").innerHTML = esc(CFG.stopLabel);
  tickClock(); renderNameday(); loadWeather(); loadDepartures();
  setInterval(tickClock, 5000);
  setInterval(renderNameday, 10 * 60 * 1000);
  setInterval(loadWeather, 15 * 60 * 1000);
  setInterval(loadDepartures, 60 * 1000);
  setInterval(function () { if (deps !== null) { renderDepartures(); } }, 15 * 1000);

  var ph0 = currentPhase();
  if (ph0) { show("menu"); setTimeout(cycle, ph0.menu * 1000); }
  else { show("info"); setTimeout(cycle, 30 * 1000); }
})();
"""


def render_info_parts(info_cfg: dict | None, target_day: str) -> tuple[str, str, str]:
    """Vrátí (css, html, js) druhé obrazovky. Bez konfigurace vrací prázdné řetězce."""
    if info_cfg is None:
        return "", "", ""
    today = datetime.now()
    # Menu je platné jen v den, pro který bylo vygenerováno (jinak TV ukazuje jen info).
    menu_date = today.strftime("%Y-%m-%d") if today.weekday() < 5 and DAYS[today.weekday()] == target_day else ""
    js = (INFO_JS
          .replace("__CFG__", json.dumps(info_cfg, ensure_ascii=False))
          .replace("__MENU_DATE__", json.dumps(menu_date))
          .replace("__NAMEDAYS__", json.dumps(NAMEDAYS_CS, ensure_ascii=False, separators=(",", ":"))))
    # "</" uvnitř <script> by předčasně ukončilo blok.
    js = js.replace("</script", "<\\/script")
    return INFO_CSS, INFO_HTML, js


def render_dashboard(results: Iterable[dict], output: Path, refresh_seconds: int, target_day: str, info_cfg: dict | None = None) -> None:
    now = datetime.now().strftime("%d. %m. %Y %H:%M")

    # TV polish režim: zachová čitelnost, ale už nezkracuje počet položek.
    # Dezerty necháváme mimo hlavní TV přehled, aby neubíraly místo obědům.

    def is_dessert(item: MenuItem) -> bool:
        text = f"{item.section} {item.title}".lower()
        dessert_words = (
            "dezert", "dezerty", "tiramisu", "větrník", "věneček", "punčový řez",
            "zmrzlin", "koláč od pekaře", "domácí koláč"
        )
        return any(word in text for word in dessert_words)

    def tidy_title_for_tv(title: str) -> str:
        title = clean_line(title)
        # Jemné zkrácení některých opakovaných frází, aby se řádky na TV nelámaly zbytečně dlouze.
        replacements = {
            "s domácím bramborovým salátem": "s bramborovým salátem",
            "s hedvábnou bramborovou kaší": "s bramborovou kaší",
            "připravený ": "",
            "dozlatova ": "",
        }
        for old, new_val in replacements.items():
            title = title.replace(old, new_val)
        return title

    cards: list[str] = []
    for r in results:
        name_raw = r["name"]
        name = html.escape(name_raw)
        source_url = r.get("url") or ""
        host = html.escape(urlparse(source_url).netloc.replace("www.", ""))
        if r.get("source_type") == "rss":
            host = f"{host} · RSS"
        if r.get("cached"):
            host = f"{host} · cache"

        items: list[MenuItem] = r.get("items") or []
        if items:
            filtered = [item for item in items if not is_dessert(item)]
            if not filtered:
                filtered = items
            rows: list[str] = []
            for item in filtered:
                title = tidy_title_for_tv(item.title)
                price = f"<span class='price'>{html.escape(item.price)}</span>" if item.price else ""
                note = f"<div class='note'>{html.escape(item.note)}</div>" if item.note else ""
                rows.append(
                    "<div class='dish'>"
                    "<div class='dish-main'>"
                    f"<div class='dish-title'>{html.escape(title)}</div>"
                    f"{price}"
                    "</div>"
                    f"{note}"
                    "</div>"
                )
            body = "\n".join(rows)
        elif r.get("empty_ok"):
            body = "<div class='empty'>Menu zatím není dostupné.<br><span>Zkusíme znovu při dalším refreshi.</span></div>"
        else:
            body = "<div class='error'>Menu se nepodařilo načíst.<br><span>Zkusíme znovu při dalším refreshi.</span></div>"

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

    info_css, info_html, info_js = render_info_parts(info_cfg, target_day)
    menu_screen_class = "screen active" if info_cfg is not None else ""

    html_doc = f"""<!doctype html>
<html lang="cs">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta http-equiv="refresh" content="{refresh_seconds}">
<title>Polední menu – {html.escape(DAY_TITLE[target_day])}</title>
<style>
/* TV polish CSS: konzervativní layout pro starší Samsung browser.
   Záměrně bez CSS gridu, proměnných, webfontů a gradientů. */
* {{ box-sizing: border-box; }}
html, body {{
  margin: 0;
  padding: 0;
  width: 100%;
  height: 100%;
  overflow: hidden;
}}
body {{
  padding: 9px 10px 8px;
  background: #f1eadf;
  color: #171412;
  font-family: Arial, Helvetica, sans-serif;
}}
.topbar {{
  display: table;
  width: 100%;
  height: 38px;
  margin-bottom: 7px;
}}
.topbar > div {{
  display: table-cell;
  vertical-align: middle;
}}
.topbar > div:last-child {{ text-align: right; }}
h1 {{
  display: inline;
  margin: 0;
  font-size: 30px;
  line-height: 1;
  letter-spacing: -0.8px;
}}
.subtitle {{
  display: inline;
  margin-left: 12px;
  color: #8b3f1d;
  font-size: 22px;
  line-height: 1;
  font-weight: 900;
}}
.timestamp {{
  color: #625b52;
  font-size: 14px;
  white-space: nowrap;
}}
.grid {{
  display: block;
  width: 100%;
  height: calc(100vh - 58px);
  font-size: 0;
}}
.card {{
  display: inline-block;
  vertical-align: top;
  width: 32.62%;
  height: calc((100vh - 72px) / 2);
  margin: 0 0.75% 7px 0;
  padding: 9px 11px 7px;
  background: #fffdf8;
  border: 1px solid #d8cdbc;
  border-radius: 13px;
  overflow: hidden;
  font-size: 16px;
}}
.card:nth-child(3n) {{ margin-right: 0; }}
.card header {{
  display: table;
  width: 100%;
  padding-bottom: 5px;
  margin-bottom: 4px;
  border-bottom: 2px solid #e4d8c7;
}}
.card header h2, .card header a {{
  display: table-cell;
  vertical-align: baseline;
}}
h2 {{
  margin: 0;
  font-size: 21px;
  line-height: 1.05;
  letter-spacing: -0.5px;
  color: #11100f;
}}
a {{
  color: #6c655d;
  text-decoration: none;
  font-size: 11px;
  text-align: right;
  white-space: nowrap;
}}
.menu-list {{
  width: 100%;
  overflow: hidden;
}}
.dish {{
  display: block;
  width: 100%;
  padding: 3px 0 4px;
  border-bottom: 1px solid #eadfce;
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
  font-size: 14.6px;
  line-height: 1.12;
  font-weight: 700;
}}
.price {{
  display: table-cell;
  vertical-align: top;
  color: #111827;
  font-size: 14.5px;
  line-height: 1.08;
  font-weight: 900;
  white-space: nowrap;
  text-align: right;
  min-width: 42px;
}}
.note {{
  display: block;
  color: #655d55;
  font-size: 10.8px;
  line-height: 1.08;
  margin-top: 1px;
  padding-right: 48px;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}}
.more {{
  color: #8b3f1d;
  font-size: 12px;
  line-height: 1.1;
  font-weight: 800;
  padding-top: 5px;
}}
.error, .empty {{
  color: #625b52;
  font-size: 17px;
  line-height: 1.25;
  padding: 18px 0;
}}
.empty span, .error span {{
  display: inline-block;
  margin-top: 5px;
  color: #8b3f1d;
  font-size: 13px;
}}
@media (max-width: 1200px) {{
  html, body {{ overflow: auto; }}
  .grid {{ height: auto; }}
  .card {{ width: 48.5%; height: auto; min-height: 310px; }}
  .card:nth-child(3n) {{ margin-right: 0.75%; }}
  .card:nth-child(2n) {{ margin-right: 0; }}
}}
@media (max-width: 760px) {{
  body {{ padding: 14px; overflow: auto; }}
  .topbar, .topbar > div {{ display: block; height: auto; text-align: left; }}
  h1 {{ display: block; font-size: 38px; }}
  .subtitle {{ display: block; margin: 4px 0 0; font-size: 24px; }}
  .timestamp {{ margin-top: 8px; }}
  .card {{ display: block; width: 100%; min-height: auto; margin-right: 0; }}
}}
{info_css}
</style>
</head>
<body>
<div id="screen-menu" class="{menu_screen_class}">
  <div class="topbar">
    <div><h1>Polední menu</h1><div class="subtitle">{html.escape(DAY_TITLE[target_day])}</div></div>
    <div class="timestamp">Aktualizováno {html.escape(now)} · refresh {refresh_seconds // 60} min</div>
  </div>
  <main class="grid">{''.join(cards)}</main>
</div>
{info_html}
{"<script>" + info_js + "</script>" if info_js else ""}
</body>
</html>
"""
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(html_doc, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Polední menu dashboard v7.2")
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
    # v7.0: druhá TV obrazovka (počasí, svátek, odjezdy MHD)
    ap.add_argument("--no-info", action="store_true", help="Vypne druhou obrazovku s počasím, svátkem a odjezdy")
    ap.add_argument("--golemio-key", default=os.environ.get("GOLEMIO_API_KEY", ""), help="API klíč Golemio pro odjezdy MHD (nebo env GOLEMIO_API_KEY)")
    ap.add_argument("--stops", default="Pražského povstání", help="Názvy zastávek oddělené čárkou, přesně jako v PID")
    ap.add_argument("--walk-minutes", type=int, default=3, help="Nezobrazovat spoje, které odjíždějí dřív, než se na zastávku dojde")
    ap.add_argument("--lat", type=float, default=OFFICE_LAT)
    ap.add_argument("--lon", type=float, default=OFFICE_LON)
    ap.add_argument("--schedule", default=DEFAULT_SCHEDULE,
                    help="Střídání obrazovek během dne: 'DO_ČASU=MENU_S/INFO_S,...', "
                         "např. '10:30=20/60,13:00=60/20,14:00=15/60'. Po poslední fázi jen informace.")
    # Starší přepínače z v7.0/v7.1 – ponechané, aby workflow nespadl; nahrazuje je --schedule.
    ap.add_argument("--menu-seconds", type=int, default=None, help=argparse.SUPPRESS)
    ap.add_argument("--info-seconds", type=int, default=None, help=argparse.SUPPRESS)
    ap.add_argument("--menu-until", default=None, help=argparse.SUPPRESS)
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
    info_cfg = None if args.no_info else info_screen_config(args)
    render_dashboard(results, out, args.refresh, target_day, info_cfg)
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
