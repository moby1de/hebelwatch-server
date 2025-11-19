# -*- coding: utf-8 -*-
"""
ereignisse_abruf.py
Kalender für HebelWatch (Ampel 3) mit:
- Jahresbasierte fixe Termine (Hexensabbat, DAX-Heuristik)
- Offizielle Fetcher (best effort) für DAX/ES50/SPDJI + Zinsentscheide
- Yahoo-Earnings (heute & morgen)
- Tages-Cache, Debug-Logging
Optimierte Version
"""

from __future__ import annotations
from bs4 import BeautifulSoup
import os
import json
import importlib
import re
import requests
from datetime import datetime, timedelta, date
from typing import List, Dict, Any, Optional

# --- Hilfsfunktionen zuerst definieren ---

def _nth_weekday_of_month(y, m, weekday, n):
    d = date(y, m, 1)
    offset = (weekday - d.weekday()) % 7
    return d + timedelta(days=offset + 7*(n-1))

def _last_weekday_of_month(y, m, weekday):
    if m == 12:
        d = date(y+1, 1, 1) - timedelta(days=1)
    else:
        d = date(y, m+1, 1) - timedelta(days=1)
    offset = (d.weekday() - weekday) % 7
    return d - timedelta(days=offset)

def _easter_sunday(y):
    a = y % 19
    b = y // 100
    c = y % 100
    d = b // 4
    e = b % 4
    f = (b + 8) // 25
    g = (b - f + 1) // 3
    h = (19*a + b - d - g + 15) % 30
    i = c // 4
    k = c % 4
    l = (32 + 2*e + 2*i - h - k) % 7
    m_val = (a + 11*h + 22*l) // 451
    month = (h + l - 7*m_val + 114) // 31
    day = ((h + l - 7*m_val + 114) % 31) + 1
    return date(y, month, day)

def _observed_weekend(d: date) -> date:
    if d.weekday() == 5:
        return d - timedelta(days=1)
    if d.weekday() == 6:
        return d + timedelta(days=1)
    return d

def _first_friday(y: int, m: int) -> date:
    d = date(y, m, 1)
    off = (4 - d.weekday()) % 7
    return d + timedelta(days=off)

def _third_friday(y: int, m: int) -> date:
    d = date(y, m, 1)
    offset = (4 - d.weekday()) % 7
    first_friday = d + timedelta(days=offset)
    return first_friday + timedelta(weeks=2)

# --- API Keys und Basis-Helper ---

FRED_API_KEY_FALLBACK = "ac24c6331bbe4bd92e5cc0ce443d4d2e"
TE_API_KEY = "123456"
FRED_API_KEY_FALLBACK = "ac24c6331bbe4bd92e5cc0ce443d4d2e"

# NEU: Destatis-Terminsuche für Verbraucherpreisindex
DEST_DE_CPI_HTML_URL = (
    "https://www.destatis.de/SiteGlobals/Forms/Suche/Termine/DE/"
    "Terminsuche_Formular.html"
    "?templateQueryString=verbraucherpreisindex"
    "&cl2Taxonomies_Themen_0=preise"
    "&cl2Taxonomies_Themen_1=verbraucherpreisindex"
)



def _load_is_market_open():
    for mod in ("LeverageLens", "LeverageLensDax","LeverageLensFutures","LeverageLensFuturesDax"):
        try:
            m = importlib.import_module(mod)
            f = getattr(m, "is_market_open", None)
            if callable(f):
                return f
        except ImportError:
            continue
    return None

_IS_MARKET_OPEN = _load_is_market_open()

def load_or_create_fred_api_key() -> str:
    path = os.path.join("CSV", "fred_api.txt")
    if not os.path.exists(path):
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write("Hier bitte API Key eingeben: xxx\n")
        except Exception:
            return FRED_API_KEY_FALLBACK
        return FRED_API_KEY_FALLBACK
    try:
        content = open(path, "r", encoding="utf-8").read().strip()
    except Exception:
        return FRED_API_KEY_FALLBACK
    m = re.search(r"\b([0-9a-fA-F]{32})\b", content)
    return m.group(1) if m else FRED_API_KEY_FALLBACK

FRED_API_KEY = os.getenv("FRED_API_KEY") or load_or_create_fred_api_key()

def _fred_get(path, params):
    key = FRED_API_KEY
    if not key:
        return None
    base = "https://api.stlouisfed.org/fred"
    params = {**params, "api_key": key, "file_type": "json"}
    try:
        r = requests.get(f"{base}/{path}", params=params, timeout=12)
        r.raise_for_status()
        return r.json()
    except Exception:
        return None

def _te_get(url):
    key = TE_API_KEY
    if not key:
        return None
    try:
        if ":" in key:
            auth = tuple(key.split(":", 1))
            r = requests.get(url, auth=auth, timeout=12)
        else:
            r = requests.get(f"{url}&c={key}", timeout=12)
        r.raise_for_status()
        return r.json()
    except Exception:
        return None

UA = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                    "(KHTML, like Gecko) Chrome/123 Safari/537.36"}

def _fetch(url: str, timeout: int = 12) -> Optional[str]:
    try:
        r = requests.get(url, headers=UA, timeout=timeout)
        r.raise_for_status()
        return r.text
    except Exception:
        return None

def fetch_de_cpi_from_investing(window_days: int = 400, debug: bool = False) -> List[Dict[str, Any]]:
    """
    Holt deutsche CPI-Termine (Germany CPI YoY) von Investing.com.

    Quelle:
      https://www.investing.com/economic-calendar/german-cpi-737

    Liefert Events im Format:
      {"datum": "YYYY-MM-DD", "typ": "CPI", "text": "DE Verbraucherpreise (VPI)", "index": "DAX"}
    nur für Termine im Zeitfenster [heute-7 Tage, heute+window_days].
    """
    url = "https://www.investing.com/economic-calendar/german-cpi-737"
    rows: List[Dict[str, Any]] = []
    today = date.today()
    horizon = today + timedelta(days=window_days)

    html = _fetch(url, timeout=15)
    if not html:
        if debug:
            print("[DE-CPI] Investing HTML nicht abrufbar.")
        return rows

    try:
        soup = BeautifulSoup(html, "html.parser")
    except Exception as e:
        if debug:
            print(f"[DE-CPI] BeautifulSoup-Fehler: {e}")
        return rows

    # Tabelle finden, die die Germany CPI YoY Releases enthält
    table = None
    for t in soup.find_all("table"):
        headers = [th.get_text(strip=True) for th in t.find_all("th")]
        if any("Release Date" in h for h in headers) and any("Time" in h for h in headers):
            table = t
            break

    if table is None:
        if debug:
            print("[DE-CPI] Keine passende Tabelle gefunden.")
        return rows

    body = table.find("tbody") or table
    seen_dates: set[date] = set()

    for tr in body.find_all("tr"):
        tds = tr.find_all("td")
        if len(tds) < 2:
            continue

        # 1. Spalte: Release Date, z.B. "Nov 28, 2025 (Nov)"
        raw_date = tds[0].get_text(" ", strip=True)
        if not raw_date:
            continue

        # Klammern "(Nov)" entfernen, wir brauchen nur "Nov 28, 2025"
        if "(" in raw_date:
            raw_date = raw_date.split("(", 1)[0].strip()

        # Versuch: englisches Datumsformat von Investing
        dt = None
        for fmt in ("%b %d, %Y", "%B %d, %Y"):
            try:
                dt = datetime.strptime(raw_date, fmt).date()
                break
            except ValueError:
                continue
        if dt is None:
            continue

        # Zeitfenster-Filter
        if not ((today - timedelta(days=7)) <= dt <= horizon):
            continue

        if dt in seen_dates:
            continue
        seen_dates.add(dt)

        rows.append({
            "datum": dt.strftime("%Y-%m-%d"),
            "typ": "CPI",
            "text": "DE Verbraucherpreise (VPI)",
            "index": "DAX",
        })

    if debug:
        print(f"[DE-CPI] Investing → {len(rows)} Termine:",
              sorted(d.strftime("%Y-%m-%d") for d in seen_dates))

    return rows

def fetch_us_market_holidays_from_nasdaq(year: int, debug: bool = False) -> List[Dict[str, Any]]:
    """
    Holt US-Börsenfeiertage UND Early-Close-Tage (NYSE/Nasdaq) von Nasdaq.
    Quelle: https://www.nasdaqtrader.com/trader.aspx?id=calendar

    Events:
      typ = "Holiday"      -> Markt geschlossen
      typ = "EarlyClose"   -> verkürzter Handel
      index = "SP500"      -> gilt für S&P 500, Dow, Nasdaq in Ampel-Logik
    """
    url = "https://www.nasdaqtrader.com/trader.aspx?id=calendar"
    html = _fetch(url, timeout=15)
    rows: List[Dict[str, Any]] = []
    if not html:
        if debug:
            print("[HOL] Nasdaq-HTML nicht abrufbar.")
        return rows

    soup = BeautifulSoup(html, "html.parser")

    # Tabelle mit Überschrift "U.S. Equity and Options Markets Holiday Schedule"
    table = None
    for h in soup.find_all(["h2", "h3"]):
        if "U.S. Equity and Options Markets Holiday Schedule" in h.get_text():
            # nächste Tabelle nach dieser Überschrift
            sib = h
            while sib and sib.name != "table":
                sib = sib.find_next_sibling()
            table = sib
            break

    if table is None:
        if debug:
            print("[HOL] Keine Holiday-Tabelle auf Nasdaq-Seite gefunden.")
        return rows

    body = table.find("tbody") or table
    today = date.today()
    horizon = date(year, 12, 31)

    for tr in body.find_all("tr"):
        tds = tr.find_all("td")
        if len(tds) < 3:
            continue

        raw_date = tds[0].get_text(" ", strip=True)
        raw_status = tds[2].get_text(" ", strip=True)  # z.B. "Closed" oder "Early Close* - U.S., 1:00 p.m."

        # Beispiel-Formate aus Nasdaq:
        #  "January 1, 2025"
        #  "July 3, 2025"
        dt = None
        for fmt in ("%B %d, %Y", "%b %d, %Y"):
            try:
                dt = datetime.strptime(raw_date, fmt).date()
                break
            except ValueError:
                continue
        if dt is None or dt.year != year:
            continue

        # Nur zukünftige + jüngste Woche
        if not ((today - timedelta(days=7)) <= dt <= horizon):
            continue

        status_lower = raw_status.lower()
        if "closed" in status_lower:
            typ = "Holiday"
        elif "early close" in status_lower:
            typ = "EarlyClose"
        else:
            continue  # normale Handelstage ignorieren

        rows.append({
            "datum": dt.strftime("%Y-%m-%d"),
            "typ": typ,
            "text": "US Börsenfeiertag" if typ == "Holiday" else "US verkürzter Handel",
            "index": "SP500",
        })

    if debug:
        print(f"[HOL] US: {len(rows)} Einträge von Nasdaq für {year}.")
    return rows


def _easter_sunday(year: int) -> date:
    """Berechnet Ostersonntag (gregorianisch)."""
    # Anonymous Gregorian algorithm
    a = year % 19
    b = year // 100
    c = year % 100
    d = b // 4
    e = b % 4
    f = (b + 8) // 25
    g = (b - f + 1) // 3
    h = (19 * a + b - d - g + 15) % 30
    i = c // 4
    k = c % 4
    l = (32 + 2 * e + 2 * i - h - k) % 7
    m = (a + 11 * h + 22 * l) // 451
    month = (h + l - 7 * m + 114) // 31
    day = ((h + l - 7 * m + 114) % 31) + 1
    return date(year, month, day)

def compute_xetra_holidays(year: int) -> List[date]:
    """
    Xetra/Frankfurt-Feiertage nach Handelskalender:
    - 1. Januar
    - Karfreitag
    - Ostermontag
    - 1. Mai
    - 24., 25., 26. Dezember
    - 31. Dezember
    """
    easter = _easter_sunday(year)
    good_friday = easter - timedelta(days=2)
    easter_monday = easter + timedelta(days=1)

    return [
        date(year, 1, 1),
        good_friday,
        easter_monday,
        date(year, 5, 1),
        date(year, 12, 24),
        date(year, 12, 25),
        date(year, 12, 26),
        date(year, 12, 31),
    ]

def fetch_eu_market_holidays_xetra(year: int, debug: bool = False) -> List[Dict[str, Any]]:
    """
    Liefert Xetra-Börsenfeiertage als Events für den DAX.
    """
    today = date.today()
    horizon = date(year, 12, 31)
    rows: List[Dict[str, Any]] = []

    for dt in compute_xetra_holidays(year):
        if not ((today - timedelta(days=7)) <= dt <= horizon):
            continue
        rows.append({
            "datum": dt.strftime("%Y-%m-%d"),
            "typ": "Holiday",
            "text": "Xetra Börsenfeiertag",
            "index": "DAX",
        })

    if debug:
        print(f"[HOL] EU/Xetra: {len(rows)} Einträge für {year}.")
    return rows

def fetch_market_holidays(year: int, debug: bool = False) -> List[Dict[str, Any]]:
    """
    Kombiniert US- und EU-Börsenfeiertage:
    - US: Nasdaq Holiday Schedule
    - EU: Xetra-Handelskalender (DAX)
    """
    rows: List[Dict[str, Any]] = []
    rows += fetch_us_market_holidays_from_nasdaq(year, debug=debug)
    rows += fetch_eu_market_holidays_xetra(year, debug=debug)

    # Dedupe
    seen, out = set(), []
    for e in rows:
        k = (e["datum"], e["typ"], e.get("index",""))
        if k not in seen:
            seen.add(k)
            out.append(e)
    if debug:
        print(f"[HOL] Gesamt: {len(out)} Holiday/ EarlyClose-Events für {year}.")
    return out



# --- Index Normalisierung ---

def _normalize_index(name: str) -> str:
    if not name:
        return ""
    n = name.strip().upper()
    mapping = {
        "DAX": "DAX",
        "EURO STOXX 50": "EURO STOXX 50",
        "EUROSTOXX50": "EURO STOXX 50",
        "ESTOXX50": "EURO STOXX 50",
        "SX5E": "EURO STOXX 50",
        "S&P 500": "S&P 500",
        "SP500": "S&P 500",
        "S&P500": "S&P 500",
        "SPX": "S&P 500",
        "DOW JONES": "DOW JONES",
        "DJIA": "DOW JONES",
        "DJI": "DOW JONES",
        "ALL": "ALL",
    }
    return mapping.get(n, n)

# --- Firmenliste für Earnings ---

TECH_FIRMEN: Dict[str, str] = {
    "AAPL": "Apple", "MSFT": "Microsoft", "AMZN": "Amazon", "NVDA": "Nvidia",
    "GOOGL": "Alphabet", "META": "Meta Platforms", "TSLA": "Tesla", "ADBE": "Adobe",
    "INTC": "Intel", "AMD": "AMD", "CRM": "Salesforce", "IBM": "IBM",
    "SAP.DE": "SAP", "IFX.DE": "Infineon", "SIE.DE": "Siemens", "DTE.DE": "Deutsche Telekom",
    "ADS.DE": "Adidas", "ASML.AS": "ASML", "OR.PA": "L'Oréal", "MC.PA": "LVMH", "AIR.PA": "Airbus"
}

# --- Regeln ---

def rule_hexensabbat(year: int) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    for m in (3, 6, 9, 12):
        dte = _third_friday(year, m)
        rows.append({"datum": dte.strftime("%Y-%m-%d"), "typ": "Hexensabbat",
                     "text": "Großer Verfallstag (Hexensabbat)", "index": "ALL"})
    return rows

def rule_dax_rebalancing_after_hexensabbat(year: int) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    for m in (3, 6, 9, 12):
        fri = _third_friday(year, m)
        mon = fri + timedelta(days=3)
        rows.append({"datum": mon.strftime("%Y-%m-%d"), "typ": "Rebalancing",
                     "text": "DAX/MDAX-Rebalancing; Kurse reagieren kurzfristig stark, weil Indexfonds und ETFs ihre Bestände anpassen müssen", "index": "DAX"})
    return rows

# --- US Market Holidays ---

def compute_us_market_holidays(year: int):
    """Vollschließungen (Early Closes nicht enthalten)."""
    out = []

    # Fixe Tage (mit Observed-Regel)
    new_years = _observed_weekend(date(year, 1, 1))
    independence = _observed_weekend(date(year, 7, 4))
    christmas = _observed_weekend(date(year, 12, 25))
    # Juneteenth (seit 2022)
    juneteenth = _observed_weekend(date(year, 6, 19))

    # Bewegliche
    mlk = _nth_weekday_of_month(year, 1, 0, 3)          # 3. Montag im Jan
    presidents = _nth_weekday_of_month(year, 2, 0, 3)   # 3. Montag im Feb
    good_friday = _easter_sunday(year) - timedelta(days=2)
    memorial = _last_weekday_of_month(year, 5, 0)       # letzter Montag im Mai
    labor = _nth_weekday_of_month(year, 9, 0, 1)        # 1. Montag im Sep
    thanksgiving = _nth_weekday_of_month(year, 11, 3, 4)  # 4. Donnerstag im Nov

    def _add(d: date, name: str):
        if d.year == year:
            out.append({
                "datum": d.strftime("%Y-%m-%d"),
                "typ": "Holiday",
                "text": f"US-Börsenfeiertag: {name}",
                "index": "USA"
            })

    _add(new_years,    "New Year's Day")
    _add(mlk,          "Martin Luther King Jr. Day")
    _add(presidents,   "Presidents' Day")
    _add(good_friday,  "Good Friday")
    _add(memorial,     "Memorial Day")
    _add(juneteenth,   "Juneteenth")
    _add(independence, "Independence Day")
    _add(labor,        "Labor Day")
    _add(thanksgiving, "Thanksgiving Day")
    _add(christmas,    "Christmas Day")

    out.sort(key=lambda x: x["datum"])
    return out

def rule_us_jobs(year: int) -> List[Dict[str, Any]]:
    """
    US-Arbeitsmarktbericht (Nonfarm Payrolls):
    Standard: erster Freitag im Monat. Fällt dieser auf US-Börsenfeiertag,
    auf den vorherigen Handelstag (Do, ggf. weiter zurück) verschieben.
    """
    rows: List[Dict[str, Any]] = []
    try:
        holi = set(h["datum"] for h in compute_us_market_holidays(year))  # 'YYYY-MM-DD'
    except Exception:
        holi = set()

    for m in range(1, 13):
        d = _first_friday(year, m)
        # bei Feiertag nach hinten (vorheriger Handelstag)
        while d.strftime("%Y-%m-%d") in holi:
            d -= timedelta(days=1)
        rows.append({
            "datum": d.strftime("%Y-%m-%d"),
            "typ": "US Jobs",
            "text": "US Arbeitsmarktbericht (Nonfarm Payrolls)",
            "index": "ALL"
        })
    return rows

# --- BoJ-Termine ---

def fetch_boj(year: int, debug: bool=False) -> List[Dict[str, Any]]:
    """
    BoJ-Geldpolitik OHNE TE-API:
    1) Vergangene Meetings {year}: 'Statements on Monetary Policy {year}'
    2) Nächstes Meeting: 'Upcoming Monetary Policy Meeting Dates' (nur Entscheidungstag)
    """
    rows: List[Dict[str, Any]] = []

    def _parse_en_date(dstr: str) -> Optional[date]:
        dstr = dstr.replace("Sept.", "Sep.")
        for fmt in ("%b %d, %Y", "%B %d, %Y", "%b. %d, %Y", "%B. %d, %Y"):
            try:
                return datetime.strptime(dstr, fmt).date()
            except ValueError:
                pass
        for fmt in ("%b %d", "%B %d", "%b. %d", "%B. %d"):
            try:
                dt = datetime.strptime(dstr, fmt).date()
                return date(year, dt.month, dt.day)
            except ValueError:
                pass
        return None

    def _add(dt: Optional[date], text: str):
        if not dt or dt.year != year:
            return
        rows.append({
            "datum": dt.strftime("%Y-%m-%d"),
            "typ": "BoJ",
            "text": text,
            "index": "ALL"
        })

    # ---------- 1) Vergangene Meetings (Statements {year}) ----------
    try:
        url_state = f"https://www.boj.or.jp/en/mopo/mpmdeci/state_{year}/index.htm"
        html = _fetch(url_state)
        if html:
            soup = BeautifulSoup(html, "html.parser")
            # a) normale Link-Texte ("July 31, 2025")
            for a in soup.find_all("a"):
                txt = (a.get_text() or "").strip()
                if f", {year}" in txt:
                    _add(_parse_en_date(txt), "BoJ Geldpolitik (Sitzung/Entscheid)")
            # b) Regex-Fallback über die ganze Seite
            for m in re.finditer(rf"\b(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Sept|Oct|Nov|Dec)\.?\s+\d{{1,2}},\s*{year}\b", soup.get_text(" ", strip=True)):
                _add(_parse_en_date(m.group(0)), "BoJ Geldpolitik (Sitzung/Entscheid)")
        elif debug:
            print("[BoJ] state-page leer oder nicht erreichbar:", url_state)
    except Exception as e:
        if debug: print("[BoJ] Fehler state-page:", e)

    # ---------- 2) Upcoming – NUR Entscheidungstag (Tag 2, sonst Tag 1) ----------
    try:
        url_cal = "https://www.boj.or.jp/en/about/calendar/index.htm"
        html2 = _fetch(url_cal)
        if html2:
            soup2 = BeautifulSoup(html2, "html.parser")
            text_all = soup2.get_text(" ", strip=True)

            # a) Versuche den Block „Upcoming Monetary Policy Meeting Dates“
            target_txt = ""
            for node in soup2.find_all(text=re.compile(r"Monetary Policy Meeting", re.I)):
                # nimm Text des folgenden Blocks, falls vorhanden
                nxt = node.find_parent()
                nxt = nxt.find_next() if nxt else None
                if nxt:
                    target_txt = nxt.get_text(" ", strip=True)
                    if target_txt:
                        break
            if not target_txt:
                target_txt = text_all  # Fallback: kompletter Seitentext

            # b) Suche Datumsangaben und wähle Entscheidungstag
            # Beispiele: "Sep. 18 (Thurs.), 19 (Fri.)"  /  "September 17–18"
            m = re.search(r"(?:(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Sept|Oct|Nov|Dec)\.?)\s+(\d{1,2})\D+(\d{1,2})", target_txt)
            if m:
                month_str, day1, day2 = m.group(1), m.group(2), m.group(3)
                decision = _parse_en_date(f"{month_str} {day2}, {year}") or _parse_en_date(f"{month_str} {day1}, {year}")
                _add(decision, "BoJ Geldpolitik (Entscheidungstag)")
            else:
                # Alternative Schreibweise: "September 17-18, 2025"
                m2 = re.search(rf"(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Sept|Oct|Nov|Dec)\.?\s+\d{{1,2}}\s*[-–]\s*(\d{{1,2}}),\s*{year}", target_txt)
                if m2:
                    month_str, day2 = m2.group(1), m2.group(2)
                    _add(_parse_en_date(f"{month_str} {day2}, {year}"), "BoJ Geldpolitik (Entscheidungstag)")
        elif debug:
            print("[BoJ] calendar-page leer oder nicht erreichbar:", url_cal)
    except Exception as e:
        if debug: print("[BoJ] Fehler calendar-page:", e)

    # ---------- Dedupe + Sort ----------
    seen, out = set(), []
    for e in rows:
        k = (e.get("datum",""), e.get("typ",""), e.get("index",""))
        if k not in seen and e.get("datum"):
            seen.add(k); out.append(e)
    out.sort(key=lambda x: x["datum"])

    if debug: print(f"[Fetcher] BoJ {year}: {len(out)} Termine (BoJ-Web).")
    return out

# --- Fetcher: Zinsentscheide ---

ECB_FALLBACK_2025 = ["2025-01-23","2025-03-13","2025-04-10","2025-06-12",
                     "2025-07-17","2025-09-11","2025-10-30","2025-12-11"]

FOMC_FALLBACK_2025 = ["2025-01-29","2025-03-19","2025-05-07","2025-06-18",
                      "2025-07-30","2025-09-17","2025-11-05","2025-12-17"]

def fetch_fomc(year: int, debug: bool=False) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    html = _fetch("https://www.federalreserve.gov/monetarypolicy/fomccalendars.htm")
    if html and BeautifulSoup:
        soup = BeautifulSoup(html, "html.parser")

        # Verbesserte Suche nach FOMC-Terminen
        for year_header in soup.find_all(text=re.compile(rf"\b{year}\b")):
            # Suche im Eltern-Container nach FOMC-spezifischen Terminen
            container = year_header.parent
            if container:
                container_text = container.get_text()
                # Suche speziell nach FOMC Meeting-Daten
                meetings = re.findall(r"(FOMC meeting|Meeting of the FOMC|FOMC).*?([A-Za-z]+)\s+(\d{1,2})(?:\s*–\s*(\d{1,2}))?", container_text, re.IGNORECASE)
                for meeting, month, day1, day2 in meetings:
                    try:
                        # Entscheidungstag ist normalerweise der letzte Tag
                        decision_day = day2 if day2 else day1
                        d = datetime.strptime(f"{month} {decision_day} {year}", "%B %d %Y").date()
                        rows.append({"datum": d.strftime("%Y-%m-%d"), "typ": "FED", "text": "FED-Zinsentscheid", "index": "ALL"})
                    except Exception:
                        continue

    if not rows and year == 2025:
        rows = [{"datum": d, "typ": "FED", "text": "FED-Zinsentscheid", "index": "ALL"} for d in FOMC_FALLBACK_2025]
        if debug: print("[Fallback] FOMC 2025 Termine verwendet:", FOMC_FALLBACK_2025)

    if debug: print(f"[Fetcher] FOMC {year}: {len(rows)} Termine.")
    return rows

def fetch_ecb(year: int, debug: bool=False) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    html = _fetch("https://www.ecb.europa.eu/press/calendars/mgc/html/index.en.html")
    if html and BeautifulSoup:
        soup = BeautifulSoup(html, "html.parser")
        for tag in soup.find_all(text=re.compile(rf"\b{year}\b")):
            m = re.search(rf"(\d{{1,2}})\s+([A-Za-z]+)\s+{year}", tag)
            if m:
                dd, mon = m.group(1), m.group(2)
                try:
                    d = datetime.strptime(f"{dd} {mon} {year}", "%d %B %Y").date()
                    rows.append({"datum": d.strftime("%Y-%m-%d"), "typ": "EZB", "text": "EZB-Zinsentscheid", "index": "ALL"})
                except Exception:
                    pass
    if not rows and year == 2025:
        rows = [{"datum": d, "typ": "EZB", "text": "EZB-Zinsentscheid", "index": "ALL"} for d in ECB_FALLBACK_2025]
        if debug: print("[Fallback] EZB 2025 Termine verwendet:", ECB_FALLBACK_2025)
    if debug: print(f"[Fetcher] EZB {year}: {len(rows)} Termine.")
    return rows

# --- Fetcher: Indizes (best effort) ---

def fetch_deutsche_boerse_dax_reviews(year: int, debug: bool=False) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    html = _fetch("https://www.deutsche-boerse.com/dbg-de/ueber-uns/presse/pressemitteilungen")
    if html and BeautifulSoup:
        soup = BeautifulSoup(html, "html.parser")
        for link in soup.find_all("a", href=True):
            txt = (link.get_text() or "").strip()
            if str(year) in txt and re.search(r"(DAX|MDAX|TecDAX).*(Review|Überprüfung|Indexanpassung)", txt, re.IGNORECASE):
                sub = _fetch(link["href"]) if link["href"].startswith("http") else None
                if sub:
                    for m in re.finditer(r"(\d{2}\.\d{2}\.\d{4}|\d{4}-\d{2}-\d{2})", sub):
                        ds = m.group(1)
                        try:
                            dt = datetime.strptime(ds, "%d.%m.%Y").date() if "." in ds else datetime.strptime(ds, "%Y-%m-%d").date()
                            rows.append({"datum": dt.strftime("%Y-%m-%d"), "typ": "Rebalancing",
                                         "text": "DAX/MDAX/TecDAX Review (offiziell)", "index": "DAX"})
                        except Exception:
                            pass
    if debug: print(f"[Fetcher] Deutsche Börse DAX {year}: {len(rows)} Termine.")
    return rows

def fetch_stoxx_blue_chip_reviews(year: int, debug: bool=False) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    html = _fetch("https://www.stoxx.com/index-reviews")
    if html and BeautifulSoup:
        soup = BeautifulSoup(html, "html.parser")
        for tag in soup.find_all(text=re.compile(rf"\b{year}\b")):
            if re.search(r"(EURO\s*STOXX\s*50|SX5E)", tag, re.IGNORECASE):
                ctx = tag.parent.get_text(" ", strip=True) if tag and tag.parent else str(tag)
                for m in re.finditer(rf"(\d{{1,2}}\s+[A-Za-z]+\s+{year}|\d{{4}}-\d{{2}}-\d{{2}})", ctx):
                    ds = m.group(1)
                    try:
                        dt = datetime.strptime(ds, "%Y-%m-%d").date() if "-" in ds else datetime.strptime(ds, "%d %B %Y").date()
                        rows.append({"datum": dt.strftime("%Y-%m-%d"), "typ": "Rebalancing",
                                     "text": "EURO STOXX 50 Review (offiziell)", "index": "EURO STOXX 50"})
                    except Exception:
                        pass
    if debug: print(f"[Fetcher] STOXX ES50 {year}: {len(rows)} Termine.")
    return rows

def fetch_spdji_changes(year: int, include_minor: bool=True, debug: bool=False) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    html = _fetch("https://www.spglobal.com/spdji/en/index-notices/")
    if html and BeautifulSoup:
        soup = BeautifulSoup(html, "html.parser")
        for link in soup.find_all("a", href=True):
            txt = (link.get_text() or "").strip()
            if not txt:
                continue
            if re.search(rf"\b{year}\b", txt) and (("S&P 500" in txt) or ("Dow Jones" in txt) or ("DJIA" in txt)):
                if not include_minor and not re.search(r"(reconstitution|rebalance|index changes?)", txt, re.IGNORECASE):
                    continue
                sub = _fetch(link["href"]) if link["href"].startswith("http") else None
                if not sub:
                    continue
                for m in re.finditer(r"(\d{4}-\d{2}-\d{2}|\b[A-Za-z]+\s+\d{1,2},\s+\d{4}\b)", sub):
                    ds = m.group(1)
                    try:
                        dt = datetime.strptime(ds, "%Y-%m-%d").date() if "-" in ds else datetime.strptime(ds, "%B %d, %Y").date()
                        idx = "S&P 500" if re.search(r"S&P\s*500", sub, re.IGNORECASE) else ("DOW JONES" if re.search(r"(Dow Jones|DJIA)", sub, re.IGNORECASE) else "ALL")
                        rows.append({"datum": dt.strftime("%Y-%m-%d"), "typ": "Index Notice",
                                     "text": "S&P DJI: Indexänderung/Notice", "index": idx})
                    except Exception:
                        pass
    if debug: print(f"[Fetcher] S&P DJI {year}: {len(rows)} Notices.")
    return rows

# --- Yahoo Earnings ---

def get_mega_cap_earnings_events(window_days: int = 14, debug: bool = False) -> List[Dict[str, Any]]:
    """
    Holt die Earnings-Termine der 'Magnificent 7' (AAPL, MSFT, AMZN, GOOGL/GOOG, META, TSLA, NVDA)
    für die nächsten `window_days` Tage aus dem Yahoo Earnings Calendar.
    Pro Tag wird höchstens EIN Event erzeugt, das alle gefundenen Firmen zusammenfasst.
    """
    if requests is None or BeautifulSoup is None:
        if debug: print("[Ereignisse] requests/BeautifulSoup fehlen – Earnings übersprungen.")
        return []

    M7 = {"AAPL", "MSFT", "AMZN", "GOOGL", "GOOG", "META", "TSLA", "NVDA"}
    base_url = "https://finance.yahoo.com/calendar/earnings?day={date}"
    headers = {"User-Agent": "Mozilla/5.0"}

    out: List[Dict[str, Any]] = []
    today = datetime.today().date()

    for offset in range(window_days):
        d = today + timedelta(days=offset)
        iso = d.strftime("%Y-%m-%d")
        url = base_url.format(date=iso)
        try:
            resp = requests.get(url, headers=headers, timeout=12)
            resp.raise_for_status()
            soup = BeautifulSoup(resp.text, "html.parser")
            # Symbol-Extraktion aus dem eingebetteten JSON
            symbols = set(re.findall(r'"symbol":"([A-Z.\-]+)"', soup.text))
            m7_today = sorted(sym for sym in symbols if sym in M7)
            if m7_today:
                # Firmennamen hübsch darstellen
                names = []
                for sym in m7_today:
                    name = TECH_FIRMEN.get(sym, sym)
                    if sym in ("GOOGL", "GOOG"):
                        name = "Alphabet"
                    names.append(name)
                names = sorted(set(names), key=names.index)  # Dedupe, Reihenfolge erhalten
                out.append({
                    "datum": iso,
                    "typ": "Earnings",
                    "text": f"Mega-Cap Earnings: {', '.join(names)}",
                    "index": "ALL"
                })
                if debug:
                    print(f"[Earnings] {iso}: {', '.join(m7_today)}")
        except Exception as e:
            if debug: print(f"[Earnings] Fehler {iso}: {e}")
            continue

    if debug: print(f"[Earnings] Mega-Cap Fenster {window_days} Tage → {len(out)} Einträge.")
    return out

# --- Jahresereignisse zusammenstellen ---

def fetch_fixed_events(year: int, include_minor_us_changes: bool=True, debug: bool=False) -> List[Dict[str, Any]]:
    events: List[Dict[str, Any]] = []

    # Zinsentscheide
    try:
        events += fetch_fomc(year, debug=debug)
    except Exception:
        if debug:
            print("[Events] fetch_fomc fehlgeschlagen")
    try:
        events += fetch_ecb(year, debug=debug)
    except Exception:
        if debug:
            print("[Events] fetch_ecb fehlgeschlagen")
    try:
        events += fetch_boj(year, debug=debug)
    except Exception:
        if debug:
            print("[Events] fetch_boj fehlgeschlagen")

    # Regeln (Hexensabbat, Rebalancing)
    try:
        events += rule_hexensabbat(year)
    except Exception:
        if debug:
            print("[Events] rule_hexensabbat fehlgeschlagen")
    try:
        events += rule_dax_rebalancing_after_hexensabbat(year)
    except Exception:
        if debug:
            print("[Events] rule_dax_rebalancing_after_hexensabbat fehlgeschlagen")

    # US-Jobdaten (NFP)
    try:
        events += rule_us_jobs(year)
    except Exception:
        if debug:
            print("[Events] rule_us_jobs fehlgeschlagen")

    # Offizielle Index-Termine
    try:
        events += fetch_deutsche_boerse_dax_reviews(year, debug=debug)
    except Exception:
        if debug:
            print("[Events] fetch_deutsche_boerse_dax_reviews fehlgeschlagen")
    try:
        events += fetch_stoxx_blue_chip_reviews(year, debug=debug)
    except Exception:
        if debug:
            print("[Events] fetch_stoxx_blue_chip_reviews fehlgeschlagen")
    try:
        events += fetch_spdji_changes(year, include_minor=include_minor_us_changes, debug=debug)
    except Exception:
        if debug:
            print("[Events] fetch_spdji_changes fehlgeschlagen")

    # NEU: Börsenfeiertage (US + EU/Xetra)
    try:
        events += fetch_market_holidays(year, debug=debug)
    except Exception:
        if debug:
            print("[Events] fetch_market_holidays fehlgeschlagen")

    return events


# --- CPI (US + DE) ---

US_CPI_FALLBACK_2025 = ["2025-09-11","2025-10-15","2025-11-13","2025-12-10"]

US_CPI_FALLBACK_2025 = ["2025-09-11","2025-10-15","2025-11-13","2025-12-10"]

US_CPI_FALLBACK_2025 = ["2025-09-11","2025-10-15","2025-11-13","2025-12-10"]

def fetch_cpi_events(debug: bool=False) -> List[Dict[str, Any]]:
    """
    US- und DE-CPI-Termine:
    - US via FRED (mit Fallback-Liste)
    - DE via Investing (Germany CPI YoY)
    Gefiltert auf ein sinnvolles Zeitfenster.
    """
    rows: List[Dict[str, Any]] = []
    today = date.today()
    horizon = today + timedelta(days=400)   # ~13 Monate in die Zukunft

    # ---- US: FRED ----
    try:
        fred_key = os.getenv("FRED_API_KEY") or FRED_API_KEY
        if fred_key:
            rel = _fred_get("releases", {"search_text": "Consumer Price Index"})
            rid = None
            if rel and rel.get("releases"):
                # Release, der wirklich "Consumer Price Index" heißt, bevorzugen
                rel["releases"].sort(
                    key=lambda x: (
                        x.get("name","").lower() != "consumer price index",
                        x.get("id",0)
                    )
                )
                rid = rel["releases"][0].get("id")
            if rid:
                dates = _fred_get("release/dates", {
                    "release_id": rid,
                    "include_release_dates_with_no_data": "true",
                })
                if dates and "release_dates" in dates:
                    for d in dates["release_dates"]:
                        ds = d.get("date")
                        if not ds:
                            continue
                        try:
                            dt = datetime.strptime(ds, "%Y-%m-%d").date()
                        except ValueError:
                            continue
                        if (today - timedelta(days=7)) <= dt <= horizon:
                            rows.append({
                                "datum": dt.strftime("%Y-%m-%d"),
                                "typ": "CPI",
                                "text": "US Verbraucherpreise (CPI)",
                                "index": "SP500",
                            })
        else:
            if debug:
                print("[CPI] FRED-API-Key fehlt – nutze US-Fallback.")
            for ds in US_CPI_FALLBACK_2025:
                dt = datetime.strptime(ds, "%Y-%m-%d").date()
                if (today - timedelta(days=7)) <= dt <= horizon:
                    rows.append({
                        "datum": ds,
                        "typ": "CPI",
                        "text": "US Verbraucherpreise (CPI)",
                        "index": "SP500",
                    })
    except Exception as e:
        if debug:
            print(f"[CPI] FRED-Fehler: {e} – nutze US-Fallback.")
        for ds in US_CPI_FALLBACK_2025:
            dt = datetime.strptime(ds, "%Y-%m-%d").date()
            if (today - timedelta(days=7)) <= dt <= horizon:
                rows.append({
                    "datum": ds,
                    "typ": "CPI",
                    "text": "US Verbraucherpreise (CPI)",
                    "index": "SP500",
                })

    # ---- DE: Investing (Germany CPI YoY) ----
    try:
        # window_days = (horizon - today).days wäre theoretisch flexibler,
        # 400 ist hier aber gleichwertig.
        rows += fetch_de_cpi_from_investing(window_days=400, debug=debug)
    except Exception as e:
        if debug:
            print(f"[CPI] Investing-DE-CPI-Fehler: {e}")

    # ---- Dedupe (Datum, Typ, Index) ----
    seen, out = set(), []
    for e in rows:
        k = (e.get("datum",""), e.get("typ",""), e.get("index",""))
        if k not in seen and e.get("datum"):
            seen.add(k)
            out.append(e)

    if debug:
        print(f"[CPI] Gesamt: {len(out)} Einträge.")
    return out



# --- PCE-Termine ---

def fetch_pce_events(debug: bool=False) -> List[Dict[str, Any]]:
    """
    US PCE: Veröffentlichungstermine der BEA („Personal Income and Outlays“)
    via FRED Release-Dates. Liefert nur Daten im sinnvollen Zeitfenster.
    """
    rows: List[Dict[str, Any]] = []
    today = date.today()
    horizon = today + timedelta(days=400)

    try:
        rel = _fred_get("releases", {"search_text": "Personal Income and Outlays"})
        rid = None
        if rel and rel.get("releases"):
            # nimm den Release mit passendem Namen
            rel["releases"].sort(key=lambda x: (x.get("name","").lower() != "personal income and outlays", x.get("id",0)))
            rid = rel["releases"][0].get("id")
        if rid:
            dates = _fred_get("release/dates", {
                "release_id": rid,
                "include_release_dates_with_no_data": "true",
            })
            if dates and "release_dates" in dates:
                for d in dates["release_dates"]:
                    ds = d.get("date")
                    if not ds:
                        continue
                    try:
                        dt = datetime.strptime(ds, "%Y-%m-%d").date()
                    except ValueError:
                        continue
                    if (today - timedelta(days=7)) <= dt <= horizon:
                        rows.append({
                            "datum": dt.strftime("%Y-%m-%d"),
                            "typ": "PCE",
                            "text": "US PCE (Personal Income & Outlays)",
                            "index": "SP500"
                        })
    except Exception as e:
        if debug: print(f"[PCE] FRED-Fehler: {e}")

    # Dedupe
    seen, out = set(), []
    for e in rows:
        k = (e["datum"], e["typ"], e.get("index",""))
        if k not in seen:
            seen.add(k); out.append(e)
    if debug: print(f"[PCE] Gesamt: {len(out)} Einträge.")
    return out

# --- US Shutdown / Continuing Resolution (CR) ---

def rule_us_shutdown_fy_start(year: int) -> List[Dict[str, Any]]:
    d = date(year, 10, 1)
    return [{
        "datum": d.strftime("%Y-%m-%d"),
        "typ": "US Shutdown",
        "text": "US Fiskaljahr beginnt – Shutdown-Risiko ohne Bewilligungen/CR",
        "index": "ALL"
    }]

def load_us_cr_deadlines(year: int) -> List[Dict[str, Any]]:
    """
    Liest optionale CSV/us_cr_deadlines.json:
    {
      "2025": ["2025-09-30", "2025-12-20"],
      "2026": ["2026-01-19"]
    }
    """
    path = os.path.join("CSV", "us_cr_deadlines.json")
    out: List[Dict[str, Any]] = []
    try:
        if os.path.exists(path):
            js = json.load(open(path, "r", encoding="utf-8"))
            for ds in js.get(str(year), []):
                # nur valide ISO-Daten übernehmen
                dt = datetime.strptime(ds, "%Y-%m-%d").date()
                out.append({
                    "datum": dt.strftime("%Y-%m-%d"),
                    "typ": "US Shutdown",
                    "text": "US CR läuft aus – Shutdown-Risiko",
                    "index": "ALL"
                })
    except Exception:
        pass
    return out

# --- Tages-Cache + Aggregation ---

def lade_oder_erstelle_ereignisse(debug: bool=False) -> List[Dict[str, Any]]:
    heute = datetime.today().date()
    pfad = os.path.join("ereignisse", f"events_{heute.isoformat()}.json")

    if os.path.exists(pfad):
        with open(pfad, "r", encoding="utf-8") as f:
            events = json.load(f)
        # >>> Sicherstellen, dass Shutdown/CR drin ist
        try:
            events += rule_us_shutdown_fy_start(heute.year)
            events += load_us_cr_deadlines(heute.year)
        except Exception:
            pass
        # Dedupe + zurück in Cache
        seen, out = set(), []
        for e in events:
            k = (e.get("datum",""), e.get("typ",""), e.get("index",""))
            if k not in seen and e.get("datum"):
                seen.add(k); out.append(e)
        with open(pfad, "w", encoding="utf-8") as f:
            json.dump(out, f, indent=2, ensure_ascii=False)
        return out

    os.makedirs("ereignisse", exist_ok=True)

    year = heute.year
    fixed = fetch_fixed_events(year, include_minor_us_changes=True, debug=debug)
    earnings_events = get_mega_cap_earnings_events(window_days=28, debug=debug)
    cpi_events = fetch_cpi_events(debug=debug)
    pce_events = fetch_pce_events(debug=debug)

    events: List[Dict[str, Any]] = fixed + earnings_events + cpi_events + pce_events

    # >>> US Shutdown/CR VOR dem Write hinzufügen
    try: events += rule_us_shutdown_fy_start(year)
    except Exception: pass
    try: events += load_us_cr_deadlines(year)
    except Exception: pass

    with open(pfad, "w", encoding="utf-8") as f:
        json.dump(events, f, indent=2, ensure_ascii=False)

    if debug: print(f"[Ereignisse] Gesamt: {len(events)} Events gespeichert ({pfad})")
    return events

# --- Bewertung: heute / morgen -> Ampel 3 ---

def bewerte_ampel_3(ereignisse: List[Dict[str, Any]], indexname: str):
    heute = datetime.today().date()
    morgen = heute + timedelta(days=1)

    # Prioritäten – Holiday/ EarlyClose bewusst NICHT auf rot gesetzt
    PRIO = {
        "CPI": 100, "PCE": 95, "US Jobs": 90, "FED": 80, "EZB": 80, "BoJ": 75,
        "US Shutdown": 70,
        "Hexensabbat": 60, "Rebalancing": 55, "Index Notice": 50, "Earnings": 30,

        # Nur für Sortierung, NICHT für Farbe
        "Holiday": 20, "EarlyClose": 20
    }

    # --- Relevanzprüfung ---
    def _relevant(ev):
        canon = _normalize_index(indexname)
        ev_idx = _normalize_index(ev.get("index", "ALL"))
        t = ev.get("typ")
        return (ev_idx == "ALL") or (ev_idx == canon) or (t in ("CPI","PCE"))

    # --- Formatierung ---
    def _fmt(ev, bullet):
        d = ev.get("datum","")
        txt = ev.get("text","(ohne Text)")
        return f"{bullet} {txt} ({d})"

    # --- Beste Events je Typ auswählen ---
    def _select(evlist, bullet):
        best = {}
        for ev in evlist:
            t = ev.get("typ","")
            if t not in best or PRIO.get(t,0) > PRIO.get(best[t].get("typ",""),0):
                best[t] = ev
        ordered = sorted(best.values(),
                         key=lambda e: PRIO.get(e.get("typ",""),0),
                         reverse=True)
        return "\n".join(_fmt(ev, bullet) for ev in ordered)

    # --- Events trennen: heute, 1–2 Tage vorher ---
    today_list, pre_list = [], []
    holiday_today, holiday_pre = [], []     # Sonderlisten

    for ev in ereignisse:
        try:
            d = datetime.strptime(ev["datum"], "%Y-%m-%d").date()
        except Exception:
            continue
        if not _relevant(ev):
            continue

        delta = (d - heute).days
        typ = ev.get("typ","")

        # Holiday/ EarlyClose separat erfassen
        if typ in ("Holiday", "EarlyClose"):
            if delta == 0:
                holiday_today.append(ev)
            elif delta in (1, 2):
                holiday_pre.append(ev)
            # wichtig: trotzdem weiter in today_list/pre_list prüfen,
            # ABER Holiday soll dort NICHT rot auslösen
            # → wir lassen sie bewusst NICHT in today_list/pre_list laufen
            continue

        # Normale harte Events
        if delta == 0:
            today_list.append(ev)
        elif delta in (1, 2):
            pre_list.append(ev)

    # --- FARBE ZUERST FÜR HARTE EVENTS ---
    if today_list:
        return "red", _select(today_list, "🔴")

    if pre_list:
        return "yellow", _select(pre_list, "🟠")

    # --- HOLIDAY-LOGIK ---
    # Nur Feiertage / EarlyClose (keine harten Events)
    if holiday_today:
        return "orange", _select(holiday_today, "🟠") \
            + "\n(Hinweis: Börse geschlossen / verkürzter Handel)"

    if holiday_pre:
        return "orange", _select(holiday_pre, "🟠") \
            + "\n(Hinweis: Bevorstehender Feiertag / verkürzter Handel)"

    # --- KEINE RELEVANTEN EVENTS ---
    return "#90EE90", "Kommentar: Keine marktrelevanten Ereignisse."


__all__ = ['lade_oder_erstelle_ereignisse', 'bewerte_ampel_3']
