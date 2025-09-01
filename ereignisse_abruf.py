# -*- coding: utf-8 -*-
"""
ereignisse_abruf.py
Kalender für HebelWatch (Ampel 3) mit:
- Jahresbasierte fixe Termine (Hexensabbat, DAX-Heuristik)
- Offizielle Fetcher (best effort) für DAX/ES50/SPDJI + Zinsentscheide
- Yahoo-Earnings (heute & morgen)
- Tages-Cache, Debug-Logging
"""

from __future__ import annotations
from bs4 import BeautifulSoup
import os
import json
import re
import requests
from datetime import datetime, timedelta, date
from typing import List, Dict, Any, Optional
#from HebelWatchv30 import is_market_open  # Hier den richtigen Import-Pfad verwenden


# --- Helpers (oben in der Datei) -----------------------------------


FRED_API_KEY = "ac24c6331bbe4bd92e5cc0ce443d4d2e"   # dein echter Key
TE_API_KEY   = "123456"                               # echter TE-Key (Token oder "user:pass")

def _fred_get(path, params):
    key = FRED_API_KEY
    if not key or requests is None:
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
    if not key or requests is None:
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
# --- Mini Fetch Helper für HTML-Seiten (für EZB/FOMC/DB/STOXX/SPDJI) ---
UA = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                    "(KHTML, like Gecko) Chrome/123 Safari/537.36"}

def _fetch(url: str, timeout: int = 12) -> Optional[str]:
    try:
        r = requests.get(url, headers=UA, timeout=timeout)
        r.raise_for_status()
        return r.text
    except Exception:
        return None
            


 
 
 #BoJ-Termine (Geldpolitik/YCC/Negativzins)   ---------------------------
 
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
            for m in re.finditer(r"\b(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Sept|Oct|Nov|Dec)\.?\s+\d{1,2},\s*%d\b" % year, soup.get_text(" ", strip=True)):
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
                m2 = re.search(r"(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Sept|Oct|Nov|Dec)\.?\s+\d{1,2}\s*[-–]\s*(\d{1,2}),\s*%d" % year, target_txt)
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

  
    
    

# --- Gesamte Schnittstelle (wird in lade_oder_erstelle_ereignisse() benutzt)


# ------------------------------------------------------------
# Index normalisieren
# ------------------------------------------------------------
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
    


# ------------------------------------------------------------
# Firmenliste für Earnings
# ------------------------------------------------------------
TECH_FIRMEN: Dict[str, str] = {
    "AAPL": "Apple", "MSFT": "Microsoft", "AMZN": "Amazon", "NVDA": "Nvidia",
    "GOOGL": "Alphabet", "META": "Meta Platforms", "TSLA": "Tesla", "ADBE": "Adobe",
    "INTC": "Intel", "AMD": "AMD", "CRM": "Salesforce", "IBM": "IBM",
    "SAP.DE": "SAP", "IFX.DE": "Infineon", "SIE.DE": "Siemens", "DTE.DE": "Deutsche Telekom",
    "ADS.DE": "Adidas", "ASML.AS": "ASML", "OR.PA": "L'Oréal", "MC.PA": "LVMH", "AIR.PA": "Airbus"
}

# ------------------------------------------------------------
# Regeln
# ------------------------------------------------------------
def _third_friday(y: int, m: int) -> date:
    d = date(y, m, 1)
    offset = (4 - d.weekday()) % 7  # Friday=4
    first_friday = d + timedelta(days=offset)
    return first_friday + timedelta(weeks=2)

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
                     "text": "DAX/MDAX-Rebalancing (heuristisch)", "index": "DAX"})
    return rows

# ------------------------------------------------------------
# Fetcher: Zinsentscheide (mit Fallback LISTEN wie in deiner alten Datei)
# ------------------------------------------------------------
ECB_FALLBACK_2025 = ["2025-01-23","2025-03-13","2025-04-10","2025-06-12",
                     "2025-07-17","2025-09-11","2025-10-30","2025-12-11"]

FOMC_FALLBACK_2025 = ["2025-01-29","2025-03-19","2025-05-07","2025-06-18",
                      "2025-07-30","2025-09-17","2025-11-05","2025-12-17"]

def fetch_fomc(year: int, debug: bool=False) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    html = _fetch("https://www.federalreserve.gov/monetarypolicy/fomccalendars.htm")
    if html and BeautifulSoup:
        soup = BeautifulSoup(html, "html.parser")
        for tag in soup.find_all(text=re.compile(rf"\b{year}\b")):
            m = re.search(r"([A-Za-z]+)\s+(\d{1,2})(?:–|-)?(\d{0,2}),\s*%d" % year, tag)
            if m:
                mm, dd = m.group(1), m.group(2)
                try:
                    d = datetime.strptime(f"{mm} {dd} {year}", "%B %d %Y").date()
                    rows.append({"datum": d.strftime("%Y-%m-%d"), "typ": "FED", "text": "FED-Zinsentscheid", "index": "ALL"})
                except Exception:
                    pass
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
            m = re.search(r"(\d{1,2})\s+([A-Za-z]+)\s+%d" % year, tag)
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

# ------------------------------------------------------------
# Fetcher: Indizes (best effort)
# ------------------------------------------------------------
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
                for m in re.finditer(r"(\d{1,2}\s+[A-Za-z]+\s+%d|\d{4}-\d{2}-\d{2})" % year, ctx):
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

# ------------------------------------------------------------
# Yahoo Earnings (heute & morgen)
# ------------------------------------------------------------
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

    if debug: print(f"[Earnings] Mega-Cap Fenster {window_days} Tage → {len(out)} Einträge.")
    return out


# ------------------------------------------------------------
# Jahresereignisse zusammenstellen
# ------------------------------------------------------------
def fetch_fixed_events(year: int, include_minor_us_changes: bool=True, debug: bool=False) -> List[Dict[str, Any]]:
    events: List[Dict[str, Any]] = []
    # Zinsentscheide (mit Fallbacks)
    try: events += fetch_fomc(year, debug=debug)
    except Exception: pass
    try: events += fetch_ecb(year, debug=debug)
    except Exception: pass
    
    # >>> NEU: BoJ <<<
    try: events += fetch_boj(year, debug=debug)
    except Exception: pass
    
    # Regeln
    events += rule_hexensabbat(year)
    events += rule_dax_rebalancing_after_hexensabbat(year)
    # Offizielle Index-Termine
    try: events += fetch_deutsche_boerse_dax_reviews(year, debug=debug)
    except Exception: pass
    try: events += fetch_stoxx_blue_chip_reviews(year, debug=debug)
    except Exception: pass
    try: events += fetch_spdji_changes(year, include_minor=include_minor_us_changes, debug=debug)
    except Exception: pass
    return events

# ------------------------------------------------------------
# CPI (US + DE) – robustes Scraping (best effort)
# ------------------------------------------------------------
# ------------------------------------------------------------
# CPI (US + DE) – robuste Version mit Fallbacks und Debug
# ------------------------------------------------------------


# --- Fallbacks für Notfälle (nur falls FRED/TE nicht verfügbar sind – optional erweiterbar)
US_CPI_FALLBACK_2025 = ["2025-09-11","2025-10-15","2025-11-13","2025-12-10"]

def fetch_cpi_events(debug: bool=False) -> List[Dict[str, Any]]:
    """US- und DE-CPI-Termine (US via FRED, DE via TradingEconomics) – gefiltert auf ein relevantes Zeitfenster."""
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
                rel["releases"].sort(key=lambda x: (x.get("name","").lower() != "consumer price index", x.get("id",0)))
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
                        # <<< wichtig: Zeitfenster-filter >>>
                        if (today - timedelta(days=7)) <= dt <= horizon:
                            rows.append({"datum": dt.strftime("%Y-%m-%d"),
                                         "typ": "CPI", "text": "US Verbraucherpreise (CPI)",
                                         "index": "SP500"})
        else:
            if debug: print("[CPI] FRED-API-Key fehlt – nutze US-Fallback.")
            for ds in US_CPI_FALLBACK_2025:
                dt = datetime.strptime(ds, "%Y-%m-%d").date()
                if (today - timedelta(days=7)) <= dt <= horizon:
                    rows.append({"datum": ds, "typ": "CPI",
                                 "text": "US Verbraucherpreise (CPI)", "index": "SP500"})
    except Exception as e:
        if debug: print(f"[CPI] FRED-Fehler: {e} – nutze US-Fallback.")
        for ds in US_CPI_FALLBACK_2025:
            dt = datetime.strptime(ds, "%Y-%m-%d").date()
            if (today - timedelta(days=7)) <= dt <= horizon:
                rows.append({"datum": ds, "typ": "CPI",
                             "text": "US Verbraucherpreise (CPI)", "index": "SP500"})

    # ---- DE: TradingEconomics ----
    try:
        te_key = os.getenv("TE_API_KEY") or TE_API_KEY
        if te_key:
            url = "https://api.tradingeconomics.com/calendar/country/germany?format=json"
            if ":" in te_key:
                auth = tuple(te_key.split(":", 1))
                r = requests.get(url, auth=auth, timeout=12)
            else:
                r = requests.get(f"{url}&c={te_key}", timeout=12)
            if r.ok:
                js = r.json()
                for it in js:
                    name = (it.get("Event") or it.get("Category") or "").lower()
                    if any(k in name for k in ("cpi","inflation")):
                        ds = (it.get("DateUtc") or it.get("Date") or "")[:10]
                        if not ds:
                            continue
                        dtry = None
                        for fmt in ("%Y-%m-%d", "%m/%d/%Y"):
                            try:
                                dtry = datetime.strptime(ds, fmt).date()
                                break
                            except ValueError:
                                continue
                        if dtry and (today - timedelta(days=7)) <= dtry <= horizon:
                            rows.append({"datum": dtry.strftime("%Y-%m-%d"),
                                         "typ": "CPI", "text": "DE Verbraucherpreise (VPI)",
                                         "index": "DAX"})
            elif debug:
                print(f"[CPI] TE HTTP {r.status_code} – DE CPI übersprungen.")
        elif debug:
            print("[CPI] TE-API-Key fehlt – DE CPI übersprungen.")
    except Exception as e:
        if debug: print(f"[CPI] TE-Fehler: {e} – DE CPI übersprungen.")

    # ---- Dedupe ----
    seen, out = set(), []
    for e in rows:
        k = (e["datum"], e["typ"], e.get("index",""))
        if k not in seen:
            seen.add(k); out.append(e)
    if debug: print(f"[CPI] Gesamt: {len(out)} Einträge.")
    return out





# ------------------------------------------------------------
# Tages-Cache + Aggregation
# ------------------------------------------------------------
def lade_oder_erstelle_ereignisse(debug: bool=False) -> List[Dict[str, Any]]:
    heute = datetime.today().date()
    pfad = os.path.join("ereignisse", f"events_{heute.isoformat()}.json")

    if os.path.exists(pfad):
        with open(pfad, "r", encoding="utf-8") as f:
            events = json.load(f)
        if debug: print(f"[Ereignisse] {len(events)} Events aus Cache geladen ({pfad})")
        return events

    os.makedirs("ereignisse", exist_ok=True)

    year = heute.year
    fixed = fetch_fixed_events(year, include_minor_us_changes=True, debug=debug)
    if debug: print(f"[Ereignisse] Feste Termine {year}: {len(fixed)} Einträge.")

    earnings_events = get_mega_cap_earnings_events(window_days=28, debug=debug)


    if debug: print(f"[Ereignisse] Earnings-Events: {len(earnings_events)} Einträge.")

# NEU: CPI einsammeln
    cpi_events = fetch_cpi_events(debug=debug)  # <— NEU
    events: List[Dict[str, Any]] = fixed + earnings_events + cpi_events

    with open(pfad, "w", encoding="utf-8") as f:
        json.dump(events, f, indent=2, ensure_ascii=False)

    if debug: print(f"[Ereignisse] Gesamt: {len(events)} Events gespeichert ({pfad})")
    return events

# ------------------------------------------------------------
# Bewertung: heute / morgen -> Ampel 3
# ------------------------------------------------------------
def bewerte_ampel_3(ereignisse: List[Dict[str, Any]], indexname: str):
    heute = datetime.today().date()
    morgen = heute + timedelta(days=1)
    rot = []
    gelb = []

    canon = _normalize_index(indexname)
    from LeverageLens import is_market_open     

    for ev in ereignisse:
        try:
            ev_datum = datetime.strptime(ev["datum"], "%Y-%m-%d").date()
        except Exception:
            continue

        ev_idx = _normalize_index(ev.get("index", "ALL"))

        relevant = (ev_idx == "ALL") or (ev_idx == canon) or (ev["typ"] == "CPI")
        if not relevant:
            continue

        if ev_datum == heute:
            rot.append(f"🔴 {ev.get('text','(ohne Text)')} ({ev_datum})")
        elif ev_datum == morgen:
            gelb.append(f"🟡 {ev.get('text','(ohne Text)')} ({ev_datum})")

    if rot:
        return "red", "\n".join(rot)
    elif gelb:
        return "yellow", "\n".join(gelb)
    else:
        market_status = is_market_open(indexname)  # Marktstatus abfragen
        return "#90EE90", f"Kommentar: Keine marktrelevanten Ereignisse. "
# {market_status}

__all__ = ['lade_oder_erstelle_ereignisse', 'bewerte_ampel_3']


# --- US-Börsenfeiertage (NYSE/Nasdaq) ---------------------------------------
from datetime import date, timedelta

def _nth_weekday_of_month(y, m, weekday, n):
    d = date(y, m, 1)
    offset = (weekday - d.weekday()) % 7
    return d + timedelta(days=offset + 7*(n-1))

def _last_weekday_of_month(y, m, weekday):
    # gehe auf den 1. des Folgemonats, 1 Tag zurück, dann zum gewünschten Wochentag
    if m == 12:
        d = date(y+1, 1, 1) - timedelta(days=1)
    else:
        d = date(y, m+1, 1) - timedelta(days=1)
    offset = (d.weekday() - weekday) % 7
    return d - timedelta(days=offset)

def _easter_sunday(y):
    # Anonymous Gregorian algorithm
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
    m = (a + 11*h + 22*l) // 451
    month = (h + l - 7*m + 114) // 31
    day = ((h + l - 7*m + 114) % 31) + 1
    return date(y, month, day)

def _observed_weekend(d: date) -> date:
    # NYSE-Regel: Samstag -> Freitag davor, Sonntag -> Montag danach
    if d.weekday() == 5:
        return d - timedelta(days=1)
    if d.weekday() == 6:
        return d + timedelta(days=1)
    return d

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
    _add(presidents,   "Presidents’ Day")
    _add(good_friday,  "Good Friday")
    _add(memorial,     "Memorial Day")
    _add(juneteenth,   "Juneteenth")
    _add(independence, "Independence Day")
    _add(labor,        "Labor Day")
    _add(thanksgiving, "Thanksgiving Day")
    _add(christmas,    "Christmas Day")

    out.sort(key=lambda x: x["datum"])
    return out



