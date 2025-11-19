# Hebelwatch Markus Jurina (markus@jurina.biz) 16.11.2025 v1.92
#Server Schalter 19.11.2025 04:21 Uhr
#Auto Updater
# AMpel kann Alarm auslösen
# Reihenfolge Miniampeln geändert (AMpel 4)
# neue Funktion Liquidität

required_modules = {
    "pandas": "pandas",
    "dash": "dash",
    "selenium": "selenium",
    "yfinance": "yfinance",
    "simpleaudio": "simpleaudio"
}

fehlende_module = []
try:
    import selenium
except ImportError:
    fehlende_module.append("selenium")

try:
    import yfinance
except ImportError:
    fehlende_module.append("yfinance")

# simpleaudio ist optional
try:
    import simpleaudio  # optional
    SIMPLEAUDIO_AVAILABLE = True
except ImportError:
    SIMPLEAUDIO_AVAILABLE = False



if fehlende_module:
    print("⚠️ Fehlende Module erkannt:")
    for m in fehlende_module:
        print(" –", m)
    print("\nBitte installiere sie mit:")
    print("pip install " + " ".join(fehlende_module))

# Programmstart

import csv
import time
import pandas as pd
from bs4 import BeautifulSoup
import plotly.graph_objs as go
import threading
import requests
from contextlib import contextmanager
from selenium import webdriver
from ereignisse_abruf import lade_oder_erstelle_ereignisse, bewerte_ampel_3
from ereignisse_abruf import compute_us_market_holidays
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.chrome.options import Options
import tempfile, atexit
from datetime import timedelta
import gc
from dash import html
import yfinance as yf
from functools import lru_cache
import math
import numpy as np
import pytz
import queue
from datetime import datetime
from contextlib import suppress
from threading import Lock
import re
import signal
import os, sys
import statistics
import json, time, re, pathlib
from typing import List, Dict, Tuple
from collections import deque, defaultdict
# --- Imports (einmalig oben) ---
from selenium.webdriver.common.by import By
FILE_LOCKS = defaultdict(Lock)
from dash import Dash, dcc, html, callback
from dash.dependencies import Output, Input, State
from concurrent.futures import ThreadPoolExecutor
import shutil, platform
import urllib.request
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
import datetime as dt
driver_pool = ThreadPoolExecutor(max_workers=2)  # Nur 2 gleichzeitige Driver
from selenium.common.exceptions import (
    StaleElementReferenceException,
    TimeoutException,
    NoSuchElementException,
    WebDriverException,
)
#VERSION_URL = "1"
###################### Demo Version? ####################
# Dax Variante                                     ==True
# Vollversion alle Indizes                         == False

#### EINGABE ##########
DEMO_DAX_ONLY = True
SERVER_VARIANT = True        # True = Handy/Server-Layout (schlank), False = Desktop, MAIN Zeile!
CURRENT_VERSION = "1.92"   ######Eingeben neue Nummer
# Wenn SERVER_VARIANT aktiv → Dax true und Server true setzen

if SERVER_VARIANT:
    SHOW_NEWS_INSTEAD_OF_COMMENT = False

#######################
# der Code
if DEMO_DAX_ONLY:
    # Vollversion (alle Indizes)
    VERSION_URL = "https://jurina.biz/leverage-lens/version_dax.json"
else:
    # DAX-Variante
    VERSION_URL = "https://jurina.biz/leverage-lens/version_full.json"

import update_module
update_module.VERSION_URL = VERSION_URL
update_module.CURRENT_VERSION = CURRENT_VERSION
#########################





os.environ["ABSEIL_LOGGING_STDERR_THRESHOLD"] = "3"   # nur Errors
os.environ["GLOG_minloglevel"] = "3"
os.environ["NO_AT_BRIDGE"] = "1"  # weniger GTK-Warnungen
_FNG_RT = {"ts": 0, "val": None}
KEY_GLOBAL = "__global__"
DRIVERS: dict[str, "WebDriver"] = {}
DRIVER_LOCKS = defaultdict(threading.Lock)
import subprocess
try:
    import psutil  # pip install psutil
except ImportError:
    psutil = None
_DRIVERS = []
_SERVICES = []
_SERVICE_PIDS = []
SHUTTING_DOWN = False
# === RSI Schwellwerte ===
RSI_WARN = 65   # ab hier Orange
RSI_OVERBOUGHT = 70  # ab hier Rot
#-------------------

_US_HOLI = {"year": None, "dates": set()}
# --- Ampel 6: Index↔Vola Zusammenhang ---
# --- Ampel 6 (mind. 3 Punkte) ---
AMP6_MIN_POINTS   = 7       # Mindestanzahl Punkte ;3 springt
AMP6_MAX_AGE_SEC  = 600      # optionales Alters-Limit (z. B. 10 Min)
AMP6_MAX_LAG_SEC  = 30
AMP6_GREEN_TH     = 0.70
AMP6_ORANGE_TH    = 0.65

WAIT_BODY = 6
WAIT_READY = 2
POLL = 0.10
# Caches für ATR-Daten (Basis und aktuell)
_ATR_CACHE_BASE = {}   # {underlying: {"ts": epoch, "m": float}}  -> Baseline-Daten (z. B. 60-Tage ATR)
_ATR_CACHE_CURR = {}  
# Cache für RSI-Werte
_RSI_CACHE = {} 
_RSI_CACHE_TTL = 120 #sekunden
_last_csv_write = {"ts": 0}

_AMP5_RED_FLAG = False
from collections import defaultdict
_A1_RED_LATCH = defaultdict(lambda: False)  # pro Underlying: Rot bereits gemeldet?

_LEVER_CACHE = defaultdict(lambda: {"long": None, "short": None, "ts": 0})
_LEVER_TTL = 30  # Sekunden: Hebel gelten so lange als “frisch”
_lever_thread = None
## Testschalter für Ampel 5:= "off" | "very_low" | "very_high"
TEST_AMP5_FORCE = "off"

#Ziel: Ein globaler Lock um alle Yahoo-Finance-Aufrufe, damit EU-Index und US-Multi nie parallel feuern. Minimalinvasiv. Keine Logikänderung.
YF_CALL_LOCK = threading.RLock()  
WINDOW_MIN = 40
WINDOW = timedelta(minutes=40)
SLIDER_MIN_SPAN = timedelta(minutes=30)  
# Offene Investing-Seite + letzter gelesener Text
_INVEST_OPEN = {"u": None, "ts": 0}
_INVEST_LAST = {}  # z.B. {"Dax": {"txt": "+0.42%", "ts": 1731268800.0}}
STALE_REFRESH_SEC = 45  # nach 45 s ohne Textänderung -> Refresh
# Globale Selenium-Timeouts
WAIT_SHORT = 3     # schnelle Checks
WAIT_MED   = 6     # Standard
WAIT_LONG  = 10    # nur wo zwingend
POLL       = 0.25  # WebDriverWait poll_frequency


# Kurzname je Underlying für den Button
VOLA_SHORT = {
    "Dax": "VDAX",
    "EURO STOXX 50": "VSTOXX",
    "S&P 500": "VIX",
    "Dow Jones": "VXD",
    "Nasdaq 100": "VXN",
    "Nasdaq": "VXN",
}
def _vola_short(u: str) -> str:
    return VOLA_SHORT.get(u, "VIX")


_LAST_GOOD_FUT: dict[str, float] = {}  # underlying -> letzter gültiger Futures-%-Wert

def _is_valid_pct(v) -> bool:
    return isinstance(v, (int, float)) and math.isfinite(v) and v != 0.0 and abs(v) < 12.0

ISSUER_WHITELIST = [
    "HSBC",
    "Société Générale",
    "UBS",
    "DZ BANK",
    "BNP Paribas",
    "Vontobel",
]

def _issuer_match(txt: str) -> bool:
    if not txt: return False
    t = txt.lower().replace("é", "e")
    return any(s.lower().replace("é", "e") in t for s in ISSUER_WHITELIST)




ARIVA_URLS = {
    # jeweils: „Beides“ (Long+Short) – eine Seite
    "Dax":            "https://www.ariva.de/zertifikate/finder/index.m?go=1&zertart_id=7&calling_campaign_id=socgen-turbo_Produktzeile-Zertifikate_2023-11-14_00%3A00%3A00_2099-09-30_00%3A00%3A00&calling_emittent_id=7066#eq_za=7-1&eq_underlying_ag=290&eq_emittent_id=g_5&eq_emittent_id=g_9&eq_emittent_id=g_14&eq_emittent_id=e_19&eq_emittent_id=g_4&eq_emittent_id=g_8&min_laufzeit_ende=open-end&max_laufzeit_ende=open-end&min_k_leverage=1&max_k_leverage=300&eq_crypto=0&eq_only_actual=1&search_id=9baed78813166cd42ddd717d24adabb0",
    "S&P 500":        "https://www.ariva.de/zertifikate/finder/index.m?go=1&zertart_id=7&calling_campaign_id=socgen-turbo_Produktzeile-Zertifikate_2023-11-14_00%3A00%3A00_2099-09-30_00%3A00%3A00&calling_emittent_id=7066#eq_za=7-1&eq_underlying_ag=4152&eq_emittent_id=g_5&eq_emittent_id=g_9&eq_emittent_id=g_14&eq_emittent_id=e_19&eq_emittent_id=g_4&eq_emittent_id=g_8&min_laufzeit_ende=open-end&max_laufzeit_ende=open-end&min_k_leverage=1&max_k_leverage=300&eq_crypto=0&eq_only_actual=1&search_id=0e56a4e00ce1de35eaa235dec7a27930",
    "Dow Jones":      "https://www.ariva.de/zertifikate/finder/index.m?go=1&zertart_id=7&calling_campaign_id=socgen-turbo_Produktzeile-Zertifikate_2023-11-14_00%3A00%3A00_2099-09-30_00%3A00%3A00&calling_emittent_id=7066#eq_za=7-1&eq_underlying_ag=4325&eq_emittent_id=g_5&eq_emittent_id=g_9&eq_emittent_id=g_14&eq_emittent_id=e_19&eq_emittent_id=g_4&eq_emittent_id=g_8&min_laufzeit_ende=open-end&max_laufzeit_ende=open-end&min_k_leverage=1&max_k_leverage=300&eq_crypto=0&eq_only_actual=1&search_id=908506827ecb657e6dcb37ed13c50304",
    "Nasdaq 100":     "https://www.ariva.de/zertifikate/finder/index.m?go=1&zertart_id=7&calling_campaign_id=socgen-turbo_Produktzeile-Zertifikate_2023-11-14_00%3A00%3A00_2099-09-30_00%3A00%3A00&calling_emittent_id=7066#eq_za=7-1&eq_underlying_ag=5873&eq_emittent_id=g_5&eq_emittent_id=g_9&eq_emittent_id=g_14&eq_emittent_id=e_19&eq_emittent_id=g_4&eq_emittent_id=g_8&min_laufzeit_ende=open-end&max_laufzeit_ende=open-end&min_k_leverage=1&max_k_leverage=300&eq_crypto=0&eq_only_actual=1&search_id=a8a1f82833d16041aa45b946b333e5db",
}

_ARIVA_LEVER = {"ts": 0.0, "ttl": 8.0, "data": {}}
_ARIVA_LOCKS = defaultdict(threading.Lock)

# --- Ariva Futures: kleiner Cache ohne Rate-Limiter ---
_ARIVA_FUT = {"ts": {}, "val": {}, "ttl": 15}  # Sekunden
ARIVA_FUT_URL = {
    "Dax":           "https://www.ariva.de/dax-future-future",
    "EURO STOXX 50": "https://www.ariva.de/euro_stoxx_50-future-future",
    "S&P 500":       "",
    "Dow Jones":     "",
    "Nasdaq 100":    "",
}


INVEST_FUT_URL = {
    "Dax": "https://www.investing.com/indices/germany-30-futures",
    "EURO STOXX 50": "https://www.investing.com/indices/eu-stocks-50-futures",
    "S&P 500": "https://www.investing.com/indices/us-spx-500-futures",
    "Dow Jones": "https://de.investing.com/indices/us-30-futures",
    "Nasdaq 100": "https://www.investing.com/indices/nq-100-futures",
    "Nasdaq":     "https://www.investing.com/indices/nq-100-futures",
}

def _ensure_investing_open(underlying: str, max_age=300):
    url = INVEST_FUT_URL.get(underlying)
    if not url:
        return None
    d = get_driver("investing", scope=underlying)  # statt "general"
    cur = ""
    try:
        cur = (d.current_url or "").split("?", 1)[0]
    except Exception:
        pass
    need_nav = (_INVEST_OPEN["u"] != underlying) or (time.time() - _INVEST_OPEN["ts"] > max_age) or (url not in cur)
    if need_nav:
        d.get(url + f"?t={int(time.time())}")
        accept_cookies_if_present(d, timeout=WAIT_MED)
        _INVEST_OPEN.update({"u": underlying, "ts": time.time()})
    return d


#Ariva-Fetcher (ohne Domain-Limit)
def _ariva_future_change(underlying: str) -> float | None:
    url = ARIVA_FUT_URL.get(underlying)
    if not url:
        return None

    now = time.time()
    ts = _ARIVA_FUT["ts"].get(underlying, 0.0)
    if (now - ts) < _ARIVA_FUT["ttl"]:
        return _ARIVA_FUT["val"].get(underlying)

    try:
        headers = {
            "User-Agent": "Mozilla/5.0",
            "Accept-Language": "de-DE,de;q=0.9,en;q=0.8",
            "Cache-Control": "no-cache",
        }
        r = requests.get(url, headers=headers, timeout=6)
        if r.status_code != 200 or not r.text:
            return None

        soup = BeautifulSoup(r.text, "html.parser")
        txt = soup.get_text(" ", strip=True)
        m = re.search(r"([+\-]?\d+(?:[.,]\d+)?)\s?%", txt)
        if not m:
            return None
        val = float(m.group(1).replace(",", "."))

        _ARIVA_FUT["ts"][underlying] = now
        _ARIVA_FUT["val"][underlying] = val
        return val
    except Exception:
        return None




def _ariva_ttl():
    try:
        # Falls du eine Markt-Open-Funktion hast, nutze sie. Sonst fixe Werte.
        return max(6, int(refresh_interval))
    except Exception:
        return 8  # Default

_LONG_TOKENS  = ("long", "call", "bull", "+", "c")
_SHORT_TOKENS = ("short", "put",  "bear", "-", "p")

def _classify_direction(text: str) -> str | None:
    t = text.lower()
    if any(tok in t for tok in _LONG_TOKENS) and not any(tok in t for tok in _SHORT_TOKENS):
        return "LONG"
    if any(tok in t for tok in _SHORT_TOKENS) and not any(tok in t for tok in _LONG_TOKENS):
        return "SHORT"
    # Bei Konflikt: Präfixe bevorzugen
    if any(tok in t for tok in (" long", " long ", " bull", " call")):
        return "LONG"
    if any(tok in t for tok in (" short", " short ", " bear", " put")):
        return "SHORT"
    return None

def _extract_numbers(s: str) -> list[float]:
    out = []
    for tok in s.replace(",", ".").split():
        with suppress(ValueError):
            f = float(tok)
            if 1.0 <= f <= 200.0:
                out.append(f)
    return out

def _scrape_ariva_levers(underlying: str) -> tuple[list[float], list[float]]:
    url = ARIVA_URLS.get(underlying)
    if not url:
        print(f"❌ ARIVA_URL fehlt für {underlying}")
        return [], []

    # HTTP GET
    headers = {
        "User-Agent": "Mozilla/5.0",
        "Accept-Language": "de-DE,de;q=0.9,en;q=0.8",
        "Cache-Control": "no-cache",
    }
    try:
        resp = requests.get(url, headers=headers, timeout=10)
        if resp.status_code != 200 or not resp.text:
            print(f"❌ Ariva HTTP {resp.status_code} für {underlying}")
            return [], []
    except Exception as e:
        print(f"❌ Ariva Request-Fehler {underlying}: {e}")
        return [], []

    html = resp.text
    soup = BeautifulSoup(html, "html.parser")

    # Tabelle finden: nimm die größte Tabelle mit Zahlen in der Nähe von „Hebel“
    tables = soup.find_all("table")
    if not tables:
        print(f"⚠ Keine Tabelle auf Ariva-Seite gefunden: {underlying}")
        return [], []

    # Wähle die Tabelle mit den meisten <tr>
    table = max(tables, key=lambda tb: len(tb.find_all("tr")))
    long_vals, short_vals = [], []

    for tr in table.find_all("tr"):
        tds = tr.find_all("td")
        if not tds:
            continue
        row_text = " ".join(td.get_text(" ", strip=True) for td in tds)
        if not row_text:
            continue
        # Emittent-Whitelist
        if not _issuer_match(row_text):
            continue
        # Richtung bestimmen
        side = _classify_direction(row_text)
        if not side:
            continue
        # Hebel-Zahl(en)
        nums = _extract_numbers(row_text)
        if not nums:
            continue
        # nimm den plausibelsten Wert: Median
        nums.sort()
        val = nums[len(nums)//2]
        if side == "LONG":
            long_vals.append(val)
        else:
            short_vals.append(val)

    return long_vals, short_vals

def get_levers_from_ariva(underlying: str) -> tuple[list[float], list[float]]:
    now = time.time()
    ttl = _ariva_ttl()

    # Cache-Hit
    ent = _ARIVA_LEVER
    cached = ent["data"].get(underlying)
    if cached and (now - ent["ts"]) < ttl:
        return cached

    # Dedup pro Underlying
    lock = _ARIVA_LOCKS[underlying]
    with lock:
        # nach Lock nochmal prüfen
        cached = ent["data"].get(underlying)
        if cached and (now - ent["ts"]) < ttl:
            return cached

        long_vals, short_vals = _scrape_ariva_levers(underlying)
        ent["data"][underlying] = (long_vals, short_vals)
        ent["ts"] = now
        ent["ttl"] = ttl
        return long_vals, short_vals

def _future_label_for(u: str) -> str:
    mapping = {
        "Dax": "FDAX",
        "EURO STOXX 50": "FESX",
        "S&P 500": "E-Mini S&P 500",
        "Dow Jones": "YM",
        "Nasdaq 100": "E-Mini Nasdaq 100",
    }
    code = mapping.get(u, "")
    return f"Futures ({code}) einblenden" if code else "Futures einblenden"



################Browser blocken/Last reuduzieren
BLOCK_URLS_DEFAULT = [
    "*.png","*.jpg","*.jpeg","*.gif","*.webp","*.svg","*.ico",
    "*.css","*.woff*","*.ttf","*.otf",
    "*doubleclick*","*googletag*","*analytics*","*advert*","*video*","*youtube*","*vpaid*"
]


# --- Health/Watchdog ---
_STATE = {"last_beat": 0.0, "last_ok": 0.0}
_STATE_LOCK = threading.RLock()

def _beat(ok=False):
    t = time.time()
    with _STATE_LOCK:
        _STATE["last_beat"] = t
        if ok:
            _STATE["last_ok"] = t

def _read_health():
    with _STATE_LOCK:
        return _STATE["last_beat"], _STATE["last_ok"]

def _restart_update_stack():
    try:
        stop_update_thread(timeout=0.5)
    except Exception:
        pass
    try:
        start_update_thread()
    except Exception as e:
        print("⚠️ restart update_thread failed:", e)

def _watchdog_loop(max_stall_sec=45):
    while True:
        lb, _ = _read_health()
        if lb and (time.time() - lb) > max_stall_sec:
            print("⚠️ Watchdog: update_data stalled → restarting thread")
            _restart_update_stack()
        time.sleep(5)

def _nan_to_none(x):
    try:
        if x is None: return None
        if isinstance(x, float) and (math.isnan(x) or math.isinf(x)): return None
        return x
    except Exception:
        return None



###########MiniAmpel 4 Eurostoxx/Dax

# --- USA-Breite: stabile Vortagswerte ---
BREADTH_EPS = 0.05  # %: Änderungen kleiner ±0,05% werden ignoriert (Deadband)



def _yf_multi_daily_prevclose(symbols: list[str]) -> dict[str, float]:
    with YF_CALL_LOCK:
        df = yf.download(
            symbols, period="5d", interval="1d",
            auto_adjust=True, progress=False, group_by="ticker", threads=False
        )
    out = {}
    for s in symbols:
        try:
            dd = df[s]["Close"].dropna()
            # gestriger Schluss vs vorgestern → finale % Veränderung der *gestrigen* Session
            prev, prevprev = float(dd.iloc[-1]), float(dd.iloc[-2])
            if prevprev > 0:
                out[s] = (prev/prevprev - 1.0) * 100.0
        except Exception:
            pass
    return out


def _is_market_open_bool(market="USA"):
    now = datetime.now(TZ_BERLIN)
    if now.weekday() >= 5:
        return False
    o_ber, c_ber = market_window_local(market, now)
    return o_ber <= now <= c_ber


_US_BREADTH_CACHE = {"ts": 0.0, "avg": None, "date": None}

def _us_breadth_ttl_seconds() -> float:
    if not _is_market_open_bool("USA"):
        return 8*3600
    now = datetime.now(TZ_BERLIN)
    o_ber, _ = market_window_local("USA", now)
    since_open = max(0, (now - o_ber).total_seconds())
    base = refresh_interval
    return (1.5*base) if since_open < 120 else (2.5*base)


def get_us_breadth_avg(force=False) -> float | None:
    """Ø-%-Change aus S&P500, Dow, Nasdaq ggü. Vortag. Throttle gemäß Vorgabe."""
    now = time.time()
    ttl = _us_breadth_ttl_seconds()
    # Anti-Phasing: starte leicht versetzt
    if not force and (now - _US_BREADTH_CACHE["ts"]) < ttl:
        return _US_BREADTH_CACHE["avg"]

    # außerhalb US-Open: nur abrufen, wenn noch kein Wert für den Tag
    today = datetime.now(TZ_BERLIN).date()
    if not _is_market_open_bool("USA"):
        if _US_BREADTH_CACHE["date"] == today and _US_BREADTH_CACHE["avg"] is not None and not force:
            return _US_BREADTH_CACHE["avg"]

    syms = ("S&P 500", "Dow Jones", "Nasdaq 100")
    changes = []
    for u in syms:
        ch = get_us_index_change_cached(u)   # <<< Multi-Cache statt Einzelabruf
        if ch is not None:
            changes.append(float(ch))
    avg = (sum(changes)/len(changes)) if changes else None


    _US_BREADTH_CACHE.update({"ts": now + 0.33*refresh_interval, "avg": avg, "date": today})
    return avg

def miniampel_usa_breadth() -> tuple[str, str, str]:
    """
    Rückgabe: (emoji, farbname, text). Farben nur green/orange.
    Regel: Ø>0 → grün, sonst orange. Kein rot.
    """
    avg = get_us_breadth_avg()
    if avg is None:
        return "⚪", "gray", "USA-Breite: keine Daten"
    if avg > 0:
        return "🟢", "green", f"USA-Breite:Ø {avg:+.2f}% (S&P/Dow/Nasdaq 100)"
    else:
        return "🟠", "orange", f"USA-Breite: Ø {avg:+.2f}% (S&P/Dow/Nasdaq 100)"

def _ampel4_descriptor_for(u: str) -> str:
    if u in ("Dax", "EURO STOXX 50"):
        return "Erkennt: RSI (8 Tage) Überkauft -verkauft / USA-Börseneinfluss + - / US-Net-Liquidity: globaler Zentralbank-Liquid.indikator"
    return "Erkennt: RSI (8 Tage) Überkauft -verkauft / CNN Fear & Greed Index / US-Net-Liquidity: globaler Zentralbank-Liquid.indikator"

# --- Multi-Download Cache für US-Indizes (GSPC, DJI, NDX) ---
_YF_MULTI_US = {"ts": 0.0, "ttl": 30.0, "data": {}}  # data: {symbol: pct_change}
def _now_berlin(): return datetime.now(TZ_BERLIN)

def _us_multi_ttl():  # Abruf Ampel 4 USA Einfluss Zeitintervall
    """TTL für den Yahoo-Multiabruf (GSPC, DJI, NDX).
    Vor US-Open selten, während US-Session stabil am Haupt-Intervall,
    nach Handelsschluss sehr selten.
    """
    if _is_market_open_bool("USA"):
        # während US-Handel: nicht öfter als alle 30 s, aber am Haupt-Refresh ausgerichtet
        return max(20, int(refresh_interval * 2.5))
    else:
        # vor/nach Handel: selten (schont Yahoo)
        return 180.0



def _yf_pct_intraday_vs_prevclose_single(sym: str) -> float | None:
    try:
        sym = sym.lstrip("$").strip()
        with YF_CALL_LOCK:
            t = yf.Ticker(sym)

            # PrevClose bevorzugt fast_info
            prev = None
            try:
                fi = getattr(t, "fast_info", None)
                if fi is not None:
                    prev = _nan_to_none(getattr(fi, "previous_close", None))
                    if prev: prev = float(prev)
            except Exception:
                prev = None
            if not prev or prev <= 0:
                for days in ("2d", "5d", "10d"):
                    d = yf.download(sym, period=days, interval="1d",
                                    progress=False, auto_adjust=False)
                    if d is not None and not d.empty:
                        cc = d["Close"].dropna()
                        if len(cc) >= 2:
                            prev = float(cc.iloc[-2])
                            if prev > 0: break
            if not prev or prev <= 0:
                return None

            # Last aus 1m inkl. prepost
            last = None
            df1 = yf.download(sym, period="1d", interval="1m",
                              progress=False, auto_adjust=False, prepost=True)
            if df1 is not None and not df1.empty:
                c = df1["Close"].dropna()
                if len(c): last = float(c.iloc[-1])

            if last is None:
                fi = getattr(t, "fast_info", None)
                if fi is not None:
                    last = _nan_to_none(getattr(fi, "last_price", None)) or \
                           _nan_to_none(getattr(fi, "last_trade", None))
                    if last: last = float(last)

            if last and last > 0:
                return (last/prev - 1.0) * 100.0
    except Exception:
        return None
    return None



# --- Ampel-5 Feldgrenzen (Hebel) relativ zum Basishebel ----------------------
def _amp5_field_bounds(base_leverage: float, category: str) -> tuple[float, float]:
    """
    Liefert (lo, hi) für die zulässige Hebelspanne im aktiven Feld.
    Herleitung über r = x/m und Hebel ~ 1/r.
      very_low:      r < 0.60        -> hebel ∈ [base/0.60, LEVER_MAX]
      low:      0.60 ≤ r < 0.90      -> hebel ∈ [base/0.90, base/0.60]
      normal:   0.90 ≤ r ≤ 1.10      -> hebel ∈ [0.90*base, 1.10*base]   # Vorgabe
      elevated: 1.10 <  r ≤ 1.50     -> hebel ∈ [base/1.50, base/1.10]
      very_high:     r > 1.50        -> hebel ∈ [LEVER_MIN, base/1.50]
    """
    b = float(max(LEVER_MIN, min(base_leverage, LEVER_MAX)))
    cat = str(category or "off")
    if cat == "very_low":
        lo, hi = b / 0.60, LEVER_MAX
    elif cat == "low":
        lo, hi = b / 0.90, b / 0.60
    elif cat == "normal":
        lo, hi = 0.90 * b, 1.10 * b
    elif cat == "elevated":
        lo, hi = b / 1.50, b / 1.10
    elif cat == "very_high":
        lo, hi = LEVER_MIN, b / 1.50
    else:
        lo, hi = LEVER_MIN, LEVER_MAX
    # numerisch begrenzen
    lo = float(np.clip(lo, LEVER_MIN, LEVER_MAX))
    hi = float(np.clip(hi, LEVER_MIN, LEVER_MAX))
    if lo > hi:  # Sicherheitsnetz
        lo, hi = hi, lo
    # auf 0,5-Schritte runden

    lo = _lev_floor(lo)
    hi = _lev_ceil(hi)
    return lo, hi

def _clamp_leverage_to_field(base_leverage: float, category: str, value: float | None) -> float | None:
    if value is None:
        return None
    lo, hi = _amp5_field_bounds(base_leverage, category)
    v = float(value)
    if v < lo: v = lo
    elif v > hi: v = hi
    v = max(lo, min(v, hi))
    return _lev_step(v)


def _refresh_multi_us():
    syms = ["^GSPC","^DJI","^NDX"]
    if _is_market_open_bool("USA"):
        data = _yf_multi_intraday_vs_prevclose(syms)
    else:
        # Vor/Nach Handel: nur finale Vortagswerte, keine 1m-Drift
        data = _yf_multi_daily_prevclose(syms)
    _YF_MULTI_US["data"] = data
    _YF_MULTI_US["ts"]   = time.time()
    _YF_MULTI_US["ttl"]  = _us_multi_ttl()



def get_us_index_change_cached(underlying: str) -> float | None:
    """Einzelwert aus Multi-Cache holen. underlying ∈ {S&P 500, Dow Jones, Nasdaq}."""
    sym = YF_SYMBOL.get(underlying)
    if sym not in ("^GSPC","^DJI","^NDX"):
        return None
    now = time.time()
    # Cache gültig?
    if (now - _YF_MULTI_US["ts"]) < _YF_MULTI_US.get("ttl", 0):
        val = _YF_MULTI_US["data"].get(sym)
        return float(val) if val is not None else None
    # sonst neu laden
    try:
        _refresh_multi_us()
        val = _YF_MULTI_US["data"].get(sym)
        return float(val) if val is not None else None
    except Exception:
        # Fallback: kein Reload gelungen → letzter Wert falls vorhanden
        val = _YF_MULTI_US["data"].get(sym)
        return float(val) if val is not None else None


###########################

def _allow_eu_vola(now=None):
    now = now or datetime.now(TZ_BERLIN)
    return (now.hour > 9) or (now.hour == 9 and now.minute >= 31)

def _allow_us_vola(now=None):
    """Erlaubt Vola-Abruf ab US-Markteröffnung (14:31 oder 15:31 je nach Sommerzeit)."""
    now = now or datetime.now(TZ_BERLIN)

    # US-Zeit (Eastern Time) ableiten
    import pytz
    ny_tz = pytz.timezone("America/New_York")
    now_us = now.astimezone(ny_tz)

    # Handelsstart 09:30 Eastern Time → entspricht 14:30/15:30 Berlin je nach DST
    return (now_us.hour > 9) or (now_us.hour == 9 and now_us.minute >= 31)



_watchdog_thread = None
def start_watchdog():
    global _watchdog_thread
    if _watchdog_thread and _watchdog_thread.is_alive():
        return
    _watchdog_thread = threading.Thread(target=_watchdog_loop, name="watchdog", daemon=True)
    _watchdog_thread.start()



def _enable_cdp_blocking(driver, block_patterns=None):
    try:
        driver.execute_cdp_cmd("Network.enable", {})
        driver.execute_cdp_cmd("Network.setBlockedURLs", {
            "urls": block_patterns or BLOCK_URLS_DEFAULT
        })
    except Exception:
        pass


def _wait_body_present(drv, timeout_s=3.0):
    end = time.time() + timeout_s
    while time.time() < end:
        try:
            if drv.find_elements(By.TAG_NAME, "body"):
                return True
        except Exception:
            pass
        time.sleep(0.05)
    return False
    



# Cache für Volatilitäts-Bänder (absolute Tagesrenditen)
# Struktur: {underlying: {"ts": epoch, "bands": {0.85: float, 0.95: float}}}
_P80_BAND_CACHE = {}

def _get_band_pct(underlying: str, q: float, days: int = 40, ttl: int = 2*60*60) -> float | None:
    """
    Liefert das q-Quantil (z.B. 0.85 oder 0.95) der absoluten Tagesrenditen in %.
    85%- und 95%-Band werden immer gemeinsam aus einem Download berechnet
    und im Cache abgelegt.
    """
    now = time.time()
    ent = _P80_BAND_CACHE.get(underlying)

    # Cache-Hit
    if ent and now - ent.get("ts", 0) < ttl:
        bands = ent.get("bands") or {}
        v = bands.get(q)
        if v and v > 0:
            return v

    sym = (
        YF_SYMBOL.get(underlying)
        or YF_SYMBOL.get(underlying.upper())
        or YF_SYMBOL.get(underlying.title())
    )
    if not sym:
        if ent:
            bands = ent.get("bands") or {}
            return bands.get(q)
        return None

    try:
        df = yf.download(
            sym,
            period="400d",
            interval="1d",
            auto_adjust=False,
            progress=False,
            threads=False
        )
        if df is None or df.empty:
            if ent:
                bands = ent.get("bands") or {}
                return bands.get(q)
            return None

        close = df["Close"]
        if isinstance(close, pd.DataFrame):
            if len(close.columns) == 1:
                close = close.iloc[:, 0]
            else:
                close = close.squeeze()

        if not isinstance(close, pd.Series):
            if ent:
                bands = ent.get("bands") or {}
                return bands.get(q)
            return None

        close = pd.to_numeric(close, errors="coerce").dropna()
        if len(close) < 2:
            if ent:
                bands = ent.get("bands") or {}
                return bands.get(q)
            return None

        r_abs_pct = (close.pct_change().abs() * 100.0).dropna()
        if len(r_abs_pct) < days:
            if ent:
                bands = ent.get("bands") or {}
                return bands.get(q)
            return None

        r_abs_pct = r_abs_pct.tail(days)

        v85 = float(r_abs_pct.quantile(0.85))
        v95 = float(r_abs_pct.quantile(0.95))

        bands: dict[float, float] = {}
        if math.isfinite(v85) and v85 > 0:
            bands[0.85] = v85
        if math.isfinite(v95) and v95 > 0:
            bands[0.95] = v95

        if bands:
            _P80_BAND_CACHE[underlying] = {"ts": now, "bands": bands}
            return bands.get(q)

        # Kein neuer Wert, ggf. alten zurückgeben
        if ent:
            old_bands = ent.get("bands") or {}
            return old_bands.get(q)
        return None

    except Exception as e:
        print(f"get_band_pct({underlying}, q={q}) error:", e)
        if ent:
            bands = ent.get("bands") or {}
            return bands.get(q)
        return None


def get_p80_band_pct(underlying: str, days: int = 40, ttl: int = 2*60*60) -> float | None:
    """Kompatibilitäts-Wrapper für das 85%-Band."""
    return _get_band_pct(underlying, 0.85, days, ttl)


def get_p95_band_pct(underlying: str, days: int = 40, ttl: int = 2*60*60) -> float | None:
    """Neues 95%-Band (aus demselben Download wie das 85%-Band)."""
    return _get_band_pct(underlying, 0.95, days, ttl)

def _p80_text(u: str, current_index_change: float = None):
    """
    Zeigt 85%- und 95%-Band in einer Zeile.
    Jedes Band wird orange, sobald |Indexänderung| >= Bandwert.
    """
    v85 = get_p80_band_pct(u)
    v95 = get_p95_band_pct(u)

    parts = []

    # 85%-Band
    if v85 and v85 > 0:
        style85 = {}
        if current_index_change is not None and abs(current_index_change) >= 1.0 * v85:
            style85["color"] = "#FF8C00"
        parts.append(
            html.Span(f"85%-Band: ⌀ ±{v85:.2f}%", style=style85)
        )

    # 95%-Band direkt dahinter, gleiche Zeile
    if v95 and v95 > 0:
        style95 = {}
        if current_index_change is not None and abs(current_index_change) >= 1.0 * v95:
            style95["color"] = "#FF8C00"
        if parts:
            parts.append(html.Span(" | ", style={"margin": "0 6px"}))
        parts.append(
            html.Span(f"95%-Band: ⌀ ±{v95:.2f}%", style=style95)
        )

    if not parts:
        return ""

    # Wird in update_graph() ohnehin noch einmal in einen html.Span eingebettet
    return html.Span(parts)



def _find_text(drv, how, sel, timeout_s=2.0):
    end = time.time() + timeout_s
    while time.time() < end:
        try:
            els = drv.find_elements(how, sel)
            if els:
                txt = (els[0].text or els[0].get_attribute("textContent") or "").strip()
                if txt:
                    return txt
        except Exception:
            pass
        time.sleep(0.05)
    return ""

def read_until_change(drv, how, sel, old_text, max_s=2.0):
    end = time.time() + max_s
    while time.time() < end:
        txt = _find_text(drv, how, sel, timeout_s=0.3)
        if txt and txt != old_text:
            return txt
    return old_text


###############Ende Browser blocken


from selenium.webdriver.support import expected_conditions as EC



def close_finanzen_popups(driver, timeout=WAIT_MED):
    """Schließt Cookie-, Contentpass-, Cleverpush- und Google-Login-Popups auf finanzen.net."""
    try:
        driver.switch_to.default_content()
    except Exception:
        pass

    w = WebDriverWait(driver, timeout)

    # 1) OneTrust (Standard-Cookie-Banner)
    try:
        btns = driver.find_elements(By.ID, "onetrust-accept-btn-handler")
        if btns and btns[0].is_displayed():
            btns[0].click()
            time.sleep(0.3)
    except Exception:
        pass

    # 2) Contentpass/Cookie-Overlay (blauer Button "Alle akzeptieren")
    try:
        btns = driver.find_elements(
            By.CSS_SELECTOR,
            "button.message-component.message-button:nth-child(2)"
        )
        for b in btns:
            if b.is_displayed():
                b.click()
                time.sleep(0.3)
                raise StopIteration
    except StopIteration:
        pass
    except Exception:
        pass

    try:
        for xp in [
            "//button[contains(., 'Alle akzeptieren')]",
            "//button[contains(., 'ALLE AKZEPTIEREN')]",
            "//button[contains(., 'Akzeptieren')]",
        ]:
            els = driver.find_elements(By.XPATH, xp)
            for b in els:
                if b.is_displayed():
                    b.click()
                    time.sleep(0.3)
                    raise StopIteration
    except StopIteration:
        pass
    except Exception:
        pass

    # 3) Cleverpush-Benachrichtigung (Später entscheiden)
    try:
        els = driver.find_elements(
            By.CSS_SELECTOR,
            "button.cleverpush-confirm-btn.cleverpush-confirm-btn-deny"
        )
        for b in els:
            if b.is_displayed():
                b.click()
                time.sleep(0.3)
                break
    except Exception:
        pass

    # 4) Google-Login-Popup (X oben rechts)
    try:
        els = driver.find_elements(By.CSS_SELECTOR, "div#close.Tv9Dp-BZ11zc")
        for e in els:
            if e.is_displayed():
                e.click()
                time.sleep(0.3)
                return
    except Exception:
        pass

    # 5) Generische Dialog-Schließen-Buttons (Fallback)
    try:
        for sel in [
            "div[role='dialog'] button[aria-label='Schließen']",
            "div[role='dialog'] button.close",
            "button[aria-label='Schließen']",
        ]:
            els = driver.find_elements(By.CSS_SELECTOR, sel)
            for b in els:
                if b.is_displayed():
                    b.click()
                    time.sleep(0.2)
                    return
    except Exception:
        pass




def reset_cache_on_start_or_underlying_change(underlying: str):
    """Cache zurücksetzen und bei Bedarf neue Daten abrufen."""
    global _ATR_CACHE_BASE, _ATR_CACHE_CURR

    # Cache zurücksetzen
    _ATR_CACHE_BASE.clear()  # Löscht den Baseline-Cache
    _ATR_CACHE_CURR.clear()  # Löscht den aktuellen ATR-Cache

    # Neuberechnung der Daten für das gewählte Underlying
    get_baseline_data(underlying)
    get_current_data(underlying)
    
    print(f"Cache für {underlying} wurde zurückgesetzt und neu geladen.")

def get_baseline_data(underlying: str):
    """Lädt Baseline-Daten (z. B. 60-Tage-ATR) für das Underlying."""
    baseline = _get_baseline_m(underlying)  # Verwendung der _get_baseline_m-Funktion aus dem vorherigen Vorschlag
    if baseline:
        _ATR_CACHE_BASE[underlying] = {"ts": time.time(), "m": baseline}

def get_current_data(underlying: str):
    """Lädt die aktuellen Daten (z. B. 2-Tages-ATR) für das Underlying."""
    current = _get_current_x(underlying)  # Verwendung der _get_current_x-Funktion aus dem vorherigen Vorschlag
    if current:
        _ATR_CACHE_CURR[underlying] = {"ts": time.time(), "x": current}
# ------------------------------------------------------------
# Futures Sprungbestätigung (Double-Sample-Check)
# ------------------------------------------------------------
_FUTURE_VERIFY = {}

def _verify_future_value(underlying: str, new_val: float, threshold: float = 10.0) -> float | None:
    """
    Prüft große Sprünge. Ein Sprung > threshold % wird erst übernommen,
    wenn der nächste Abruf ihn bestätigt (zweiter Wert ±0.3 % gleich).
    Gibt None zurück, wenn noch unbestätigt.
    """
    if new_val is None or not isinstance(new_val, (int, float)):
        return None

    state = _FUTURE_VERIFY.setdefault(underlying, {"last": None, "pending": None})
    last = state["last"]

    # erster Wert → sofort übernehmen
    if last is None:
        state["last"] = new_val
        return new_val

    diff = abs(new_val - last)
    if diff <= threshold:
        # normaler kleiner Unterschied
        state["last"] = new_val
        state["pending"] = None
        return new_val

    # großer Sprung erkannt
    pend = state["pending"]
    if pend is None:
        # 1. Mal gesehen → vormerken, aber nicht übernehmen
        state["pending"] = new_val
        return None

    # 2. Mal gesehen → bestätigen, wenn ähnlich
    if abs(new_val - pend) <= 1.0:
        state["last"] = new_val
        state["pending"] = None
        return new_val
    else:
        # widersprüchlich → verwerfen
        state["pending"] = None
        return None


# ------------------------------------------------------------
# Ariva-basierte EU-Futures-Abfrage mit Sprung-Bestätigung
# ------------------------------------------------------------
def _eu_future_change_finanzen(underlying: str) -> float | None:
    """
    Liest die %-Änderung des DAX/Euro Stoxx 50-Futures über Ariva.
    Verwendet Sprung-Bestätigung, um Einzel-Ausreißer zu ignorieren.
    Fallback: Yahoo-Daten.
    """
    try:
        url = ARIVA_FUT_URL.get(underlying)
        if not url:
            return None

        headers = {

        "User-Agent": "Mozilla/5.0",
        "Accept": "text/html,application/xhtml+xml",
        "Accept-Language": "de-DE,de;q=0.9",
        "Cache-Control": "no-cache"
        }
        r = requests.get(url, headers=headers, timeout=6)
        if r.status_code in (403, 429):
            try:
                _ariva_backoff()
            except Exception:
                pass
            return None
        if r.status_code != 200 or not r.text:
            raise RuntimeError(f"Ariva HTTP {r.status_code}")

        soup = BeautifulSoup(r.text, "html.parser")
        box = soup.select_one("div.snapshotQuotesBox")
        if not box:
            raise RuntimeError("snapshotQuotesBox fehlt")

        # Prozentwert innerhalb des Headers extrahieren
        cand = box.select_one("td.last.colwin") or box.select_one("td.last")
        txt = (cand.get_text(" ", strip=True) if cand else "").replace("−", "-")
        m = re.search(r"([+\-]?\d[\d\.,]*)\s*%", txt)
        if not m:
            txt_box = box.get_text(" ", strip=True).replace("−", "-")
            m = re.search(r"([+\-]?\d[\d\.,]*)\s*%", txt_box)
        if not m:
            raise RuntimeError("kein Prozentwert gefunden")

        val_raw = float(m.group(1).replace(".", "").replace(",", "."))
        if not (-12.0 < val_raw < 12.0):
            raise RuntimeError(f"unplausibel: {val_raw}")

        # ---- Sprung-Verifikation anwenden ----
        val_verified = _verify_future_value(underlying, val_raw)
        if val_verified is not None:
            return val_verified

        # Sprung noch nicht bestätigt → letzten stabilen Wert anzeigen
        last_val = _FUTURE_VERIFY.get(underlying, {}).get("last")
        return last_val

    except Exception:
        # Fallback: Yahoo-Future
        try:
            y = _eu_future_change_yahoo(underlying)
            return float(y) if y is not None else None
        except Exception:
            return None


def _eu_future_change_yahoo(underlying: str) -> float | None:
    """Yahoo Finance Fallback für EU-Futures"""
    symbol_map = {
        "Dax": "FDAX=F",
        "EURO STOXX 50": "FESX=F"
    }
    
    sym = symbol_map.get(underlying)
    if not sym:
        return None
        
    try:
        with YF_CALL_LOCK:
            t = yf.Ticker(sym)
            # Verwende 5 Tage für robustere Daten
            data = t.history(period="5d", interval="1d")
            
            if data is None or len(data) < 2:
                return None
                
            # Letzter vs. vorletzter Schlusskurs
            if len(data) >= 2:
                prev = data["Close"].iloc[-2]
                curr = data["Close"].iloc[-1]
                if prev > 0:
                    return ((curr - prev) / prev) * 100.0
                    
    except Exception as e:
        print(f"⚠️ Yahoo Finance {underlying} Future Fehler: {e}")
        
    return None

def _eu_future_finanzen_selenium(url: str, underlying: str) -> float | None:
    """Selenium Fallback für Finanzen.net Futures"""
    try:
        driver = get_driver("general")
        driver.get(url)
        time.sleep(2)
        
        # Popups schließen
        close_finanzen_popups(driver)
        time.sleep(1)
        
        # Seite parsen
        html = driver.page_source
        soup = BeautifulSoup(html, 'html.parser')
        text = soup.get_text(" ", strip=True).replace("−", "-")
        
        # Prozentwert suchen
        match = re.search(r'([+-]?\d+[.,]\d+)\s*%', text)
        if match:
            value = float(match.group(1).replace(',', '.'))
            if -10 <= value <= 10:  # Plausibilitätscheck
                return value
                
    except Exception as e:
        print(f"⚠️ Selenium Fallback für {underlying} Future fehlgeschlagen: {e}")
    
    return None



    
# dämpft hebelberechnung live vola#####

def _live_push_and_median(underlying: str, abs_L_pct: float, now_ts: float | None = None) -> float:
    if now_ts is None:
        now_ts = time.time()
    dq = _LIVE_BUF[underlying]
    dq.append((now_ts, float(abs_L_pct)))
    cutoff = now_ts - _LIVE_WIN_SEC
    while dq and dq[0][0] < cutoff:
        dq.popleft()
    # Median der letzten ≤5 Min
    values = [v for _, v in dq] or [abs_L_pct]
    return float(statistics.median(values))
#####################


def _live_clear(underlying: str):
    _LIVE_BUF[underlying].clear()


def _us_holiday_dates(y):
    if _US_HOLI["year"] != y:
        ev = compute_us_market_holidays(y)
        _US_HOLI["year"] = y
        _US_HOLI["dates"] = {e["datum"] for e in ev}
    return _US_HOLI["dates"]



# === Zweistufiger Bestätigungsfilter (10%-Regel) ===
# === OneOutlierFilter: blockt nur den *ersten* Sprung > rel_thresh ===

from threading import Lock

def _is_num(x):
    return isinstance(x, (int, float)) and math.isfinite(x)

class OneOutlierFilter:
    def __init__(self, rel_thresh=0.80, big_thresh=0.90, small_blocks=1, big_blocks=2):
        self.rel_thresh = rel_thresh      # >10% = Sprung
        self.big_thresh = big_thresh      # >50% = sehr großer Sprung
        self.small_blocks = small_blocks  # normale Blockanzahl
        self.big_blocks = big_blocks      # Blockanzahl bei sehr großem Sprung
        self._last = None
        self._block_remaining = 0
        self._lock = Lock()

    def reset(self):
        with self._lock:
            self._last = None
            self._block_remaining = 0
            
    def last(self):
        with self._lock:
            return self._last


    def update(self, x):
            with self._lock:
             if not _is_num(x):
                 return self._last

             if self._last is None:
                 self._last = x
                 self._block_remaining = 0
                 return x

        # Änderung in %-Punkten
             abs_change = abs(x - self._last)

        # >>> NEU: kleine Änderungen immer akzeptieren <<<
             if abs_change < 0.02:   # Grenze = 0.02 %-Punkte
                 self._last = x
                 self._block_remaining = 0
                 return x

             base = max(0.30, abs(self._last))   # Mindestbasis 0.30 % statt fast 0
             rel = abs_change / base
             is_jump = rel > self.rel_thresh

             if self._block_remaining > 0:
                 self._last = x
                 self._block_remaining -= 1
                 return None

             if is_jump:
                 self._block_remaining = self.big_blocks if rel > self.big_thresh else self.small_blocks
                 self._last = x
                 return None

             self._last = x
             self._block_remaining = 0
             return x



# Instanzen
LEVER_LONG_FILTER  = OneOutlierFilter(rel_thresh=0.10)
LEVER_SHORT_FILTER = OneOutlierFilter(rel_thresh=0.10)
VOL_FILTER   = OneOutlierFilter(rel_thresh=0.10, big_thresh=0.50, small_blocks=1, big_blocks=1)
INDEX_FILTER = OneOutlierFilter(rel_thresh=0.30, big_thresh=1.00, small_blocks=1, big_blocks=1)
#Filter Sprünge >50%, 2 ticks überspringen, danch übernehmen


def reset_jump_filters(_=None):
    LEVER_LONG_FILTER.reset()
    LEVER_SHORT_FILTER.reset()
    VOL_FILTER.reset()
    INDEX_FILTER.reset()



# Ersatz für get_driver(*args, headless=True)
def get_driver(use_case: str = "general", scope: str | None = None, headless: bool = True):
    """Hole oder erzeuge einen dedizierten Chrome-Driver je use_case[/scope]."""
    if SHUTTING_DOWN:
        raise RuntimeError("Shutdown in progress")
    key = use_case if scope is None else f"{use_case}_{scope}"

    # vorhandenen Pool-Treiber nehmen
    with _DRIVER_POOL_LOCK:
        drv = _DRIVER_POOL.get(key)
        if drv:
            try:
                _ = drv.title  # lebt noch?
                return drv
            except Exception:
                try: drv.quit()
                except Exception: pass
                _DRIVER_POOL[key] = None
                drv = None

    # neu erstellen
    drv = make_driver()  # nutzt deine bestehenden Optionen
    _enable_cdp_blocking(drv)
    with _DRIVER_POOL_LOCK:
        _DRIVER_POOL[key] = drv
        _DRIVERS.append(drv)
    return drv




######################chrome beenden####################

def signal_handler(sig, frame):
    """Behandelt System-Signale für ordnungsgemäßes Beenden."""
    print(f"\n🛑 Signal {sig} empfangen, beende Anwendung...")
    shutdown_all_drivers()
    sys.exit(0)




def request_shutdown():
    # 1) Flag setzen, damit nichts Neues mehr startet
    global SHUTTING_DOWN
    SHUTTING_DOWN = True

    # 2) Intervals/Ticker abschalten (siehe Callback unten)

    # 3) Cleanup sofort
    _cleanup()

def _cleanup():
    import subprocess, sys, shutil

    try:
        # alle bekannten Driver schließen
        for d in list(_DRIVERS):
            try:
                d.quit()
            except:
                pass

        # auch Pool-Driver schließen
        for k, d in list(_DRIVER_POOL.items()):
            if d:
                try:
                    d.quit()
                except:
                    pass
                _DRIVER_POOL[k] = None

        # Services stoppen
        for s in list(_SERVICES):
            try:
                if getattr(s, "stop", None):
                    s.stop()
                if getattr(s, "process", None):
                    try:
                        s.process.terminate()
                    except:
                        pass
            except:
                pass

    finally:
        # tmp-Profile löschen
        try:
            if '_TMP_PROFILE_DIR' in globals() and _TMP_PROFILE_DIR:
                shutil.rmtree(_TMP_PROFILE_DIR, ignore_errors=True)
        except:
            pass

        # Harte Säuberung nach Plattform
        if sys.platform.startswith("win"):
            for im in ("chromedriver.exe", "chrome.exe"):
                try:
                    subprocess.run(
                        ["taskkill", "/F", "/IM", im, "/T"],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
                    )
                except:
                    pass
        else:
            for name in (
                "chromedriver",
                "chrome",
                "google-chrome",
                "chrome_crashpad_handler"
            ):
                try:
                    subprocess.run(
                        ["pkill", "-9", "-f", name],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
                    )
                except:
                    pass


def _signal_handler(sig, frame):
    """Behandelt System-Signale für ordnungsgemäßes Beenden."""
    print(f"\n🛑 Signal {sig} empfangen, beende Anwendung...")
    shutdown_all_drivers()
    # Zusätzlich: Alle Python-Threads beenden
    import os
    os._exit(0)  # Hartes Beenden falls nötig

# Signal-Handler registrieren
import signal
try:
    signal.signal(signal.SIGINT, _signal_handler)
    signal.signal(signal.SIGTERM, _signal_handler)
    if hasattr(signal, 'SIGBREAK'):
        signal.signal(signal.SIGBREAK, _signal_handler)
except Exception as e:
    print(f"⚠️ Signal-Handler konnte nicht registriert werden: {e}")

#ampel 1 statt pfeile die man schlecht sieht, farbig
def build_dir_badges(idx_pct, vola_pct, underlying=None):
    import dash.html as html
    if underlying is None:
        try:
            underlying = get_selected_underlying()
        except Exception:
            underlying = "Index"

    vola_name = _vola_short(underlying)  # statt _vola_name

    def chip(label, up=None):
        base = {
            "display": "inline-flex", "alignItems": "center", "gap": "6px",
            "padding": "2px 8px", "borderRadius": "8px", "border": "1px solid",
            "fontWeight": "600", "fontSize": "90%"
        }
        if up is True:
            base.update({"background": "#e6f5ec", "borderColor": "#0f7b3b", "color": "#0f7b3b"})
        elif up is False:
            base.update({"background": "#fdeaea", "borderColor": "#b42318", "color": "#b42318"})
        else:
            base.update({"background": "#eee", "borderColor": "#999", "color": "#444"})
        return html.Span(label, style=base)

    parts = []
    if idx_pct is not None:
        parts.append(
            chip(f"{underlying} {'↑↑' if idx_pct > 0 else '↓↓' if idx_pct < 0 else '→'}",
                 True if idx_pct > 0 else False if idx_pct < 0 else None)
        )
    if vola_pct is not None:
        parts.append(
            chip(f"{vola_name} {'↑↑' if vola_pct > 0 else '↓↓' if vola_pct < 0 else '→'}",
                 True if vola_pct > 0 else False if vola_pct < 0 else None)
        )
    return parts



TZ_BERLIN = pytz.timezone("Europe/Berlin")


# für Ampel 2 erweiterung########

# --- SOFR-Proxy (TED ersatz) --------------------------------------------------
FRED_API_KEY_FALLBACK = "c3c1ab19ea30ab27ddd6bcfcab4a86af"
_FRED_URL = "https://api.stlouisfed.org/fred/series/observations"
_SOFR_CACHE = {"ts": 0, "bps": None, "text": "SOFR-Proxy: keine Daten."}
_SOFR_CACHE_TTL = 900  # 30 Minuten Cache (da Tagesdaten)

def _fred_last(series_id, days=14):
    """Letzte gültige Beobachtung als float (% p.a.)."""
    import pandas as pd, datetime as _dt
    if not FRED_API_KEY:
        return None
    end = _dt.date.today()
    start = end - _dt.timedelta(days=days)
    p = {"series_id": series_id, "file_type": "json",
         "observation_start": start.isoformat(), "observation_end": end.isoformat(),
         "api_key": FRED_API_KEY}
    r = requests.get(_FRED_URL, params=p, timeout=15); r.raise_for_status()
    obs = r.json().get("observations", [])
    vals = [o.get("value") for o in obs if o.get("value") not in (".", None)]
    if not vals: return None
    try: return float(vals[-1])
    except: return None


def load_or_create_fred_api_key() -> str:
    path = os.path.join("CSV", "fred_api.txt")  # Ordner "CSV" wird extern verwaltet
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

# Umgebung > Datei > Fallback
FRED_API_KEY = os.getenv("FRED_API_KEY") or load_or_create_fred_api_key()


def find_text_retry(driver, locator: tuple[str, str], wait_s=10, retries=3):
    for _ in range(retries):
        try:
            el = WebDriverWait(driver, WAIT_MED).until(EC.visibility_of_element_located(locator))
            return el.text
        except StaleElementReferenceException:
            continue
    raise TimeoutException("stale after retries")

def cleanup_stale_processes():
    """Bereinigt alte Chrome/Chromedriver Prozesse beim Start."""
    print("🧹 Überprüfe auf verwaiste Prozesse...")


    
    if platform.system() == "Windows":
        commands = [
            ["taskkill", "/F", "/IM", "chromedriver.exe", "/T"],
            ["taskkill", "/F", "/IM", "chrome.exe", "/T"]
        ]
    else:
        commands = [
            ["pkill", "-9", "-f", "chromedriver"],
            ["pkill", "-9", "-f", "chrome"],
            ["pkill", "-9", "-f", "google-chrome"]
        ]
    
    for cmd in commands:
        try:
            subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=5)
        except Exception:
            pass



def _yf_multi_intraday_vs_prevclose(symbols: list[str]) -> dict[str, float]:
    """Liefert {symbol: pct_change} intraday vs. Vortagesschluss für verfügbare Symbole."""
    import pandas as pd
    # yfinance: Multi-Download mit 1 Request
    df_1m = yf.download(symbols, period="1d", interval="1m", auto_adjust=True, progress=False, group_by="ticker", threads=True)
    df_d  = yf.download(symbols, period="2d", interval="1d", auto_adjust=True, progress=False, group_by="ticker", threads=True)

    out = {}
    for s in symbols:
        try:
            d1 = df_1m[s]["Close"].dropna()
            dd = df_d[s]["Close"].dropna()
            if d1.empty or len(dd) < 2:
                continue
            last = float(d1.iloc[-1])
            prev = float(dd.iloc[-2])
            if prev <= 0:
                continue
            out[s] = (last/prev - 1.0) * 100.0
        except Exception:
            continue
    return out




def get_sofr_proxy_comment(cache_sec=900):
    """Gibt (bps:int, text:str). Cacht für cache_sec Sekunden."""

    now = time.time()
    
    # Cache prüfen (nur wenn nicht None und innerhalb TTL)
    if (now - _SOFR_CACHE["ts"] < _SOFR_CACHE_TTL and 
        _SOFR_CACHE["bps"] is not None and 
        _SOFR_CACHE["text"] is not None):
        return _SOFR_CACHE["bps"], _SOFR_CACHE["text"]

    # Neuen Wert abrufen
    sofr = _fred_last("SOFR")              # Overnight SOFR, % p.a.
    tb3m = _fred_last("DGS3MO") or _fred_last("TB3MS")  # 3M T-Bill, % p.a.
    
    if sofr is None or tb3m is None:
        # Fallback: letzten gültigen Wert verwenden falls vorhanden
        if _SOFR_CACHE["bps"] is not None:
            return _SOFR_CACHE["bps"], _SOFR_CACHE["text"]
        return (0, "SOFR-Proxy: keine Daten.")

    spread_pp = sofr - tb3m
    bps = int(round(spread_pp * 100))

    # Kategorie-Text gemäß Skala
    if abs(bps) > 100:
        txt = "Extrem (Systemkrise): >100 bps – Historisch nur in Krisen (2007 Bankenkrise bis 465 bps, Corona 2020 140 bps)."
    elif abs(bps) >= RSI_OVERBOUGHT:
        txt = "Kritisch (Liquiditätsstress): Banken leihen zögerlich. Meist Vorbote stärkerer Abverkäufe."
    elif abs(bps) >= 40:
        txt = "Erhöht (Interbankmarkt wird nervös): Frühwarnsignal für knapper werdende Liquidität."
    elif abs(bps) >= 10:
        txt = "Normalbereich (kein Stress): 10–40 bps – Typisch in ruhigen Marktphasen."
    else:
        txt = "Unter Normalbereich (<10 bps) – sehr ruhige Interbank-Lage"

    # Cache aktualisieren
    _SOFR_CACHE.update({"ts": now, "bps": bps, "text": txt})
    return bps, txt

# --- US Net Liquidity (WALCL - RRPONTSYD - WTREGEN, 30-Tage-Veränderung) ---#######
# : Miniampel „US-Net-Liquidity“ (inkl. Berechnung)
_US_NET_LIQ_CACHE = {
    "ts": 0.0,
    "delta": None,
    "color": "gray",
    "emoji": "⚪",
    "text": "US-Net-Liquidity: keine Daten."
}
_US_NET_LIQ_TTL = 86400  # 24h Cache, reicht da Tages-/Wochen-Daten


###elper: FRED-Serie als Zeitreihe
def _fred_series(series_id: str, days: int = 60):
    """Liefert Liste (date, float) der letzten Tage für eine FRED-Serie."""
    import datetime as _dt
    if not FRED_API_KEY:
        return []

    end = _dt.date.today()
    start = end - _dt.timedelta(days=days)
    p = {
        "series_id": series_id,
        "file_type": "json",
        "observation_start": start.isoformat(),
        "observation_end": end.isoformat(),
        "api_key": FRED_API_KEY,
    }
    try:
        r = requests.get(_FRED_URL, params=p, timeout=15)
        r.raise_for_status()
        obs = r.json().get("observations", [])
    except Exception:
        return []

    out = []
    for o in obs:
        val = o.get("value")
        if val in (".", None):
            continue
        date_str = o.get("date") or o.get("observation_date")
        if not date_str:
            continue
        try:
            d = _dt.date.fromisoformat(date_str[:10])
        except Exception:
            continue
        try:
            f = float(val)
        except Exception:
            continue
        out.append((d, f))

    out.sort(key=lambda t: t[0])
    return out


####Hauptfunktion: get_us_net_liquidity
def get_us_net_liquidity(cache_sec: int = _US_NET_LIQ_TTL):
    """
    Liefert (delta_pct, color_name, emoji, text) für US-Net-Liquidity.
    color_name ∈ {"green","orange","red","gray"}.
    """
    now_ts = time.time()
    c = _US_NET_LIQ_CACHE

    # Cache nutzen, wenn gültig
    if (now_ts - c["ts"] < cache_sec) and (c["delta"] is not None):
        return c["delta"], c["color"], c["emoji"], c["text"]

    # FRED-Daten holen (letzte ~60 Tage genügen)
    walcl = _fred_series("WALCL", days=60)
    rrp   = _fred_series("RRPONTSYD", days=60)
    tga   = _fred_series("WTREGEN", days=60)

    if not walcl or not rrp or not tga:
        # Fallback: Cache oder neutral
        if c["delta"] is not None:
            return c["delta"], c["color"], c["emoji"], c["text"]
        return 0.0, "gray", "⚪", "US-Net-Liquidity: keine Daten."

    from collections import defaultdict
    import datetime as _dt

    tmp = defaultdict(dict)
    for d, v in walcl:
        tmp[d]["walcl"] = v
    for d, v in rrp:
        tmp[d]["rrp"] = v
    for d, v in tga:
        tmp[d]["tga"] = v

    points = []
    for d, vals in tmp.items():
        if "walcl" in vals and "rrp" in vals and "tga" in vals:
            nl = vals["walcl"] - vals["rrp"] - vals["tga"]
            points.append((d, nl))

    points.sort(key=lambda t: t[0])
    if len(points) < 2:
        if c["delta"] is not None:
            return c["delta"], c["color"], c["emoji"], c["text"]
        return 0.0, "gray", "⚪", "US-Net-Liquidity: keine Daten."

    latest_date, latest_val = points[-1]
    cutoff = latest_date - _dt.timedelta(days=30)

    ref_candidates = [(d, v) for d, v in points if d <= cutoff]
    if ref_candidates:
        ref_date, ref_val = ref_candidates[-1]
    else:
        ref_date, ref_val = points[0]

    if not ref_val or ref_val == 0:
        if c["delta"] is not None:
            return c["delta"], c["color"], c["emoji"], c["text"]
        return 0.0, "gray", "⚪", "US-Net-Liquidity: keine Daten."

    delta_pct = (latest_val / ref_val - 1.0) * 100.0
    d = float(delta_pct)

    # Einordnung nach deiner Logik
    # Rot (3/3): ≤ -1,0 %  – Crash-Risikozone
    # Rot (2/3): ≤ -0,7 %  – Risiko deutlich erhöht
    # Orange:     < -0,3 % – erste Warnung
    # Grau:       -0,3 % bis +0,3 % – neutral
    # Grün:       > +1,0 % – Rückenwind

    if d <= -1.0:
        color_name = "red"
        emoji = "🔴"
        core = "Crash-Risikozone (3/3): oft 3–7 % Drawdown.Sell-the-rip! Buy-the-dip funktioniert nicht!"
    elif d <= -0.7:
        color_name = "red"
        emoji = "🔴"
        core = "Risiko (2/3) steigt: spürbare Verschlechterung.Sell-the-rip! Buy-the-dip funktioniert nicht!"
    elif d < -0.3:
        color_name = "orange"
        emoji = "🟠"
        core = "Risiko (1/3) steigt: leichte Schwäche.Hier ist Long möglich, aber stark eingeschränkt."
    elif d > 1.0:
        color_name = "green"
        emoji = "🟢"
        core = "Rückenwind: starke Risk-On-Phasen, Buy-the-dip funktioniert."
    elif -0.3 <= d <= 0.3:
        color_name = "gray"
        emoji = "⚪"
        core = "neutral: Markt reagiert kaum.Buy-the-dip funktioniert."
    else:
        # leicht positiv, aber noch kein Vollsignal
        color_name = "gray"
        emoji = "⚪"
        core = "leicht positiv, aber noch kein klares Signal."

    sign_fmt = f"{d:+.1f}".replace(".", ",")
    text = f"US-Net-Liquidity: {sign_fmt} % – {core}"

    _US_NET_LIQ_CACHE.update({
        "ts": now_ts,
        "delta": d,
        "color": color_name,
        "emoji": emoji,
        "text": text,
    })
    return d, color_name, emoji, text




# Manuelles Cache-Reset falls benötigt
def reset_sofr_cache():
    """Setzt den SOFR-Cache zurück"""
    global _SOFR_CACHE
    _SOFR_CACHE = {"ts": 0, "bps": None, "text": "SOFR-Proxy: keine Daten."}

def get_levers_from_onvista(current_underlying: str) -> tuple[list[float], list[float]]:
    key = f"onvista_{current_underlying}"
    lock = DRIVER_LOCKS[key]
    with lock:
        d = get_driver("onvista", current_underlying)

        def _read_table_text(timeout_s=2.0) -> str:
            txt = _find_text(d, By.CSS_SELECTOR, "table tbody", timeout_s)
            if txt: return txt
            txt = _find_text(d, By.CSS_SELECTOR, "table", 0.8)
            if txt: return txt
            txt = _find_text(d, By.XPATH, "(//table)[1]", 0.8)
            return txt or ""

        long_vals, short_vals = [], []

        # LONG
        try:
            _get_with_timeout(d, UNDERLYINGS[current_underlying]["long"] + f"&t={int(time.time())}", timeout_s=7)
            _wait_body_present(d, timeout_s=2.0)
            with suppress(Exception):
                close_onvista_popups(d, timeout=3)
            t = _read_table_text(2.0)
            long_vals = _parse_leverage_numbers(t) if t else []
        except Exception:
            pass

        # SHORT
        try:
            _get_with_timeout(d, UNDERLYINGS[current_underlying]["short"] + f"&t={int(time.time())}", timeout_s=7)
            _wait_body_present(d, timeout_s=2.0)
            with suppress(Exception):
                close_onvista_popups(d, timeout=3)
            t = _read_table_text(2.0)
            short_vals = _parse_leverage_numbers(t) if t else []
        except Exception:
            pass

        return long_vals, short_vals



################################################ariva anstelle onvista##################################################
def scrape_onvista_leverage(current_underlying: str) -> tuple[list[float], list[float]]:
    """
    Arriva-Backend:
    Holt Long/Short-Hebel über ARIVA_URLS (Beides) und trennt lokal.
    Beibehalt der Signatur für Kompatibilität.
    """
    try:
        long_vals, short_vals = get_levers_with_fallback(current_underlying)
        print(f"🔁 ARIVA {current_underlying}: long={len(long_vals)}, short={len(short_vals)}")
        return long_vals, short_vals
    except Exception as e:
        print(f"❌ ARIVA Fehler {current_underlying}: {e}")
        return [], []





def _release_drivers(keys: list[str]) -> int:
    """Entfernt/quit Driver aus dem Pool (mit Lock)."""
    n = 0
    with _DRIVER_POOL_LOCK:
        for k in keys:
            with suppress(Exception):
                d = _DRIVER_POOL.pop(k, None)
                if d:
                    d.quit()
                    n += 1
    return n

# -------- Lever-Source Fallback (Ariva -> Onvista) mit Hysterese --------

# Parameter für Stabilität
FAILS_BEFORE_SWITCH = 3       # so viele aufeinanderfolgende Fehlschläge bevor Quelle gewechselt wird
COOLDOWN_SEC        = 120     # mindestens 5 min bis zur nächsten Umschaltung
MIN_LEVERS_TOTAL    = 6       # minimale Anzahl gefundener Hebel (long+short), sonst "schlechter Datensatz"
PROBE_INTERVAL_SEC  = 120     # wie oft während Onvista-Aktivität Ariva testweise geprüft wird

# pro Underlying Zustand der Quelle
_LEVER_SRC = defaultdict(lambda: {
    "primary": "ariva",       # Wunschquelle
    "active":  "ariva",       # aktuell genutzt
    "fails":   0,             # aufeinanderfolgende Fehlschläge der aktiven Quelle
    "last_switch": 0.0,       # epoch der letzten Umschaltung
    "last_probe":  0.0,       # epoch der letzten Probe der Primärquelle
    "last_good":   ([], []),  # letzter guter Datensatz als Notausgabe
})

def _is_good_dataset(long_vals, short_vals) -> bool:
    try:
        n = (len(long_vals) if long_vals else 0) + (len(short_vals) if short_vals else 0)
        if n < MIN_LEVERS_TOTAL:
            return False
        # Plausibilität einzelner Werte
        for v in (long_vals or []) + (short_vals or []):
            if not isinstance(v, (int, float)) or not math.isfinite(v) or v < 1.0 or v > 300.0:
                return False
        return True
    except Exception:
        return False

def _fetch_from_source(source: str, underlying: str) -> tuple[list[float], list[float]]:
    if source == "ariva":
        return get_levers_from_ariva(underlying)
    elif source == "onvista":
        return get_levers_from_onvista(underlying)
    return [], []

def get_levers_with_fallback(underlying: str) -> tuple[list[float], list[float]]:
    st = _LEVER_SRC[underlying]
    now = time.time()

    # 1) Aktive Quelle versuchen
    long_vals, short_vals = _fetch_from_source(st["active"], underlying)
    if _is_good_dataset(long_vals, short_vals):
        st["fails"] = 0
        st["last_good"] = (long_vals, short_vals)
        return long_vals, short_vals

    # 2) aktiver Versuch war schlecht → Fail zählen
    st["fails"] += 1

    # 3) Umschalten nur, wenn Schwellwert + Cooldown erfüllt sind
    can_switch = (st["fails"] >= FAILS_BEFORE_SWITCH) and ((now - st["last_switch"]) >= COOLDOWN_SEC)

    if can_switch:
        new_src = "onvista" if st["active"] == "ariva" else "ariva"
        alt_long, alt_short = _fetch_from_source(new_src, underlying)
        if _is_good_dataset(alt_long, alt_short):
            st["active"] = new_src
            st["fails"] = 0
            st["last_switch"] = now
            st["last_good"] = (alt_long, alt_short)
            print(f"↔ Quelle gewechselt: {underlying} → {new_src.upper()}")
            return alt_long, alt_short
        else:
            # alternative Quelle auch schlecht → kein Flip-Flop, bleib bei aktiv
            st["last_switch"] = now  # Cooldown neu starten, um Pendeln zu vermeiden
            print(f"⚠ Alternative Quelle ebenfalls schlecht ({new_src}). Bleibe bei {st['active']}.")

    # 4) Wenn wir derzeit auf ONVISTA laufen, primäre Quelle ARIVA nur sporadisch „proben“
    if st["active"] == "onvista" and (now - st["last_probe"]) >= PROBE_INTERVAL_SEC:
        st["last_probe"] = now
        probe_long, probe_short = _fetch_from_source("ariva", underlying)
        if _is_good_dataset(probe_long, probe_short) and ((now - st["last_switch"]) >= COOLDOWN_SEC):
            st["active"] = "ariva"
            st["fails"] = 0
            st["last_switch"] = now
            st["last_good"] = (probe_long, probe_short)
            print(f"↔ Zurück auf ARIVA (Probe erfolgreich): {underlying}")
            return probe_long, probe_short

    # 5) Notausgabe: letzter guter Datensatz oder leer
    lg = st["last_good"]
    if _is_good_dataset(*lg):
        print(f"ℹ {underlying}: nutze last_good aus Cache (aktiv={st['active']}, fails={st['fails']})")
        return lg
    return long_vals or [], short_vals or []


def switch_underlying(new_underlying: str):
    global selected_underlying, stop_event, _volatility_cache

    old = selected_underlying

    # A) laufende Loops stoppen
    stop_update_thread(timeout=5)
    with suppress(Exception):
        stop_leverage_thread(timeout=5)  # falls vorhanden

    # B) alte Driver schließen
    reset_drivers_on_underlying_change(old_underlying=old)
    # EURO STOXX 50 – 'general' und spezifischen Key freigeben
    keys_to_release = ["general", f"general_{old}"]
    _release_drivers(keys_to_release)

    # C) neuen Zustand setzen + Filter auf NEUES Underlying
    set_selected_underlying(new_underlying)
    reset_jump_filters(new_underlying)
    reset_futures_filter(new_underlying)  # <-- vorher war hier das alte

    # D) Volatility-Cache leeren
    for k in list(_volatility_cache.keys()):
        _volatility_cache[k] = {"value": None, "ts": 0}

    # E) Memoized Caches leeren (wenn vorhanden)
    with suppress(Exception):
        scrape_average_leverage.cache_clear()

    # F) Threads neu starten
    if stop_event:
        stop_event.clear()
    start_update_thread()
    start_leverage_thread()

    
def get_vstoxx_change_onvista(timeout=10):
    """Liefert die %-Änderung des VSTOXX von OnVista. Bevorzugt den %-Text, nicht die Punkte."""
    try:
        
        from bs4 import BeautifulSoup

        url = "https://www.onvista.de/index/VSTOXX-Volatilitaetsindex-Index-12105800"
        r = requests.get(url, headers={"User-Agent":"Mozilla/5.0"}, timeout=timeout)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")

        # 1) Bevorzugt: Prozent direkt aus dem Text
        txt = soup.get_text(" ", strip=True).replace("−", "-")
        m = re.search(r"([+-]?\d+[.,]\d+)\s?%", txt)
        if m:
            val = float(m.group(1).replace(",", "."))
            if -30.0 <= val <= 30.0:
                return round(val, 2)

        # 2) Fallback: <data value="…">, aber nur, wenn der Kontext kein "Pkt" enthält
        for tag in soup.select("data[value]"):
            val_raw = (tag.get("value") or "").strip()
            if not val_raw:
                continue
            # Kontext prüfen
            ctx = (tag.parent.get_text(" ", strip=True) or "").lower()
            if "pkt" in ctx:
                continue  # Punkte-Chip, überspringen
            try:
                val = float(val_raw.replace(",", "."))
            except ValueError:
                continue
            if -30.0 <= val <= 30.0:
                return round(val, 2)

        return None
    except Exception as e:
        print("⚠️ get_vstoxx_change_onvista:", e)
        return None



def _read_pct_stable(drv, how, sel, tries=4, tol_pp=0.15, pause=0.15):
    last = None
    for _ in range(tries):
        txt = _find_text(drv, how, sel, timeout_s=0.8)
        val = _extract_percent(txt) if txt else None
        if val is None:
            time.sleep(pause); continue
        if last is None:
            last = val; time.sleep(pause); continue
        if abs(val - last) <= tol_pp:
            return round((val + last) / 2.0, 2)
        last = val; time.sleep(pause)
    return None

def _plausible_vstoxx(p):  # enger Rahmen verhindert Fehlgriffe
    return p is not None and -20.0 <= p <= 20.0

# === Helfer: Lesen im Kontext (Container-Element) ===
def _read_attr_in(ctx_el, how, sel, attr="value", to=1.2):
    end = time.time() + to
    while time.time() < end:
        try:
            els = ctx_el.find_elements(how, sel)
            if els:
                v = (els[0].get_attribute(attr) or "").strip()
                if v:
                    return v
        except Exception:
            pass
        time.sleep(0.05)
    return ""

def _read_text_in(ctx_el, how, sel, to=1.2):
    end = time.time() + to
    while time.time() < end:
        try:
            els = ctx_el.find_elements(how, sel)
            if els:
                txt = (els[0].text or els[0].get_attribute("textContent") or "").strip()
                if txt:
                    return txt
        except Exception:
            pass
        time.sleep(0.05)
    return ""


def get_vstoxx_change_stock3(timeout=12, retries=3):
    if DISABLE_STOCK3_VSTOXX:
        return None
    # ... bestehender Code ...

    




def _parse_vstoxx_value(driver):
    """
    Liest explizit den Prozentwert MIT Vorzeichen aus dem stock3-Prozentfeld.
    Gibt float oder None zurück.
    """
    try:
        el = driver.find_element(By.CSS_SELECTOR, "span.instrument-value.changePerc")
        raw = (el.text or el.get_attribute("data-inst-formatted") or "").strip()
        txt = raw.replace("\xa0", " ").replace("−", "-")
        m = re.search(r"([+\-]\d+(?:[.,]\d+)?)\s*%", txt)
        if not m:
            return None  # kein Vorzeichen → lieber Fallback (OnVista/Yahoo)
        return float(m.group(1).replace(",", "."))
    except Exception:
        return None



_SOUND_ENABLED = True
_SOUND_LOCK = Lock()
_APP_SHUTDOWN = False

#++++++++++++++++++++++++++ Für Kategorie Volatilität (1-5) und Hebel Vorschlag#######################

# --- ATR5%-Engine + Vola-Balken + Hebel-Autopilot ---------------------------
from zoneinfo import ZoneInfo
TZ = ZoneInfo("Europe/Berlin")

ATR_BASE_DAYS = 60          # Referenzfenster
ATR_INTERVAL  = "5m"        # 5-Minuten-Kerzen
ATR_EMA_SPAN  = 3           # Glättung über 3 Kerzen = 15 Min
LEVER_MIN, LEVER_MAX = 1.0, 30.0
BASE_LEVERAGE_DEFAULT = 6  # Startwert im UI und Fallback



# Kategorien relativ zum 30-T-Median m (x = aktueller ATR5% geglättet)
# r = x/m
VOLA_THRESH = {
    "very_low": 0.60,   # r < 0.60
    "low":      0.90,   # 0.60 ≤ r < 0.90
    "high":     1.10,   # 0.90 ≤ r ≤ 1.10  -> normal
    "very_high":1.50,   # 1.10 < r ≤ 1.50  -> erhöht
}                       # r > 1.50 -> sehr hoch

VOLA_COLORS = {
    "very_low":  "red",  # rot
    "low":       "#ffd84d",  # gelb
    "normal":    "#43a047",  # grün
    "elevated":  "#43a047",  # grün
    "very_high": "#ffd84d",  # gelb
    "off":       "#9e9e9e",
    
}

YF_SYMBOL = {
    "Dax": "^GDAXI",
    "EURO STOXX 50": "^STOXX50E",
    "S&P 500": "^GSPC",
    "Dow Jones": "^DJI",
    "Nasdaq 100": "^NDX",
}

FUT_SYMBOL = {
    "Dax": "FDAX=F",
    "EURO STOXX 50": "FESX=F",
    "S&P 500": "ES=F",
    "Dow Jones": "YM=F",
    "Nasdaq 100": "NQ=F",
}

FINANZEN_FUT_URL = {
    "Dax": "https://www.finanzen.net/futures/dax-future",
    "EURO STOXX 50": "https://www.finanzen.net/futures/euro-stoxx-50-future",
}


VOLA_DESCRIPTIONS = {
    "very_low": html.Span([
        html.Span("Ampel 5:", style={"fontWeight": "bold"}),
        " Volatilität unter 60% des Medians → Handel / Einstieg nicht empfohlen"
    ]),
    "low": html.Span([
        html.Span("Ampel 5:", style={"fontWeight": "bold"}),
        " 60-90% des Medians → unterdurchschn. Volatilität;",html.Br()," Es empfiehlt sich einen anderen Index anzuschauen"
    ]),
    "normal": html.Span([
        html.Span("Ampel 5:", style={"fontWeight": "bold"}),
        " 90-110% des Medians → typische Marktvolatilität"
    ]),
    "elevated": html.Span([
        html.Span("Ampel 5:", style={"fontWeight": "bold"}),
        " 110-150% des Medians → erhöhte Volatilität;" ,html.Br(),"Chancen steigen, Hebel prüfen"
    ]),
    "very_high": html.Span([
        html.Span("Ampel 5:", style={"fontWeight": "bold"}),
        " über 150% des Medians → extreme Volatilität,",html.Br()," Hebel anpassen und News prüfen"
    ]),
    "off": html.Span([
        html.Span("Ampel 5:", style={"fontWeight": "bold"}),
        " Keine Volatilitätsdaten verfügbar"
    ]),
}



_ATR_CACHE_BASE = {}   # {underlying: {"ts": epoch, "m": float}}
_ATR_CACHE_CURR = {}   # {underlying: {"ts": epoch, "x": float}}

def _trading_hours(underlying: str):
    if underlying in ("Dax", "EURO STOXX 50"):
        return ("09:00", "17:30")
    return ("15:30", "22:00")

def _to_berlin_index(idx):
    try:
        if idx.tz is None:
            return idx.tz_localize("UTC").tz_convert(TZ)
        return idx.tz_convert(TZ)
    except Exception:
        # falls naive lokale Zeit: als Berlin interpretieren
        return idx.tz_localize(TZ)

def _yf_5m(symbol: str, period: str) -> "pd.DataFrame":
    df = yf.download(symbol, period=period, interval=ATR_INTERVAL, auto_adjust=True, progress=False)
    if df is None or df.empty:
        return pd.DataFrame()
    df = df.rename(columns=str.title)
    df.index = _to_berlin_index(df.index)
    return df

def _filter_hours(df: "pd.DataFrame", underlying: str):
    if df.empty: return df
    start, end = _trading_hours(underlying)
    out = df.between_time(start, end)
    return out if not out.empty else df


def _atr5pct(df: pd.DataFrame):
    if df.empty: return pd.Series(dtype=float)
    o,h,l,c = df["Open"], df["High"], df["Low"], df["Close"]
    prev_c  = c.shift(1)
    tr = np.maximum(h-l, np.maximum((h - prev_c).abs(), (l - prev_c).abs()))
    atr = tr.ewm(span=14, adjust=False).mean()
    
    # KORREKTUR: In Prozent umwandeln (×100)
    atr_pct = (atr / c) * 100.0
    

    
    return atr_pct
    
INDEX_POOL = ["Dax","EURO STOXX 50","S&P 500","Dow Jones","Nasdaq 100"]
# --- Robust History Loader (fallback) ---
def _safe_read_history(u: str) -> pd.DataFrame:
    try:
        # Kandidaten-Pfade – passe an deine Struktur an
        for p in [f"history_{u}.csv", f"data/history_{u}.csv", f"./csv/{u}.csv"]:
            if os.path.exists(p):
                df = pd.read_csv(p)
                return df
    except Exception as e:
        print(f"⚠️ _safe_read_history({u}) failed: {e}")
    return pd.DataFrame()

def _load_history_any(u: str) -> pd.DataFrame:
    # 1) bevorzugt: load_history_clean
    try:
        return load_history_clean(u)  # wenn vorhanden
    except NameError:
        pass
    except Exception as e:
        print(f"⚠️ load_history_clean({u}) failed: {e}")

    # 2) alternative: load_history
    try:
        return load_history(u)  # falls es diese Funktion gibt
    except NameError:
        pass
    except Exception as e:
        print(f"⚠️ load_history({u}) failed: {e}")

    # 3) CSV-Fallback
    return _safe_read_history(u)



# 24h-TTL für Baseline
# ganz oben einmal:
BASELINE_TTL_SEC = 24*60*60
ATR_BASE_DAYS    = 60

def _get_baseline_m(underlying: str) -> float | None:
    now = time.time()
    ent = _ATR_CACHE_BASE.get(underlying, {})
    if ent and now - ent.get("ts", 0) < BASELINE_TTL_SEC:
        return ent.get("m")

    sym = YF_SYMBOL.get(underlying)
    if not sym:
        return ent.get("m")

    df = _yf_5m(sym, period=f"{ATR_BASE_DAYS}d")
    df = _filter_hours(df, underlying)
    atr_pct = _atr5pct(df)  # Serie mit ATR in %

    try:
        # robust auf 1D bringen
        if isinstance(atr_pct, pd.DataFrame):
            atr_pct = atr_pct.squeeze(axis=1)
        arr = np.asarray(atr_pct, dtype="float64").ravel()
        s = pd.Series(arr).replace([np.inf, -np.inf], np.nan).dropna()
        if s.empty:
            return ent.get("m")

        m = float(np.nanmedian(s.values))
        if math.isfinite(m) and m > 0:
            # DEBUG: ATR-Wert vor Cache
            print(f"🔍 _get_baseline_m({underlying}): Roh-ATR={m}, nach Cache={ent.get('m')}")
            
            _ATR_CACHE_BASE[underlying] = {"ts": now, "m": m}
            return m
        return ent.get("m")
    except Exception as e:
        print(f"baseline_m error: {e}")
        return ent.get("m")


def get_baseline_text(underlying: str) -> str:
    m = _get_baseline_m(underlying)
    return f"{m:.2f} %" if m and m > 0 else "—"


def _get_current_x(underlying: str) -> float | None:
    now = time.time()
    ent = _ATR_CACHE_CURR.get(underlying, {})
    if ent and now - ent.get("ts", 0) < 60:
        return ent.get("x")
    sym = YF_SYMBOL.get(underlying)
    if not sym: 
        return ent.get("x")
    df = _yf_5m(sym, period="2d")
    df = _filter_hours(df, underlying)
    atr_pct = _atr5pct(df)
    if atr_pct.empty:
        return ent.get("x")
    x = float(_to_scalar(atr_pct.ewm(span=ATR_EMA_SPAN, adjust=False).mean().iloc[-1]))
    
    # DEBUG: Current ATR Wert
    print(f"🔍 _get_current_x({underlying}): Current ATR = {x}%")
    
    _ATR_CACHE_CURR[underlying] = {"ts": now, "x": x}
    return x

def _mean_baseline_vola(exclude: str | None = None) -> float | None:
    """
    Durchschnittliche 30T-Baseline (Median ATR5%) über mehrere Underlyings.
    Nutzt _get_baseline_m(u). Ignoriert None/0.0 und optional 'exclude'.
    """
    # Universum bestimmen: erst YF_SYMBOL, sonst UNDERLYINGS, sonst Fallback-Liste
    try:
        universe = list(YF_SYMBOL.keys())
    except Exception:
        try:
            universe = list(UNDERLYINGS.keys())
        except Exception:
            universe = ["DAX", "EURO STOXX 50", "S&P 500", "Dow Jones", "Nasdaq 100"]

    vals = []
    for u2 in universe:
        if exclude and u2 == exclude:
            continue
        try:
            m2 = _get_baseline_m(u2)
            if m2 and m2 > 0:
                vals.append(float(m2))
        except Exception:
            pass

    if not vals:
        return None
    return float(np.nanmean(np.asarray(vals, dtype="float64")))


# --- Live-Bewegung (Index) für 60/40-Mix ---
_LM_CACHE = {}  # {underlying: {"ts": epoch, "pct": float}}

def _live_movement_pct(underlying: str) -> float:
    """Std der 1m-Returns über 10 Min, normiert auf Tagesmedian bis jetzt. → L_% (−..+)."""
    sym = YF_SYMBOL.get(underlying)
    if not sym:
        return 0.0
    tkr = yf.Ticker(sym)
    intra = tkr.history(period="1d", interval="1m")["Close"]
    if intra is None or intra.empty or len(intra) < 12:
        return 0.0
    ret = intra.pct_change()
    sig10 = ret.rolling(10, min_periods=10).std()
    s_t = float(sig10.iloc[-1]) if pd.notna(sig10.iloc[-1]) else 0.0
    med_today = float(sig10.iloc[:-1].median() if len(sig10) > 12 else sig10.median())
    med_today = max(med_today, 1e-6)
    if not math.isfinite(med_today) or med_today <= 0:
        return 0.0
    L_pct = (s_t / med_today) - 1.0
    return float(np.clip(L_pct, -0.60, 1.60))

def _recommend_leverage_eff(r_eff: float, base_leverage: float | None) -> float | None:
    """
    KORRIGIERT: Hebel indirekt proportional zur Volatilität
    - Bei hoher Vola (r_eff > 1) → niedrigerer Hebel
    - Bei niedriger Vola (r_eff < 1) → höherer Hebel
    """
    try:
        # Eingabevalidierung
        if (r_eff is None or not math.isfinite(r_eff) or r_eff <= 0):
            return None
            
        if base_leverage is None:
            base_leverage = BASE_LEVERAGE_DEFAULT
            
        base = max(LEVER_MIN, min(float(base_leverage), LEVER_MAX))
        
        # KORRIGIERT: Basishebel durch r_eff teilen (nicht multiplizieren)
        # r_eff > 1 = hohe Vola → niedrigerer Hebel
        # r_eff < 1 = niedrige Vola → höherer Hebel
        raw = base / float(r_eff)
        
        # Auf plausible Grenzen beschränken
        clipped = float(np.clip(raw, LEVER_MIN, LEVER_MAX))
        
        # Auf 0.5-Schritte runden
                # --- dynamische Rundung je nach Hebelbereich ---
        if clipped < 10:
            result = round(clipped * 20) / 20   # 0.05-Schritte unter 10x
        elif clipped < 20:
            result = round(clipped * 10) / 10   # 0.1-Schritte zwischen 10x und 20x
        else:
            result = round(clipped * 2) / 2     # 0.5-Schritte ab 20x

        
        print(f"🔍 Hebelberechnung: Basis={base}, r_eff={r_eff:.3f}, Raw={raw:.2f}, Result={result:.2f}")
        return result
        
    except Exception as e:
        print(f"⚠️ Fehler in _recommend_leverage_eff: {e}")
        return None




def _map_pct_to_level(pct: float) -> int:
    # pct ist z. B. +0.12 für +12 %
    if pct <= -0.30: return 1
    if pct <= -0.10: return 2
    if pct <= +0.10: return 3
    if pct <= +0.30: return 4
    return 5

def _level_to_category(lvl: int) -> str:
    return {1:"very_low", 2:"low", 3:"normal", 4:"elevated", 5:"very_high"}.get(int(lvl), "off")

def _get_live_movement_pct(underlying: str) -> float | None:
    """Intraday 'Speed' der Indexlinie: Std der 1m-Returns über 10 Min,
       normalisiert auf den heutigen Median bis jetzt. Liefert L_% (−..+)."""
    now = time.time()
    ent = _LM_CACHE.get(underlying, {})
    if ent and now - ent.get("ts", 0) < 20:
        return ent.get("pct")

    sym = YF_SYMBOL.get(underlying)
    if not sym: return None
    try:
        t = yf.Ticker(sym)
        intra = t.history(period="1d", interval="1m")["Close"]
        if intra is None or intra.empty or len(intra) < 12:
            return 0.0
        ret = intra.pct_change()
        sig = ret.rolling(10, min_periods=10).std()
        s_t = float(sig.iloc[-1]) if not math.isnan(sig.iloc[-1]) else 0.0
        med_today = float(sig.iloc[:-1].median() if len(sig) > 12 else sig.median())
        if not math.isfinite(med_today) or med_today <= 0:
            L_pct = 0.0
        else:
            L_pct = (s_t / med_today) - 1.0
        L_pct = float(np.clip(L_pct, -0.60, 1.60))
        _LM_CACHE[underlying] = {"ts": now, "pct": L_pct}
        return L_pct
    except Exception:
        return 0.0




def _categorize(x: float, m: float) -> str:
    if not x or not m or m <= 0: return "off"
    r = x / m
    if r < VOLA_THRESH["very_low"]:             return "very_low"
    if r < VOLA_THRESH["low"]:                  return "low"
    if r <= VOLA_THRESH["high"]:                return "normal"
    if r <= VOLA_THRESH["very_high"]:           return "elevated"
    return "very_high"



# Zuerst die build_vola_strip Funktion aktualisieren:
def _to_scalar(v):
    # wandelt 1-Element-Objekte sauber in float
    try:
        if hasattr(v, "item"):        # numpy scalar / 0-d array / pandas Scalar
            v = v.item()
        elif hasattr(v, "iloc"):       # 1-Element-Series/DataFrame
            v = v.iloc[0]  # This is the recommended approach
        # Additional check for single-element Series
        elif isinstance(v, pd.Series) and len(v) == 1:
            v = v.iloc[0]
    except Exception:
        pass
    return v


# Ampel 5 – Extra-Rot, wenn Empfehlung ≤ 45% des Basishebels
AMP5_RED_LEVER_RATIO = 0.45

def build_vola_strip(category: str, base_leverage: float, recommended_leverage) -> list:
    global _AMP5_RED_FLAG, TEST_AMP5_FORCE  # <-- für Alarm in update_graph

    labels = [("very_low","Sehr niedrig"), ("low","Niedrig"), ("normal","Normal"),
              ("elevated","Erhöht"), ("very_high","Sehr hoch")]
    segs = []

    base_leverage = _to_scalar(base_leverage)
    recommended_leverage = None if recommended_leverage is None else _to_scalar(recommended_leverage)

    def _is_critical_red(cat, base_lv, rec_lv):
        if cat != "very_high" or rec_lv is None or base_lv in (None, 0):
            return False
        try:
            return float(rec_lv) <= float(base_lv) * AMP5_RED_LEVER_RATIO
        except Exception:
            return False

    critical_red = _is_critical_red(category, base_leverage, recommended_leverage)

    # --- TESTOVERRIDE: Ampel 5 forcieren ---
    if TEST_AMP5_FORCE == "very_low":
        category = "very_low"
        critical_red = False
    elif TEST_AMP5_FORCE == "very_high":
        category = "very_high"
        critical_red = True        
        ##########################

    # --- Ampel-5-Alarmflag setzen: rot bei very_low ODER very_high+kritisch ---
    _AMP5_RED_FLAG = (category == "very_low") or (category == "very_high" and critical_red)  # :contentReference[oaicite:0]{index=0}

    for key, lab in labels:
        active = (key == category)
        bg_col  = VOLA_COLORS.get(key, "#eee") if active else "#eeeeee"
        brd_col = VOLA_COLORS.get(key, "#aaa") if active else "#cccccc"

        if active and key == "very_high" and critical_red:
            bg_col  = VOLA_COLORS["very_low"]   # gleiches Rot wie „sehr niedrig“
            brd_col = VOLA_COLORS["very_low"]

        border = f"2px solid {brd_col}" if active else "1px solid #cccccc"

        if active:
            if recommended_leverage is not None and recommended_leverage >= LEVER_MIN:
                try:
                    val_txt = f"{float(_to_scalar(recommended_leverage)):.2f}×"
                except Exception:
                    val_txt = "\u00A0"
            else:
                val_txt = "\u00A0"
        else:
            val_txt = "\u00A0"

        segs.append(html.Div([
            html.Div(lab,     style={"fontSize":"16px","fontWeight":"600","lineHeight":"1.05","minHeight":"18px"}),
            html.Div(val_txt, style={"fontSize":"16px","fontWeight":"600","lineHeight":"1.05","minHeight":"18px"})
        ], style={
            "flex":"0 0 84px",
            "display":"flex","flexDirection":"column","alignItems":"center","justifyContent":"center",
            "textAlign":"center","padding":"6px 4px",
            "backgroundColor": bg_col, "border": border, "borderRadius":"6px",
            "marginRight":"4px","minHeight":"48px"
        }))
    segs[-1].style["marginRight"] = "0px"
    return segs
    
    
###AMpel 6 Helfer###########

from collections import deque

def _pearson(a, b):
    a = np.asarray(a, float); b = np.asarray(b, float)
    if len(a) < 3 or len(b) < 3: return np.nan
    if np.std(a) == 0 or np.std(b) == 0: return np.nan
    return float(np.corrcoef(a, b)[0,1])

def _spearman(a, b):
    # Rang-Korrelation ohne SciPy
    a = np.asarray(a, float); b = np.asarray(b, float)
    if len(a) < 3 or len(b) < 3: return np.nan
    ra = pd.Series(a).rank(method="average").to_numpy()
    rb = pd.Series(b).rank(method="average").to_numpy()
    return _pearson(ra, rb)  # Pearson der Ränge = Spearman




    now = pd.Timestamp.now(tz=TZ_BERLIN)
    fresh = df[df["timestamp"] >= now - pd.Timedelta(seconds=AMP6_MAX_AGE_SEC)].sort_values("timestamp")
    if len(fresh) < AMP6_MIN_POINTS:
        fresh = df.sort_values("timestamp").tail(AMP6_MIN_POINTS)
    if len(fresh) < AMP6_MIN_POINTS:
        return 0.0, 0

    x = fresh["index_change"].astype(float).to_numpy()
    v = fresh["volatility_change"].astype(float).to_numpy()

    # Paare ohne NaN
    m = ~(np.isnan(x) | np.isnan(v))
    x, v = x[m], v[m]
    if len(x) < AMP6_MIN_POINTS:
        return 0.0, 0

    step_s = max(1, int(round(refresh_interval)))
    max_lag_steps = max(0, int(AMP6_MAX_LAG_SEC // step_s))

    best, best_lag = 0.0, 0
    for lag in range(0, max_lag_steps + 1):
        if lag == 0:
            x_, v_ = x, -v
        else:
            x_, v_ = x[lag:], -v[:-lag]
        if len(x_) >= AMP6_MIN_POINTS and len(v_) >= AMP6_MIN_POINTS:
            r = _spearman(x_, v_)
            if np.isfinite(r):
                s = abs(r)
                if s > best:
                    best, best_lag = s, lag * step_s
    return float(np.clip(best, 0.0, 1.0)), int(best_lag)



#######################




#++++++++++++++++++++++++++ ENDE Für Kategorie Volatilität (1-5) und Hebel Vorschlag#######################


def start_driver(headless=True):
    if _APP_SHUTDOWN:
        raise RuntimeError("App shutting down; no new drivers")

    global _DRIVER, _SERVICE
    if _DRIVER:
        return _DRIVER

    opts = webdriver.ChromeOptions()
    if headless: opts.add_argument("--headless=new")
    opts.add_experimental_option("detach", False)
    opts.add_argument("--disable-gpu")
    opts.add_argument("--log-level=2")
    # vermeidet „Geister“-Relaunches über OS-Optimierungen
    opts.add_argument("--disable-backgrounding-occluded-windows")
    opts.add_argument("--disable-renderer-backgrounding")

    service = Service(os.getenv("CHROMEDRIVER", "/usr/bin/chromedriver"))

    drv = webdriver.Chrome(service=service, options=opts)
    drv.set_page_load_timeout(20)
    drv.set_script_timeout(20)

    _DRIVER = drv
    _SERVICE = service
    try:
        _DRIVERS.append(drv); _SERVICES.append(service)
        if getattr(service, "process", None):
            _SERVICE_PIDS.append(service.process.pid)
    except Exception:
        pass
    return drv
    
###start schneller#####################
def warmup_drivers():
    with _DRIVER_POOL_LOCK:
        for key in ("onvista", "general", "investing"):
            if _DRIVER_POOL.get(key) is None:
                try:
                    drv = make_driver()
                    _enable_cdp_blocking(drv)
                    _DRIVER_POOL[key] = drv
                    _DRIVERS.append(drv)
                    print(f"✅ Driver '{key}' vorab gestartet")
                except Exception as e:
                    print(f"⚠️ Driver '{key}' Warmup-Fehler: {e}")


                    
                    
def warmup_requests():
    def _do():
        try:
            for u in ("Dax","EURO STOXX 50","S&P 500"):
                try:
                    get_index_data(u)
                except:
                    pass
                try:
                    get_volatility_change(u)
                except:
                    pass
                try:
                    scrape_average_leverage(UNDERLYINGS[u]["long"])
                except:
                    pass
        except Exception as e:
            print("⚠️ Warmup-Requests Fehler:", e)
    threading.Thread(target=_do, daemon=True).start()


###start schneller Ende#####################



def set_sound_enabled(val: bool):
    global _SOUND_ENABLED
    with _SOUND_LOCK:
        _SOUND_ENABLED = bool(val)

def is_sound_enabled() -> bool:
    with _SOUND_LOCK:
        return _SOUND_ENABLED
        

def atomic_write_csv(df, final_path: str, max_retries: int = 6):
    """Windows-sicher: Lock + Retry-Replace."""
    lock = FILE_LOCKS[final_path]
    with lock:
        dirpath = os.path.dirname(final_path) or "."
        basename = os.path.basename(final_path)
        fd, tmppath = tempfile.mkdtemp(prefix=basename + ".", dir=dirpath), None
        # wir erzeugen eine temp-Datei im tmp-Ordner und benennen sie dann um
        try:
            tmpfile = os.path.join(fd, basename + ".tmp")
            df.to_csv(tmpfile, index=False, encoding="utf-8", lineterminator="\n")
            # Replace mit Retry, falls Ziel kurz gelockt ist (Explorer/Leser)
            for i in range(max_retries):
                try:
                    os.replace(tmpfile, final_path)
                    break
                except PermissionError:
                    time.sleep(0.25 * (i + 1))
            else:
                raise PermissionError(f"Lock auf {final_path} blieb bestehen.")
        finally:
            # tmp-Ordner aufräumen
            try:
                if os.path.isdir(fd):
                    shutil.rmtree(fd, ignore_errors=True)
            except Exception:
                pass
        
def resource_path(rel_path: str) -> str:
    """liefert Pfade korrekt, egal ob im PyInstaller-Binary oder im normalen Python"""
    if hasattr(sys, "_MEIPASS"):
        return os.path.join(sys._MEIPASS, rel_path)
    return os.path.join(os.path.dirname(__file__), rel_path)        
    

# --- Alarm-Konfiguration ---
ALARM_FILE_SINGLE = os.path.join(os.path.dirname(__file__), "Alarm1.wav")
ALARM_FILE_BOTH   = os.path.join(os.path.dirname(__file__), "Alarm2.wav")
_last_alarm_state = None
ALARM_DURATION_SEC = 3

FONT_STACK = "Noto Sans, Segoe UI, Segoe UI Variable, Roboto, Helvetica Neue, Arial, Liberation Sans, system-ui, -apple-system, sans-serif"

### Starte Update nur in der Desktop-Variante #############
if not SERVER_VARIANT:
    update_module.check_update_later(delay_sec=10)
##################

# Initialize the app mit korrektem Asset-Pfad (für PyInstaller-Linux wichtig)
app = Dash(
    __name__,
    assets_folder=resource_path("assets"),
    assets_url_path="/assets"
)
# Globalen Font aus FONT_STACK überall anwenden
app.index_string = app.index_string.replace(
    "</head>",
    f"<style>body, div, span {{ font-family: {FONT_STACK}; }}</style></head>"
)


# -----------------------------------------------
# Konfiguration / Konstanten
# -----------------------------------------------
show_volatility = True
ampel1_text = "Standard Kommentar"
NEWS_REFRESH_SECONDS = 150
NEWS_TOTAL_ITEMS = 9
NEWS_PAGE_SIZE = 4
NEWS_SWITCH_EVERY_N_INTERVALS = 4
MARKET_TIMES = {
    "USA": {"start": {"hour": 15, "minute": 30}, "end": {"hour": 22, "minute": 0}},
    "EUROPE": {"start": {"hour": 9, "minute": 0}, "end": {"hour": 17, "minute": 30}},
}

# direkt UNTER MARKET_TIMES einfügen
HOLIDAYS_FIXED = {
    "EUROPE": {(1, 1), (12, 25), (12, 26)},   # Neujahr, 1./2. Weihnachtsfeiertag
    "USA":    {(1, 1), (7, 4),  (12, 25)},    # New Year, Independence Day, Christmas
}


def market_window_local(market: str, now_berlin: datetime | None = None):
    now_berlin = now_berlin or datetime.now(TZ_BERLIN)
    if market == "USA":
        tz_mkt = ZoneInfo("America/New_York")
        o = datetime(now_berlin.year, now_berlin.month, now_berlin.day, 9, 30, tzinfo=tz_mkt)
        c = datetime(now_berlin.year, now_berlin.month, now_berlin.day, 16, 0,  tzinfo=tz_mkt)
    else:  # EUROPE
        tz_mkt = ZoneInfo("Europe/Berlin")   # Xetra-Fenster
        o = datetime(now_berlin.year, now_berlin.month, now_berlin.day, 9, 0,  tzinfo=tz_mkt)
        c = datetime(now_berlin.year, now_berlin.month, now_berlin.day, 17, 30, tzinfo=tz_mkt)
    # nach Berlin transformieren
    o_ber = o.astimezone(TZ_BERLIN)
    c_ber = c.astimezone(TZ_BERLIN)
    return o_ber, c_ber

def is_market_open(underlying):
    tz = TZ_BERLIN
    now = datetime.now(tz)
    market = "USA" if underlying in ["Nasdaq 100", "S&P 500", "Dow Jones"] else "EUROPE"

    # Wochenende/Feiertage wie gehabt …
    # (bestehende Holiday-Blöcke unverändert lassen)

    o_ber, c_ber = market_window_local(market, now)
    market_hours = f"{o_ber.strftime('%H:%M')}-{c_ber.strftime('%H:%M')} Uhr MEZ/MESZ"
    if now.weekday() >= 5:
        return html.Span(f"❌ Börse geschlossen ({market_hours})", style={"fontSize": "16px"})
    # Feiertage prüfen wie bisher …

    return html.Span(
        f"{'✅ Börse geöffnet' if o_ber <= now <= c_ber else '❌ Börse geschlossen'} ({market_hours})",
        style={"fontSize": "16px"}
    )






# ==== WebDriver-Setup ====
_DRIVER_POOL = {
    "onvista": None,  # Driver ausschließlich für OnVista (Hebel-Scraping)
    "general": None   # Driver für alles andere (VDAX, VSTOXX, Finanztreff, etc.)
}
_DRIVER_POOL_LOCK = threading.Lock()
_TMP_PROFILE_DIR = None

def _make_chrome_options() -> Options:
    global _TMP_PROFILE_DIR
    _TMP_PROFILE_DIR = tempfile.mkdtemp(prefix=f"hebelwatch_profile_{time.time()}_")
    opts = Options()
    opts.add_argument("--lang=de-DE,de")
    opts.add_experimental_option("prefs", {"intl.accept_languages": "de,de_DE"})
    opts.add_experimental_option("prefs", {"intl.accept_languages": "de,de_DE"})
    opts.add_argument("--no-sandbox")
    opts.add_argument("--disable-dev-shm-usage")
    opts.add_argument(f"--user-data-dir={_TMP_PROFILE_DIR}")
    opts.add_argument("--headless=new")
    opts.add_argument("--disable-blink-features=AutomationControlled")
    opts.add_argument("--window-size=1280,900")
    opts.add_argument("--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36")
    opts.add_argument("--disable-gpu")
    opts.add_argument("--disable-software-rasterizer")
    opts.add_argument("--disable-logging")
    opts.add_argument("--log-level=3")
    opts.add_experimental_option('excludeSwitches', ['enable-logging'])
    return opts




def _find_chrome_binary() -> str:
    cand = [
        os.getenv("CHROME_BIN"),
        shutil.which("chromium"),
        shutil.which("chromium-browser"),
        shutil.which("google-chrome-stable"),
        shutil.which("google-chrome"),
        "/usr/bin/chromium", "/usr/bin/chromium-browser",
        "/usr/bin/google-chrome-stable", "/usr/bin/google-chrome",
    ]
    for p in cand:
        if p and os.path.exists(p):
            return p
    raise FileNotFoundError("Kein Chrome/Chromium gefunden – setze CHROME_BIN oder installiere chromium.")

def _find_chromedriver() -> str:
    cand = [os.getenv("CHROMEDRIVER"), shutil.which("chromedriver"), "/usr/bin/chromedriver"]
    for p in cand:
        if p and os.path.exists(p):
            return p
    raise FileNotFoundError("Kein chromedriver gefunden – setze CHROMEDRIVER oder installiere chromedriver.")

import os, shutil, platform
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.chrome.options import Options

def _find_chrome_win():
    cands = [
        os.getenv("CHROME_BIN"),
        r"C:\Program Files\Google\Chrome\Application\chrome.exe",
        r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",
    ]
    return next((p for p in cands if p and os.path.exists(p)), None)

def make_driver(headless=True):
    from selenium import webdriver
    from selenium.webdriver.chrome.service import Service
    import tempfile, os

    profile_dir = tempfile.mkdtemp(prefix="ll_chrome_")
    global _TMP_PROFILE_DIR
    _TMP_PROFILE_DIR = profile_dir

    options = webdriver.ChromeOptions()
    if headless:
        options.add_argument("--headless=new")
    options.add_argument("--mute-audio")
    options.add_argument("--blink-settings=imagesEnabled=false")
    options.add_argument(f"--user-data-dir={profile_dir}")
    options.add_argument("--disable-extensions")
    options.page_load_strategy = "eager"
    # Optional nur bei Bedarf:
    # options.add_argument("--no-sandbox")
    # options.add_argument("--disable-dev-shm-usage")

    prefs = {
        "profile.managed_default_content_settings.media_stream": 2,
        "profile.managed_default_content_settings.plugins": 2,
        "profile.default_content_setting_values.notifications": 2,
        "profile.managed_default_content_settings.videos": 2,
        "profile.default_content_setting_values.automatic_downloads": 2,
    }
    options.add_experimental_option("prefs", prefs)

    driver = webdriver.Chrome(service=Service(), options=options)
    try:
        _enable_cdp_blocking(driver)  # stelle sicher, dass die Blockliste nicht XHR zu Kursdaten trifft
    except Exception:
        pass
    return driver




def accept_cookies_if_present(d, timeout=WAIT_MED):
    WebDriverWait(d, timeout).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
    for how, sel in [
        (By.CSS_SELECTOR, "button#onetrust-accept-btn-handler"),
        (By.XPATH, "//button[contains(., 'Akzeptieren') or contains(., 'Zustimmen') or contains(., 'Accept All')]"),
        (By.XPATH, "//button[contains(@class,'consent') and (contains(.,'OK') or contains(.,'Akzeptieren'))]"),
    ]:
        try:
            btn = d.find_element(how, sel)
            if btn.is_displayed():
                btn.click(); time.sleep(0.6); break
        except Exception:
            pass

def _vola_name(u: str) -> str:
    return {
        "Dax": "VDAX",
        "EURO STOXX 50": "VSTOXX",
        "S&P 500": "VIX",
        "Dow Jones": "VXD",
        "Nasdaq 100": "VXN",
    }.get(u, "Vola")
#Hilfsfunktionen hinzufügen wegen rudnen ampel 5
def _lev_step(x: float) -> float:
    x = float(x)
    if x < 10:    return round(x * 20) / 20    # 0.05
    if x < 20:    return round(x * 10) / 10    # 0.1
    return round(x * 2) / 2                    # 0.5

def _lev_floor(x: float) -> float:
    x = float(x)
    if x < 10:    return math.floor(x * 20) / 20
    if x < 20:    return math.floor(x * 10) / 10
    return math.floor(x * 2) / 2

def _lev_ceil(x: float) -> float:
    x = float(x)
    if x < 10:    return math.ceil(x * 20) / 20
    if x < 20:    return math.ceil(x * 10) / 10
    return math.ceil(x * 2) / 2
#Hilfsfunktionen hinzufügen wegen rudnen ampel 5 ende

def clean_ticker(symbol):
    return symbol.replace("$", "").strip()



def safe_concat(dfs, **kwargs):
    cleaned = []
    for df in dfs:
        if df is None:
            continue
        if getattr(df, 'empty', True):
            continue
        # hat die Tabelle wenigstens irgendwo einen Nicht-NA-Wert?
        if not df.notna().any().any():
            continue
        cleaned.append(df)

    if not cleaned:
        # Leeres Ergebnis konsistent zurückgeben
        return pd.DataFrame()

    return pd.concat(cleaned, **kwargs)


# News
SHOW_NEWS_INSTEAD_OF_COMMENT = True
_news_cache = {"ts": 0, "items": []}

def get_top_news(max_items=9, cache_seconds=120):
    now = time.time()
    if now - _news_cache["ts"] < cache_seconds and _news_cache["items"]:
        return _news_cache["items"]
  # rss_url = "https://api.boerse-frankfurt.de/v1/feeds/news.rss"
   #rss_url = "https://www.tagesschau.de/wirtschaft/finanzen/index~rss2.xml"
    rss_url = "https://www.finanztreff.de/feed/marktberichte.rss"
    #rss_url = "https://api.boerse-frankfurt.de/v1/feeds/news.rss"
    try:
        r = requests.get(rss_url, timeout=10)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, 'lxml-xml')
        items = []
        for it in soup.find_all("item")[:max_items]:
            title = it.title.get_text(strip=True)
            link = it.link.get_text(strip=True)
            items.append((title, link))
        _news_cache["ts"] = now
        _news_cache["items"] = items
        return items
    except Exception as e:
        print(f"⚠️ Fehler beim Laden der News: {e}")
        return []

def get_news_block(page_index=0):
    cache_time = NEWS_REFRESH_SECONDS if page_index == 0 else 9999
    headlines = get_top_news(NEWS_TOTAL_ITEMS, cache_seconds=cache_time)
    if not headlines:
        return html.Div("Keine News verfügbar", style={"color": "#666"})

    last_ts = _news_cache.get("ts", 0)
    last_str = datetime.fromtimestamp(last_ts, tz=TZ_BERLIN).strftime("%H:%M:%S") if last_ts else "-"

    total = len(headlines)
    num_pages = max(1, math.ceil(total / NEWS_PAGE_SIZE))
    start = (page_index * NEWS_PAGE_SIZE) % total
    end = start + NEWS_PAGE_SIZE
    page_items = (
        headlines[start:end]
        if end <= total else (headlines[start:] + headlines[:end - total])
    )
    page_info = f" {page_index + 1}/{num_pages}"

    # Basis-Style für News-Container
    outer_style = {
        "backgroundColor": "#e0e0e0",
        "padding": "8px 12px",
        "borderRadius": "8px",
        "zIndex": "1000",
        "display": "inline-block",   # sorgt dafür, dass der graue Hintergrund exakt am Inhalt endet
        "maxWidth": "480px",         # verhindert extrem breite Boxen
    }

    # Desktop: News-Blase oben rechts (wie bisher)
    if not SERVER_VARIANT:
        outer_style.update({
            "position": "absolute",
            "right": "30px",
            "top": "480px",
        })

    # Server/Handy: News unter dem Index, volle Breite erlaubt
    else:
        outer_style.update({
            "marginTop": "8px",
            "marginBottom": "8px",
            "width": "100%",         # auf kleinen Displays gute Anpassung
            "display": "block",      # normaler Block unter dem Plot
            "maxWidth": "100%",      # volle Breite nutzen
        })

    return html.Div([
        html.Div([
            html.Span(
                f"Top-Börsennachrichten (finanztreff.de) Seite {page_info}",
                style={"fontWeight": "bold", "display": "block"}
            ),
            html.Span(
                f"Stand: {last_str}",
                style={"color": "#555", "fontSize": "90%", "display": "block"}
            )
        ], style={"marginBottom": "10px"}),

        html.Ul([
            html.Li(
                html.A(
                    title,
                    href=link,
                    target="_blank",
                    style={"textDecoration": "none", "color": "#004c99"}
                ),
                style={"marginBottom": "8px", "listStyleType": "none"}
            ) for title, link in page_items
        ], style={"paddingLeft": "0", "marginTop": "0"})

    ], style=outer_style)



#Position news block top": "460px","width":


# RSI
def get_rsi(ticker_symbol, period=8):
    """RSI-Berechnung mit Cache (nur alle 60 Sekunden neu berechnen)"""
    now = time.time()
    
    # Cache-Schlüssel erstellen
    cache_key = f"{ticker_symbol}_{period}"
    
    # Prüfen ob Cache-Eintrag existiert und noch gültig ist
    if cache_key in _RSI_CACHE:
        cache_entry = _RSI_CACHE[cache_key]
        if now - cache_entry["ts"] < _RSI_CACHE_TTL:
            return cache_entry["value"]
    
    try:
        stock = yf.Ticker(clean_ticker(ticker_symbol))
        data = stock.history(period="3mo")
        if len(data) < period:
            return None
        delta = data['Close'].diff()
        up = delta.where(delta > 0, 0)
        down = -delta.where(delta < 0, 0)
        avg_gain = up.ewm(alpha=1/period, adjust=False).mean()
        avg_loss = down.ewm(alpha=1/period, adjust=False).mean()
        rs = avg_gain / avg_loss
        rsi = 100 - (100 / (1 + rs))
        rsi_value = rsi.iloc[-1]
        
        # Im Cache speichern
        _RSI_CACHE[cache_key] = {"ts": now, "value": rsi_value}
        return rsi_value
        
    except Exception as e:
        print(f"Fehler bei RSI-Berechnung für {ticker_symbol}: {e}")
        return None

# Optional: Cache leeren Funktion falls benötigt
def clear_rsi_cache():
    """Leert den RSI-Cache"""
    global _RSI_CACHE
    _RSI_CACHE.clear()

def bewerte_rsi_ampel(rsi_value):
    if rsi_value is None:
        return "#808080", "RSI: Keine Daten verfügbar", "Keine Daten"
    if rsi_value >= RSI_OVERBOUGHT:
        return "#ff0000", "RSI-Indikator", f"Risiko: Korrektur innerhalb 8 Tage wahrscheinlich! RSI ={rsi_value:.1f}%"
    elif rsi_value >= RSI_WARN:
        return "#FFA500", "RSI-Indikator", f"Warnung: Markt überhitzt! (RSI {rsi_value:.1f}%) Erhöhtes Rückfall-Risiko"
    else:
        return "#90EE90", "RSI-Indikator", f"RSI unkritisch ({rsi_value:.1f}%)"

# Ordner / Zustände
CSV_FOLDER = "CSV"
os.makedirs(CSV_FOLDER, exist_ok=True)

scraper_start_time = datetime.now(TZ_BERLIN).strftime("%H:%M:%S")

persistenter_kommentar = ""
persistenz_counter = 0
verhältnis_vorher = 0

def get_rsi_for_underlying(underlying):
    return {"Dax":"^GDAXI","S&P 500":"^GSPC","EURO STOXX 50":"^STOXX50E","Dow Jones":"^DJI","Nasdaq 100":"^NDX"}.get(underlying,None)

FARBCODES = {"green":"#90EE90","orange":"orange","red":"red","gray":"gray","orange":"#FFA500"}

UNDERLYINGS = {
    "Dax": {
        "long": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-DAX?customerId=7&customerIntegrationOrigin=derivative&customerIntegrationType=QUICKLINKS_DERIVATIVES&customerName=UBS&idExerciseRight=2&idIssuer=53163&idIssuerIntegration=53163",
        "short": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-DAX?customerId=7&customerIntegrationOrigin=derivative&customerIntegrationType=QUICKLINKS_DERIVATIVES&customerName=UBS&idExerciseRight=1&idIssuer=53163&idIssuerIntegration=53163"},
       
    "S&P 500": {
        "long": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-S-P-500?customerId=7&customerIntegrationOrigin=derivative&customerIntegrationType=QUICKLINKS_DERIVATIVES&customerName=UBS&idExerciseRight=2&idIssuer=53163&idIssuerIntegration=53163",
        "short": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-S-P-500?customerId=7&customerIntegrationOrigin=derivative&customerIntegrationType=QUICKLINKS_DERIVATIVES&customerName=UBS&idExerciseRight=1&idIssuer=53163&idIssuerIntegration=53163",
    },
    "EURO STOXX 50": {
        "long": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-EURO-STOXX-50?idExerciseRight=2",
        "short": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-EURO-STOXX-50?idExerciseRight=1",
        
    },
    "Dow Jones": {
        "long": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-Dow-Jones?idExerciseRight=2",
        "short": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-Dow-Jones?idExerciseRight=1",
        
    },
    "Nasdaq 100": {
        "long": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-NASDAQ-100?idExerciseRight=2",
        "short": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-NASDAQ-100?idExerciseRight=1",
       
    }
}



def _cache_load() -> Dict:
    if futures_CACHE_PATH.is_file():
        try:
            return json.loads(futures_CACHE_PATH.read_text(encoding="utf-8"))
        except Exception:
            return {}
    return {}

def _cache_save(obj: Dict) -> None:
    futures_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    futures_CACHE_PATH.write_text(json.dumps(obj, ensure_ascii=False, indent=2), encoding="utf-8")



def _yf_pct_change_intraday_vs_prevclose(sym: str) -> float | None:
    try:
        df = yf.download(sym, period="2d", interval="1m", auto_adjust=True, progress=False)
        if df is None or df.empty:
            return None

        # letzter Kurs
        last = float(df["Close"].iloc[-1])

        # Schlusskurs Vortag aus daily-Daten holen
        daily = yf.Ticker(sym).history(period="2d")
        if daily is None or len(daily) < 2:
            return None
        prev = float(daily["Close"].iloc[-2])

        if prev == 0:
            return None
        return (last / prev - 1.0) * 100.0
    except Exception:
        return None



selected_underlying = "Dax"
# Thread-sicherer Zugriff auf das aktuell gewählte Underlying
_SELECTED_LOCK = Lock()

def get_selected_underlying():
    with _SELECTED_LOCK:
        return selected_underlying

def set_selected_underlying(u: str):
    global selected_underlying
    with _SELECTED_LOCK:
        selected_underlying = u

refresh_interval = 8  #Abruf Intervall

last_fetch_time = "-"
ALARM_THRESHOLD = 999
stop_event = threading.Event()
update_thread = None
# === leichte Caches/TTLs ===
FUTURES_TTL = max(12, int(refresh_interval))       # 1 Tick
INDEX_TTL   = max(10, int(refresh_interval))       # 1 Tick
_FUTURES_CACHE = {"ts": 0, "u": None, "val": None}
_INDEX_CACHE   = {"ts": 0, "u": None, "val": None}

#_last_vdax_change = None
#_last_EURO_STOXX_50_change = None
# Verwende ein Dictionary:
_volatility_cache = {
    "Dax": {"value": None, "ts": 0},
    "S&P 500": {"value": None, "ts": 0},
    "EURO STOXX 50": {"value": None, "ts": 0},
    "Dow Jones": {"value": None, "ts": 0},
    "Nasdaq 100": {"value": None, "ts": 0}
}

# Sichtbar konfigurierbar:
VDAX_WAIT_OVERRIDE = None  # z.B. 4 setzen, sonst dynamisch

# Optional: Glättung ein/aus
FUTURE_SMOOTHING = False

def _extract_percent(txt: str) -> float | None:
    if not txt:
        return None
    t = txt.replace("−","-").replace("%","").replace(",",".").strip()
    import re
    m = re.search(r"([+-]?\d+(?:\.\d+)?)", t)
    return float(m.group(1)) if m else None

def _investing_future_change(underlying: str, timeout=WAIT_SHORT) -> float | None:
    url = INVEST_FUT_URL.get(underlying)
    if not url:
        return None
    try:
        d = _ensure_investing_open(underlying)
        if d is None:
            return None

        from selenium.webdriver.common.by import By
        from selenium.webdriver.support.ui import WebDriverWait
        from selenium.webdriver.support import expected_conditions as EC

        now = time.time()
        el = WebDriverWait(d, timeout).until(
            EC.visibility_of_element_located((By.CSS_SELECTOR, '[data-test="instrument-price-change-percent"]'))
        )
        txt = (el.text or "").strip()

        # Stale-Guard: wenn Text zu lange unverändert, einmal refreshen
        last = _INVEST_LAST.get(underlying)
        if last and last.get("txt") == txt and (now - last.get("ts", 0)) > STALE_REFRESH_SEC:
            d.refresh()
            el = WebDriverWait(d, timeout).until(
                EC.visibility_of_element_located((By.CSS_SELECTOR, '[data-test="instrument-price-change-percent"]'))
            )
            txt = (el.text or "").strip()
            now = time.time()

        _INVEST_LAST[underlying] = {"txt": txt, "ts": now}

        val = _extract_percent(txt)
        if val is None:
            # letzter Rettungsversuch
            d.refresh()
            el = WebDriverWait(d, timeout).until(
                EC.visibility_of_element_located((By.CSS_SELECTOR, '[data-test="instrument-price-change-percent"]'))
            )
            val = _extract_percent((el.text or "").strip())

        return stabilize_future_pct(underlying, val) if FUTURE_SMOOTHING and val is not None else val
    except Exception:
        return None



def get_vdax_change(timeout=4):
    """
    VDAX %-Änderung von boerse-frankfurt.de robust auslesen.
    Probiert mehrere Selektoren. Kein None ins Cache schreiben.
    Finanztreff-Fallback ist zwischen 09:00–09:40 Europe/Berlin gesperrt.
    """
    url = "https://www.boerse-frankfurt.de/index/vdax"

    def _try_once():
        d = get_driver("general")
        d.get(url + f"?t={int(time.time())}")
        accept_cookies_if_present(d, timeout=4)
        WebDriverWait(d, timeout).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        time.sleep(1.2)

        # 1) dd nach dt-Label
        for xp in [
            "//dt[normalize-space()='Veränderung zum Vortag']/following-sibling::dd[1]",
            "//td[normalize-space()='Veränderung zum Vortag']/following-sibling::td[1]",
            "//div[contains(@class,'change') or contains(@class,'percent') or contains(@class,'veraenderung')]",
            "//*[contains(text(), '%')]"
        ]:
            try:
                el = d.find_element(By.XPATH, xp)
                raw = el.text.strip()
                val = _extract_percent(raw)
                if val is not None:
                    return round(val, 2)
            except Exception:
                continue
        return None
    #
    drv = None
    from contextlib import suppress

# ...
    try:
        val = _try_once()
        if val is None:
            # Driver reset + zweiter Versuch
            with _DRIVER_POOL_LOCK:
                for k in ("general", f"general_{selected_underlying}"):
                    with suppress(Exception):
                        d = _DRIVER_POOL.pop(k, None)
                        if d:
                            d.quit()
            val = _try_once()
    except Exception as e:
        print(f"⚠️ VDAX Frankfurt fehlgeschlagen: {e}")
        val = None


    # Zeitfenster: Finanztreff-Fallback für Vola sperren zwischen 09:00–09:40 Europe/Berlin
    try:
        now_ber = datetime.now(TZ_BERLIN)
        block_finanztreff = now_ber.replace(hour=9, minute=0, second=0, microsecond=0) <= now_ber < \
                            now_ber.replace(hour=9, minute=40, second=0, microsecond=0)
    except Exception:
        block_finanztreff = False

    if val is None and not block_finanztreff:
        val = get_vdax_change_finanztreff()
    # if val is None:
    #     val = get_vdax_change_yahoo()  # bewusst auskommentiert wie bisher

    if val is not None:
        _volatility_cache["Dax"] = {"value": val, "ts": time.time()}
    return val



def get_EURO_STOXX_50_change():
    try:
        d = get_driver("general", KEY_GLOBAL)
        d.get("https://www.boerse-frankfurt.de/index/EURO%20STOXX%2050")
        el = WebDriverWait(d, 12).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "td.widget-table-cell.text-end.change-percent"))
        )
        raw = (el.text or "").strip()
        val = _parse_german_percent(raw)
        if val is not None:
            print(f"✔️ EURO STOXX 50 Veränderung: {val:.2f} %")
        else:
            print(f"⚠️ EURO STOXX 50: konnte Zahl nicht parsen (raw='{raw}')")
        return val
    except Exception as e:
        print(f"⚠️ Fehler beim EURO STOXX 50-Abruf: {e}")
        return None

def _parse_german_percent(raw: str) -> float | None:
    """Wandelt '0,85 %' / '+1,2%' / '-0,30 %' in float (0.85 / 1.2 / -0.30)."""
    if not raw:
        return None
    txt = raw.replace("\xa0", " ").strip()  # geschütztes Leerzeichen
    
    m = re.search(r"-?\+?\d+(?:[.,]\d+)?", txt)
    if not m:
        return None
    num = m.group(0).replace(".", "").replace(",", ".").replace("+", "")
    try:
        return float(num)
    except ValueError:
        return None

# --- VSTOXX (stock3) ---
_last_vstoxx_change = None  # Prozentwert, z.B. 0.85


def get_vix_change_yahoo():
    try:
        data = yf.Ticker("^VIX").history(period="2d")
        if len(data) >= 2:
            prev = data['Close'].iloc[-2]
            curr = data['Close'].iloc[-1]
            return ((curr - prev) / prev) * 100
    except Exception as e:
        print(f"Fehler beim Abrufen des VIX: {e}")
    return None

def get_vxn_change_yahoo():
    try:
        data = yf.Ticker("^VXN").history(period="2d")
        if len(data) >= 2:
            prev = data['Close'].iloc[-2]
            curr = data['Close'].iloc[-1]
            return ((curr - prev) / prev) * 100
    except Exception as e:
        print(f"Fehler beim Abrufen des VXN: {e}")
    return None



def get_vxd_change_yahoo():
    try:
        data = yf.Ticker("^VXD").history(period="2d")
        if len(data) >= 2:
            prev = data['Close'].iloc[-2]
            curr = data['Close'].iloc[-1]
            return ((curr - prev) / prev) * 100
    except Exception as e:
        print(f"Fehler beim Abrufen des VXD: {e}")
    return None


# --- Multi-Cache: Index+Future eines Underlyings ---
_YF_MULTI_IF = {"ts": 0.0, "ttl": 15.0, "data": {}}  # data[underlying] = {"idx": float|None, "fut": float|None}


def get_index_data(underlying):
    """
    Live %-Änderung ggü. Vortagesschluss + Lastpreis.
    Quelle: Yahoo 1m-Data; PrevClose bevorzugt fast_info.previous_close.
    Rückgabe: (pct_change: float|None, last_str: str, color_flag: str)
    """
    try:
        # Symbol ermitteln (nutze vorhandene Map, sonst lokale Fallback-Map)
        sym = None
        try:
            sym = YF_SYMBOL.get(underlying)  # falls vorhanden
        except Exception:
            pass
        if not sym:
            sym = {
                "Dax": "^GDAXI",
                "EURO STOXX 50": "^STOXX50E",
                "S&P 500": "^GSPC",
                "Dow Jones": "^DJI",
                "Nasdaq": "^NDX",
                "Nasdaq 100": "^NDX",
            }.get(underlying)

        if not sym:
            return None, "-", "gray"

        with YF_CALL_LOCK:
            t = yf.Ticker(sym)

            # 1) PrevClose: fast_info → Fallback Daily (2–10d)
            prev_close = None
            try:
                fi = getattr(t, "fast_info", None)
                if fi is not None:
                    prev_close = _nan_to_none(getattr(fi, "previous_close", None))
                    if prev_close: prev_close = float(prev_close)
            except Exception:
                prev_close = None

            if not prev_close or prev_close <= 0:
                for days in ("2d", "5d", "10d"):
                    try:
                        ddf = yf.download(sym, period=days, interval="1d",
                                          progress=False, auto_adjust=False)
                        if ddf is None or ddf.empty:
                            continue
                        closes = ddf["Close"].dropna()
                        if len(closes) >= 2:
                            prev_close = float(closes.iloc[-2])
                            if prev_close > 0:
                                break
                    except Exception:
                        continue

            # 2) Letzter Kurs: 1m-Data → Fallback fast_info Preisfelder
            last = None
            try:
                intra = yf.download(sym, period="1d", interval="1m",
                                    progress=False, auto_adjust=False, prepost=True)
                if intra is not None and not intra.empty:
                    c = intra["Close"].dropna()
                    if len(c) > 0:
                        last = float(c.iloc[-1])
            except Exception:
                last = None

            if last is None:
                try:
                    fi = getattr(t, "fast_info", None)
                    if fi is not None:
                        last = _nan_to_none(getattr(fi, "last_price", None)) or \
                               _nan_to_none(getattr(fi, "last_trade", None))
                        if last: last = float(last)
                    if not last:
                        info = getattr(t, "info", {}) or {}
                        lp = info.get("regularMarketPrice")
                        if lp: last = float(lp)
                except Exception:
                    last = None

        # 3) Ergebnis
        if last and prev_close and prev_close > 0:
            pct = (last/prev_close - 1.0) * 100.0
            return float(round(pct, 2)), f"{last:.2f}", "color"

        return None, "-", "gray"

    except Exception as e:
        print(f"Fehler bei Yahoo-Indexdaten ({underlying}): {e}")
        return None, "-", "gray"



# --- Gong-Funktionalität für Börsenschluss ---#######################
_GONG_PLAYED_TODAY = {"date": None, "played": False}

def _should_play_gong(underlying: str) -> bool:
    # … Reset wie bisher …
    market = "USA" if underlying in ("S&P 500","Dow Jones","Nasdaq 100") else "EUROPE"
    now = datetime.now(TZ_BERLIN)
    _, close_ber = market_window_local(market, now)
    one_min_before = (close_ber - timedelta(minutes=1)).replace(second=0, microsecond=0)
    if now.replace(second=0, microsecond=0) == one_min_before and not _GONG_PLAYED_TODAY["played"]:
        _GONG_PLAYED_TODAY["played"] = True
        return True
    return False

    
    now = datetime.now(TZ_BERLIN)
    
    # Börsenzeiten für verschiedene Underlyings
    market_times = {
        "Dax": {"end": (17, 29)},  # 1 Minute vor 17:30
        "EURO STOXX 50": {"end": (17, 29)},
        "S&P 500": {"end": (21, 59)},  # 1 Minute vor 22:00
        "Dow Jones": {"end": (21, 59)},
        "Nasdaq 100": {"end": (21, 59)}
    }
    
    if underlying not in market_times:
        return False
    
    end_hour, end_minute = market_times[underlying]["end"]
    
    # Prüfe ob aktuelle Zeit genau 1 Minute vor Börsenschluss
    if (now.hour == end_hour and now.minute == end_minute and now.second == 0):
        _GONG_PLAYED_TODAY["played"] = True
        return True
    
    return False

def get_gong_sound() -> str:
    """Gibt den Gong-Sound zweimal nacheinander zurück, wenn es Zeit ist."""
    underlying = get_selected_underlying()

    if _should_play_gong(underlying) and is_sound_enabled():
        u = app.get_asset_url("gong.wav")
        ts1 = f"{time.time():.3f}"
        ts2 = f"{time.time() + 6.2:.3f}"  # zweiter Gong 6 Sek. später
        # Rückgabe enthält beide URLs mit Zeitversatz
        return f"{u}?ts={ts1}|delay=0;{u}?ts={ts2}|delay=6"

    return ""


    ##ende TOn zu Börsenschluß

def get_index_future_changes(underlying: str) -> tuple[float | None, float | None]:
    idx = YF_SYMBOL.get(underlying)
    idx_val: float | None = None
    fut_val: float | None = None
    try:
        # Index unverändert via Yahoo
        if underlying in ("Dax", "EURO STOXX 50"):
            idx_val = _yf_pct_intraday_vs_prevclose_single(idx)
        else:
            vals = _yf_multi_intraday_vs_prevclose([idx])
            idx_val = vals.get(idx)

        # Futures: Dax & EURO STOXX 50 ausschließlich Investing
        if underlying in ("Dax", "EURO STOXX 50"):
            fut_val = _investing_future_change(underlying)
        else:
            # US etc. bleiben wie bisher
            fut_val = _investing_future_change(underlying)
            if fut_val is None:
                vals = _yf_multi_intraday_vs_prevclose([FUT_SYMBOL.get(underlying)])
                fut_val = vals.get(FUT_SYMBOL.get(underlying)) or _ariva_future_change(underlying)
    except Exception:
        pass
    return idx_val, fut_val



def get_future_change_pct(underlying: str) -> float | None:
    print(f"🔍 Abrufe Future für: {underlying}")

    try:
        _, fut_val = get_index_future_changes(underlying)
        if fut_val is not None:
            print(f"✅ {underlying} Future: {fut_val:.2f}%")
            return float(fut_val)
    except Exception:
        pass

    # Dax & EURO STOXX 50 nur Investing
    if underlying in ("Dax", "EURO STOXX 50"):
        v = _investing_future_change(underlying)
        return float(v) if isinstance(v, (int, float)) else None

    # Rest wie bisher
    v = _investing_future_change(underlying)
    if isinstance(v, (int, float)):
        return float(v)

    vals = _yf_multi_intraday_vs_prevclose([FUT_SYMBOL.get(underlying)])
    v = vals.get(FUT_SYMBOL.get(underlying))
    if v is None or v == 0.0:
        v = _ariva_future_change(underlying)
    return float(v) if isinstance(v, (int, float)) else None



def get_intraday_change_min_max(underlying: str):
    """Liefert (min_pct, max_pct) des heutigen Tages relativ zum Vortagesschluss in Prozent.
       Quelle: Yahoo Finance 1m-Daten inkl. Pre/Post. Kein CSV."""
    ticker_map = {
        "Dax": "^GDAXI",
        "EURO STOXX 50": "^STOXX50E",
        "S&P 500": "^GSPC",
        "Dow Jones": "^DJI",
        "Nasdaq": "^NDX",
        "Nasdaq 100": "^NDX",
    }
    sym = ticker_map.get(underlying)
    if not sym:
        return None, None
    try:
        # Optional: globaler Yahoo-Lock, falls vorhanden
        lock = globals().get("YF_CALL_LOCK", None)
        import yfinance as yf

        if lock:
            lock.__enter__()
        try:
            t = yf.Ticker(sym)

            # 1) PrevClose: fast_info → Fallback Daily (2–5d)
            prev_close = None
            fi = getattr(t, "fast_info", None)
            if fi is not None:
                pc = getattr(fi, "previous_close", None)
                if pc is not None and float(pc) > 0:
                    prev_close = float(pc)

            if not prev_close or prev_close <= 0:
                d = yf.download(
                    sym, period="2d", interval="1d",
                    auto_adjust=False, progress=False, threads=False
                )
                if d is None or d.empty or "Close" not in d or d["Close"].dropna().size < 2:
                    d = yf.download(
                        sym, period="5d", interval="1d",
                        auto_adjust=False, progress=False, threads=False
                    )
                if d is not None and not d.empty and "Close" in d:
                    cc = d["Close"].dropna()
                    if cc.size >= 2:
                        prev_close = float(cc.iloc[-2])

            if not prev_close or prev_close <= 0:
                return None, None

            # 2) Intraday-Min/Max aus 1m inkl. Pre/Post
            intra = yf.download(
                sym, period="1d", interval="1m",
                auto_adjust=False, progress=False, threads=False, prepost=True
            )
        finally:
            if lock:
                lock.__exit__(None, None, None)

        if intra is None or intra.empty:
            return None, None

        highs = intra.get("High")
        lows  = intra.get("Low")
        if highs is None or lows is None:
            return None, None
        highs = highs.dropna()
        lows  = lows.dropna()
        if highs.empty or lows.empty:
            return None, None

        hi = float(highs.max())
        lo = float(lows.min())
        if hi <= 0 or lo <= 0:
            return None, None

        max_pct = (hi - prev_close) / prev_close * 100.0
        min_pct = (lo - prev_close) / prev_close * 100.0

        # Docstring-konform: (min_pct, max_pct)
        return float(min_pct), float(max_pct)
    except Exception:
        return None, None





def cleanup_memory():
    gc.collect()
    # WebDriver-Cache leeren
    if _DRIVER:
        _DRIVER.execute_script("window.open('','_blank').close()")
        _DRIVER.execute_script("window.location.reload(true)")

def _plausible_vdax(p: float | None) -> bool:
    # VDAX %-Veränderung i. d. R. zwischen -20% und +20%
    return p is not None and -20.0 <= float(p) <= 20.0


from datetime import datetime
import pytz
TZ_BERLIN = pytz.timezone("Europe/Berlin")

def get_volatility_change(underlying):
    """
    Liefert die %-Änderung des passenden Volatilitätsindex.
    Vorbörslich keine Vola-Abfragen:
      - Dax, EURO STOXX 50: erst ab 09:31 Europe/Berlin
      - S&P 500, Dow Jones, Nasdaq: erst ab 15:31 Europe/Berlin
    Vorher wird nur der Cache zurückgegeben (oft None -> „Keine Daten“ in der UI).
    """
    global _volatility_cache
    now_ts = time.time()
    cache = _volatility_cache.get(underlying, {"value": None, "ts": 0})

    # TTL an refresh_interval koppeln
    ttl = max(1, refresh_interval - 1)
    if (now_ts - cache["ts"] < ttl) and (cache["value"] is not None):
        return cache["value"]

    # Nur aktives Underlying aktiv abrufen
    try:
        if underlying != get_selected_underlying():
            return cache.get("value")
    except Exception:
        return cache.get("value")

    # Zeitfenster
    now_ber = datetime.now(TZ_BERLIN)
    is_eu = underlying in ("Dax", "EURO STOXX 50")
    is_us = underlying in ("S&P 500", "Dow Jones", "Nasdaq 100")

    # EU-Vola bis 09:31 nicht abrufen
    if is_eu and not (now_ber.hour > 9 or (now_ber.hour == 9 and now_ber.minute >= 20)):
        return cache.get("value")

    # US-Vola bis 15:31 nicht abrufen
    if is_us and not (now_ber.hour > 15 or (now_ber.hour == 15 and now_ber.minute >= 25)):
        return cache.get("value")

    # Clamp ±30 %
    CLAMP_MIN, CLAMP_MAX = -30.0, 30.0
    def _clamp(p):
        return max(CLAMP_MIN, min(CLAMP_MAX, float(p)))

    try:
        val = None

        if underlying == "EURO STOXX 50":
            # strikt OnVista
            val = get_vstoxx_change_onvista()
            if val is not None and not (CLAMP_MIN <= float(val) <= CLAMP_MAX):
                val = None

        elif underlying == "Dax":
            val = get_vdax_change()
            if val is not None:
                val = _clamp(val)

        elif underlying == "S&P 500":
            val = (get_vix_change_yahoo() or get_vix_change_finanztreff())

        elif underlying == "Dow Jones":
            val = (get_vxd_change_yahoo() or get_vxd_change_finanztreff())

        elif underlying == "Nasdaq 100":
            val = (get_vxn_change_yahoo() or get_vxn_change_finanztreff())

        if val is not None:
            v = float(val)
            _volatility_cache[underlying] = {"value": v, "ts": now_ts}
            return v

        # Fallback: letzter Wert aus Cache
        return cache.get("value")

    except Exception as e:
        print(f"⚠️ get_volatility_change: {e}")
        return cache.get("value")


def get_vstoxx_change_yahoo():
    return None


# einmal global sicherstellen
if "_DRIVER_POOL_LOCK" not in globals():
    _DRIVER_POOL_LOCK = threading.Lock()
if "DRIVERS" not in globals():
    DRIVERS = {}
if "DRIVER_LOCKS" not in globals():
    DRIVER_LOCKS = {}

def reset_drivers_on_underlying_change(old_underlying: str | None = None) -> int:
    """Schließt passende Driver (onvista/general) threadsicher und räumt Locks. Rückgabe: Anzahl geschlossen."""
    keys = list(DRIVERS.keys())
    kill: set[str] = set()

    if old_underlying is None:
        # alles Onvista + alle 'general'-Keys
        kill.update(k for k in keys if k.startswith("onvista_") or k.startswith("general"))
    else:
        # alle zum alten Underlying + general-Varianten
        kill.update(k for k in keys if k.endswith(f"_{old_underlying}"))
        kill.update({"general", f"general_{old_underlying}"})

    closed = 0
    with _DRIVER_POOL_LOCK:
        for k in kill:
            drv = DRIVERS.pop(k, None)
            if drv:
                with suppress(Exception):
                    drv.quit()
                closed += 1
            with suppress(Exception):
                DRIVER_LOCKS.pop(k, None)
    return closed


import re

def _parse_leverage_numbers(txt: str) -> list[float]:
    import re
    # 1) streng: nur echte Hebel-Notation mit x/×
    strict = re.findall(r"(?i)(?:\bhebel\b[^:\n\r]*:?\s*)?(?:x|×)\s*(\d{1,4}(?:[.,]\d{1,2})?)|(\d{1,4}(?:[.,]\d{1,2})?)\s*(?:x|×)", txt)
    nums = [g1 or g2 for g1, g2 in strict]
    # 2) fallback: alte breite Suche
    if not nums:
        nums = re.findall(r"(?i)(?:\bhebel\b\s*:?\s*)?(?:x|×)?\s*(\d{1,4}(?:[.,]\d{1,2})?)\s*(?:x|×)?", txt)

    out = []
    for n in nums:
        n = n.replace(".", "").replace(",", ".")
        try:
            v = float(n)
            if 1.1 <= v <= 500:  # vorher 300
                out.append(v)
        except ValueError:
            pass
    return out

def get_vstoxx_change() -> float | None:
    """
    VSTOXX %-Veränderung von stock3.com via Selenium.
    Gibt float zurück, z. B. 0.85 (= +0,85 %) oder -0.30.
    """
    try:
        d = get_driver()
        d.get("https://stock3.com/indizes/vstoxx-volatilitaetsindex-17271029/")
        el = WebDriverWait(d, 20).until(
            EC.presence_of_element_located(
                (By.CSS_SELECTOR, "span.instrument-value.changePerc")
            )
        )
        raw = el.text.strip() or el.get_attribute("data-inst-formatted") or ""
        val = _parse_german_percent(raw)
        if val is not None:
            print(f"✔️ VSTOXX Veränderung: {val:.2f} % (Quelle: stock3)")
        else:
            print(f"⚠️ VSTOXX: konnte Zahl nicht parsen (raw='{raw}')")
        return val
    except Exception as e:
        print(f"⚠️ Fehler beim VSTOXX-Abruf: {e}")
        return None

# Mein Hebel anpassen an Vola des gewählten Index
# Cross-Index-Korrektur (nutzt bestehendes _get_current_x)
INDEX_POOL = ["Dax","EURO STOXX 50","S&P 500","Dow Jones","Nasdaq 100"]  # deine 5

def _mean_current_vola(exclude: str | None = None) -> float | None:
    xs = []
    for u in INDEX_POOL:
        if exclude and u == exclude:
            continue
        xi = _get_current_x(u)
        if xi and xi > 0:
            xs.append(xi)
    if not xs:
        return None
    return float(np.mean(xs))


    


def get_csv_filename(underlying):
    # In EXE: CSV im gleichen Verzeichnis wie EXE speichern
    if hasattr(sys, '_MEIPASS'):
        base_dir = os.path.dirname(sys.executable)
    else:
        base_dir = os.path.dirname(__file__)
    
    csv_dir = os.path.join(base_dir, "CSV")
    os.makedirs(csv_dir, exist_ok=True)
    return os.path.join(csv_dir, f"hebel_{underlying.replace(' ', '_')}.csv")


def log_index_event(timestamp, index_change):
    filename = os.path.join(CSV_FOLDER, "log_index.csv")
    log_exists = os.path.exists(filename)
    with open(filename, mode='a', newline='', encoding='utf-8') as file:
        writer = csv.writer(file, lineterminator='\n')
        if not log_exists:
            writer.writerow(["timestamp", "index_change"])
        writer.writerow([timestamp, index_change])

def _wait_onvista_table(d, timeout=WAIT_LONG):
    WebDriverWait(d, timeout).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
    try:
        WebDriverWait(d, 6).until(
            EC.presence_of_element_located((By.XPATH, "//table//th[contains(., 'Hebel') or contains(., 'Gearing')]"))
        ); return True
    except Exception:
        pass
    WebDriverWait(d, timeout).until(EC.presence_of_element_located((By.CSS_SELECTOR, "table tbody")))
    time.sleep(0.8); return True



@lru_cache(maxsize=8)
def scrape_average_leverage(url_onvista, url_finanzen=None):
    # OnVista
    try:
        d = get_driver("onvista", get_selected_underlying())
        d.get(url_onvista)
        WebDriverWait(d, 15).until(EC.presence_of_element_located((By.CSS_SELECTOR, "table tr")))
        WebDriverWait(d, 5).until(lambda drv: "gearingAsk" in drv.page_source or "Hebel" in drv.page_source)
        soup = BeautifulSoup(d.page_source, "html.parser")
        vals = []
        for row in soup.find_all("tr"):
            for cell in row.find_all("td"):
                t = cell.get_text(strip=True)
                try:
                    v = float(t.replace(',', '.'))
                    if 1 <= v <= 200:
                        vals.append(v); break
                except ValueError:
                    continue
        if vals:
            return sum(vals)/len(vals)
    except Exception:
        pass
    # Optionaler Fallback Finanzen.net
    if url_finanzen:
        try:
            d = get_driver("onvista", get_selected_underlying())
            d.get(url_finanzen)
            WebDriverWait(d, 15).until(EC.presence_of_element_located((By.CSS_SELECTOR, "table tr")))
            WebDriverWait(d, 5).until(lambda drv: "gearingAsk" in drv.page_source or "Hebel" in drv.page_source)
            soup = BeautifulSoup(d.page_source, "html.parser")
            vals = []
            for row in soup.find_all("tr"):
                for cell in row.find_all("td"):
                    t = cell.get_text(strip=True)
                    try:
                        v = float(t.replace(',', '.'))
                        if 1 <= v <= 200:
                            vals.append(v); break
                    except ValueError:
                        continue
            if vals:
                return sum(vals)/len(vals)
        except Exception:
            pass
    return None

    

def play_alarm():
    if not is_sound_enabled():
        return
    if SIMPLEAUDIO_AVAILABLE:
        wav_path = resource_path("alarm.wav")
        if os.path.exists(wav_path):
            try:
                import simpleaudio as sa
                sa.WaveObject.from_wave_file(wav_path).play()
                return
            except Exception:
                pass
    try:
        import winsound
        winsound.Beep(1000, 500)
    except Exception:
        print("⚠️ Kein Audio-Ausgabemodul verfügbar.")

def get_dynamic_thresholds(df_history):
    if len(df_history) < 10:
        return {'short_crash': -10,'short_warning': -8,'long_warn': 15,'bullisch': 10,'index_confirm': 0.2,'leverage_volatility_factor': 1.0}
    index_volatility = df_history['index_change'].abs().rolling(10).mean().iloc[-1]
    leverage_volatility = df_history[['long_avg','short_avg']].pct_change().abs().mean().mean()
    if index_volatility < 0.3:
        return {'short_crash': -8,'short_warning': -6,'long_warn': 12,'bullisch': 8,'index_confirm': 0.15,'leverage_volatility_factor': 0.8}
    elif index_volatility < 0.5:
        return {'short_crash': -10,'short_warning': -8,'long_warn': 15,'bullisch': 10,'index_confirm': 0.25,'leverage_volatility_factor': 1.0}
    else:
        return {'short_crash': -12,'short_warning': -10,'long_warn': 18,'bullisch': 12,'index_confirm': 0.35,'leverage_volatility_factor': 1.2}

def bewerte_ampel(long_now, long_prev, short_now, short_prev, timestamp=None, index_change=None, df_history=None):
    global persistenter_kommentar, persistenz_counter, verhältnis_vorher
    kommentar = "Keine Bewertung möglich"
    if persistenz_counter > 0 and ("Crash-Alarm" in persistenter_kommentar or "Frühwarnung" in persistenter_kommentar):
        kommentar = persistenter_kommentar; persistenz_counter -= 1
    else:
        persistenter_kommentar = kommentar; persistenz_counter = 0
    ampel_symbol = "⚪"
    if long_now > short_now:
        ampel_symbol = "🔴"; base_kommentar = "🔴 Long-Hebel über Short-Hebel - Banken erwarten fallenden Markt,deswegen bieten Sie kleinere Short an"
    elif long_now < short_now:
        ampel_symbol = "🟢"; base_kommentar = "🟢 Short-Hebel über Long-Hebel - Banken erwarten steigenden Markt,deswegen bieten Sie kleinere Long an"
    else:
        ampel_symbol = "🟠"; base_kommentar = "🟠 Neutral: Long- und Short-Hebel gleich. Evtl: Programm neu starten und Reset. Wenn Börse zu sind Hebelsprünge normal."
    thresholds = get_dynamic_thresholds(df_history if df_history is not None else pd.DataFrame())
    rel_delta_long = (long_now - long_prev) / long_prev * 100 * thresholds['leverage_volatility_factor'] if long_prev != 0 else 0
    rel_delta_short = (short_now - short_prev) / short_prev * 100 * thresholds['leverage_volatility_factor'] if short_prev != 0 else 0
    if rel_delta_short <= thresholds['short_crash']:
        ampel_symbol = "🔴"; base_kommentar = f"🔴 Auffälliger Rückgang der Short-Hebel um {abs(rel_delta_short):.1f}% (Volatilität: {thresholds['leverage_volatility_factor']:.1f}x)"
    elif rel_delta_short <= thresholds['short_warning']:
        ampel_symbol = "🟠"; base_kommentar = f"🟠 Frühwarnung: Shorts  (fällt){abs(rel_delta_short):.1f}% (Schwelle: {thresholds['short_warning']}%)"
    elif rel_delta_long >= thresholds['long_warn']:
        ampel_symbol = "🟠"; base_kommentar = f" 🟠 Long-Push: {rel_delta_long:.1f}% (Schwelle: {thresholds['long_warn']}%)"
    kommentar = base_kommentar
    if (long_now < long_prev) and (short_now < short_prev):
        kommentar += " | Achtung: Beide Hebel sinken – Banken könnten sich zurückziehen oder hohe Volatilität erwarten"; persistenter_kommentar = kommentar; persistenz_counter = 10
    verhältnis_neu = short_now - long_now
    if verhältnis_vorher * verhältnis_neu < 0:
        kommentar += " | 🔁 Hebel-Kreuzung erkannt – Bankenstruktur hat sich gedreht"; persistenter_kommentar = kommentar; persistenz_counter = 36
    verhältnis_vorher = verhältnis_neu
    try:
        rel_diff = abs(short_now - long_now) / ((abs(short_now) + abs(long_now)) / 2) * 100
        if rel_diff < 9: kommentar += " | Banken unsicher "
    except ZeroDivisionError:
        pass
    if timestamp:
        # log_ampel_event entfernt
        if index_change is not None: log_index_event(timestamp, index_change)
    return kommentar

def determine_ampel_signal(df):
    if len(df) < 1:
        return 0.5, "-", "⚪ Warte auf Daten", "-", "-", "-"
    hebel_signal = "⚪ Warte auf Daten"
    if len(df) >= 2:
        long_now, long_prev = df['long_avg'].iloc[-1], df['long_avg'].iloc[-2]
        short_now, short_prev = df['short_avg'].iloc[-1], df['short_avg'].iloc[-2]
        index_now = df['index_change'].iloc[-1]
        timestamp = df['timestamp'].iloc[-1]
        hebel_signal = bewerte_ampel(long_now, long_prev, short_now, short_prev, timestamp=timestamp, index_change=index_now, df_history=df)
    vola = df['index_change'].pct_change().abs().rolling(10).mean().iloc[-1] * 100 if len(df) >= 11 else 0
    if vola < 0.15: n, vola_text = 76, "Extrem ruhig – sehr niedrige Volatilität"
    elif vola < 0.3: n, vola_text = 54, "Ruhiger Markt – leichte Bewegung"
    elif vola < 0.4: n, vola_text = 36, "Aktiv – moderate Volatilität"
    else: n, vola_text = 24, "Hohe Volatilität"
    n = max(n, 8)
    if len(df) >= 180 and (df['timestamp'].iloc[-1] - df['timestamp'].iloc[0]) >= pd.Timedelta(minutes=20):
        span = df['index_change'].iloc[-min(60, len(df)):]
        tagesverlauf_text = "Tagesverlauf: Seitwärts (< 0.3 %)" if (span.max() - span.min()) < 0.3 else "-"
    else:
        tagesverlauf_text = "-"
    rel_pos = 0.5; ampel3_signal = "-"
    return rel_pos, ampel3_signal, hebel_signal, f"Aktuell: {vola_text}", "-", tagesverlauf_text

def get_market_hours_comment(underlying):
    market_comment = is_market_open(underlying)
    o_ber, c_ber = market_window_local("USA")
    return f"{market_comment} (Öffnungszeiten: {o_ber.strftime('%H:%M')}-{c_ber.strftime('%H:%M')} Uhr MEZ/MESZ)"


# --- Finanztreff: generischer Vola-Parser ---
def _ft_accept_cookies_quick(d, timeout=WAIT_MED):
    try:
        WebDriverWait(d, timeout).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        for how, sel in [
            (By.CSS_SELECTOR, "button#onetrust-accept-btn-handler"),
            (By.XPATH, "//button[contains(., 'Akzeptieren') or contains(., 'Zustimmen') or contains(., 'Accept All')]"),
        ]:
            try:
                btn = d.find_element(how, sel)
                if btn.is_displayed():
                    btn.click()
                    break
            except Exception:
                continue
    except Exception:
        pass

def _finanztreff_allowed_for_vola(underlying: str) -> bool:
    now = datetime.now(TZ_BERLIN)
    if underlying in ("Dax", "EURO STOXX 50"):
        start = now.replace(hour=9, minute=0, second=0, microsecond=0)
        end   = now.replace(hour=9, minute=40, second=0, microsecond=0)
        if start <= now < end:
            return False
    return True


# --- NEU: Futures-Bestätigungsfilter (>70%-Sprünge) ---
from collections import defaultdict

# pro Underlying eigener Filterzustand
FUTURES_FILTERS = defaultdict(lambda: OneOutlierFilter(
    rel_thresh=0.70,   # Sprung, wenn |Δ| > 70% vom Basiswert
    big_thresh=1.20,   # sehr großer Sprung > 120%
    small_blocks=1,    # 1 Tick Bestätigung
    big_blocks=2       # 2 Ticks bei sehr großem Sprung
))

def stabilize_future_pct(underlying: str, raw: float | None) -> float | None:
    """
    Nimmt den rohen Futures-%-Wert und gibt einen stabilisierten Wert zurück.
    - Kleine Abweichungen gehen sofort durch.
    - Sehr große Sprünge werden erst nach 1–2 Ticks bestätigt.
    - 0.0/NaN/inf → verwirft und nutzt den letzten gültigen Wert.
    """
    if not _is_valid_pct(raw):  # 0.0, None, inf, |raw|>=12 -> verwerfen
        return _LAST_GOOD_FUT.get(underlying)

    f = FUTURES_FILTERS[underlying]
    v = f.update(float(raw))   # OneOutlierFilter schon vorhanden
    if v is None:
        # Sprung noch unbestätigt -> letzten gültigen Wert behalten
        return _LAST_GOOD_FUT.get(underlying)
    _LAST_GOOD_FUT[underlying] = v
    return v

def reset_futures_filter(underlying: str | None = None):
    """Beim Underlying-Wechsel/Reset aufrufen."""
    if underlying is None:
        for u, flt in FUTURES_FILTERS.items():
            try: flt.reset()
            except: pass
        _LAST_GOOD_FUT.clear()
    else:
        try: FUTURES_FILTERS[underlying].reset()
        except: pass
        _LAST_GOOD_FUT.pop(underlying, None)

        

def _finanztreff_vola_change(token: str) -> float | None:
    """
    Liest % direkt im Kontext der Zeile, die das Token enthält (z.B. 'VSTOXX', 'VIX').
    Normalisiert Unicode-Minus und prüft Plausibilität.
    """
    try:
        d = get_driver("general")
        d.get("https://www.finanztreff.de/")
        _ft_accept_cookies_quick(d)
        WebDriverWait(d, 15).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        time.sleep(1.0)

        # 1) Versuche DOM-Kontext: Knoten mit Token, dann in Vorfahren/Kindern Prozentwert suchen
        for xp in [
            f"//*[contains(translate(normalize-space(.), '{token.lower()}', '{token.lower()}'), '{token}')]",
            f"//*[contains(normalize-space(.), '{token}')]",
        ]:
            try:
                el = d.find_element(By.XPATH, xp)
                block_text = el.text
                # ggf. ein bis zwei Ebenen Eltern prüfen
                parent = el
                for _ in range(3):
                    try:
                        parent = parent.find_element(By.XPATH, "..")
                        block_text += " " + parent.text
                    except Exception:
                        break
                block_text = block_text.replace("−", "-")
                m = re.search(r"([+-]?\d+[.,]\d+)\s*%", block_text)
                if m:
                    val = float(m.group(1).replace(".", "").replace(",", "."))
                    if -20.0 <= val <= 20.0:
                        print(f"✔️ {token} (finanztreff): {val:.2f} %")
                        return round(val, 2)
            except Exception:
                pass

        # 2) Fallback: HTML parsen und in Textnähe des Tokens suchen (Fenster 160 Zeichen)
        soup = BeautifulSoup(d.page_source, "html.parser")
        text = soup.get_text(" ", strip=True).replace("−", "-")
        m_token = re.search(re.escape(token), text, flags=re.I)
        if m_token:
            snippet = text[m_token.start(): m_token.end() + 160]
            m = re.search(r"([+-]?\d+[.,]\d+)\s*%", snippet)
            if m:
                val = float(m.group(1).replace(".", "").replace(",", "."))
                if -20.0 <= val <= 20.0:
                    print(f"✔️ {token} (finanztreff): {val:.2f} %")
                    return round(val, 2)
    except Exception as e:
        print(f"⚠️ {token} finanztreff fehlgeschlagen: {e}")
    return None


def get_vstoxx_change_finanztreff():
    return None




def get_vix_change_finanztreff():     return _finanztreff_vola_change("VIX")
def get_vxd_change_finanztreff():     return _finanztreff_vola_change("VXD")
def get_vxn_change_finanztreff():     return _finanztreff_vola_change("VXN")

_AMP1_STATE = {}  # key: underlying -> {"color": str, "hold": int, "mode": str}
def _ampel1_status_core(idx_change: float,
                        vola_change: float,
                        AMP1_MIN_MOVE_FLOOR: float,
                        vola_scale_q80: float,
                        vola_over_index: bool,
                        underlying: str,
                        vola_name: str) -> tuple[str, str]:
    """
    Ampel 1 mit Hysterese und Mindestdauer für Orange:
      Fall 1: Vola < Index => grün
      Fall 2: Vola < Index & Vola ↑ deutlich => orange ("Achtung, Vola steigt")
      Fall 3: Vola > Index => rot
      Fall 4: Vola > Index & Vola ↓ deutlich => orange ("Vola fällt wieder, Entspannung möglich")
    Zusatz-Kommentare:
      - Vola > Index & Vola ↑ deutlich => rot, "Stressphase, Risiko hoch"
      - Index ↑ & Vola ↓ deutlich (bei Vola < Index) => grün, "steigender Trend, Risiko gering"
    Hysterese:
      - Orange bleibt min. HOLD_MIN Zyklen.
      - Rückschalten erst, wenn Bewegung unter Relax-Schwelle liegt.
    """
    # Schwellen
    thr = max(AMP1_MIN_MOVE_FLOOR, vola_scale_q80)  # Eintritt
    thr_relax = 0.8 * thr                             # Rückkehr (Hysterese)
    HOLD_MIN = 4                                      # Mindestdauer Orange (Zyklen)

    vola_up_strong   = vola_change >=  thr
    vola_down_strong = vola_change <= -thr
    vola_up_relax    = vola_change >=  thr_relax
    vola_down_relax  = vola_change <= -thr_relax

    st = _AMP1_STATE.get(underlying, {"color": None, "hold": 0, "mode": None})

    # 1) Basisfarbe + Kommentar ohne Hysterese
    if not vola_over_index:
        color = "green"
        comment = f"{vola_name} unter {underlying} → ruhig."
        if vola_up_strong:
            color = "orange"
            comment = f"{underlying} stabil, aber {vola_name} steigt → Achtung."
            mode = "ORANGE_LOW_UP"
        else:
            # Zusatzfall: Index ↑ & Vola ↓ stark → positives Umfeld
            if (idx_change > 0) and vola_down_strong:
                color = "green"
                comment = f"{underlying} (steigt) und {vola_name} (fällt) → steigender Trend, Risiko gering."
            mode = None
    else:
        color = "red"
        comment = f"{vola_name} über {underlying} → Risiko erhöht."
        if vola_down_strong:
            color = "orange"
            comment = f"{vola_name} fällt wieder → Entspannung möglich."
            mode = "ORANGE_HIGH_DOWN"
        elif vola_up_strong:
            color = "red"
            comment = f"{underlying} (fällt) und {vola_name} (steigt) → Stressphase, Risiko hoch."
            mode = None
        else:
            mode = None

    # 2) Hysterese nur für Orange
    if st["color"] == "orange":
        st["hold"] = max(0, st["hold"] - 1)
        prev_mode = st.get("mode")

        # Orange beibehalten, solange Mindestdauer nicht abgelaufen
        if st["hold"] > 0:
            color = "orange"
            # Kommentar passend zum bisherigen Modus belassen
            if prev_mode == "ORANGE_LOW_UP":
                comment = f"{underlying} stabil, aber {vola_name} steigt → Achtung."
            elif prev_mode == "ORANGE_HIGH_DOWN":
                comment = f"{vola_name} fällt wieder → Entspannung möglich."
        else:
            # Mindestdauer abgelaufen: nur zurückschalten, wenn unter Relax-Schwelle
            if prev_mode == "ORANGE_LOW_UP":
                if not vola_up_relax:
                    # Rückkehr erlaubt: Farbe aus aktueller Basisentscheidung
                    pass
                else:
                    color = "orange"
                    comment = f"{underlying} stabil, aber {vola_name} steigt → Achtung."
            elif prev_mode == "ORANGE_HIGH_DOWN":
                if not vola_down_relax:
                    pass
                else:
                    color = "orange"
                    comment = f"{vola_name} fällt wieder → Entspannung möglich."

    # 3) Wenn neu Orange wird, Hold setzen und Modus speichern
    if (st["color"] != "orange") and (color == "orange"):
        st["hold"] = HOLD_MIN
        st["mode"] = mode
    elif color != "orange":
        st["hold"] = 0
        st["mode"] = None

    # 4) State aktualisieren
    st["color"] = color
    _AMP1_STATE[underlying] = st

    return color, comment


#Ersetzt die statischen Titel durch einen dynamischen Helper (ampel 1)
def get_ampel1_title(u: str) -> str:
    """Erzeugt den dynamischen Titel für Ampel 1 mit passendem Volatilitätsindex."""
    vola = _vola_short(u)
    return f"Ampel 1: Zusammenhang {u} ↔ {vola} (sofort)"


def _amp1_trend_flags(df_window):
    """
    Liefert: up_trend:bool, down_trend:bool, rel_pos:float, v_now:float, i_now:float
    Trend = Verteilung (q20/q80) + Richtung in den letzten 3 Ticks.
    """
    s_vola = df_window["volatility_change"].dropna()
    s_idx  = df_window["index_change"].dropna()
    if len(s_vola) < 5 or len(s_idx) < 5:
        v_now = float(s_vola.iloc[-1]) if len(s_vola) else 0.0
        i_now = float(s_idx.iloc[-1])  if len(s_idx)  else 0.0
        return False, False, 0.5, v_now, i_now

    v_now = float(s_vola.iloc[-1])
    i_now = float(s_idx.iloc[-1])

    v_min = float(s_vola.min()); v_max = float(s_vola.max())
    rel_pos = (v_now - v_min) / (v_max - v_min) if v_max != v_min else 0.5

    q20 = float(s_vola.quantile(0.18))
    q80 = float(s_vola.quantile(0.82))

    recent = s_vola.tail(4)  # 3 Diffs
    diffs  = recent.diff().tail(3)
    up_cnt   = int((diffs > 0).sum())
    down_cnt = int((diffs < 0).sum())

    up_trend   = (v_now >= q80) and (up_cnt >= 2)
    down_trend = (v_now <= q20) and (down_cnt >= 2)
    return up_trend, down_trend, rel_pos, v_now, i_now

A1_MIN_POINTS_FOR_ORANGE = 15  # Schwelle, ab der Orange überhaupt zugelassen wird

def get_ampel1_status(df, selected_underlying):
    from datetime import time as dtime  # lokale Import-Absicherung

    # Region / Startzeiten je Underlying
    if selected_underlying in ("Dax", "EURO STOXX 50"):
        region = "EU"
        start_time = dtime(9, 30)
    elif selected_underlying in ("S&P 500", "Dow Jones", "Nasdaq 100"):
        region = "US"
        start_time = dtime(15, 25)   # wie von dir gewünscht
    else:
        region = "OTHER"
        start_time = None  # keine spezielle Sperre

    # Anzahl gültiger Vola-Werte
    valid = df["volatility_change"].notna().sum() if "volatility_change" in df.columns else 0

    # Uhrzeit in Berlin
    now = datetime.now(TZ_BERLIN).time()

    # Vor Markt-Start für die jeweilige Region:
    if start_time is not None and now < start_time:
        if region == "EU":
            msg = ("Keine Daten. Bitte warten."
                   "Dax/EURO STOXX: Vola ab ca. 09:30 verfügbar.")
        elif region == "US":
            msg = ("Keine Daten. Bitte warten. "
                   "USA (S&P 500, Dow, Nasdaq): Vola ab ca. 15:25 verfügbar.")
        else:
            msg = "Ampel 1: Vola noch nicht freigegeben."
        return FARBCODES["gray"], 0.5, msg

    # Nach Marktstart, aber noch gar keine Vola- oder Indexdaten
    if valid == 0 or "index_change" not in df.columns:
        return FARBCODES["gray"], 0.5, "Ampel 1: Keine Daten verfügbar."

    try:
        # nur letzte 75 Minuten behalten (Ampel-1-Zeitfenster)
        cutoff = datetime.now(TZ_BERLIN) - timedelta(minutes=75)
        ts = pd.to_datetime(df["timestamp"])
        if getattr(ts.dt, "tz", None) is None:
            ts = ts.dt.tz_localize(TZ_BERLIN)
        else:
            ts = ts.dt.tz_convert(TZ_BERLIN)

        df_window = df.loc[ts >= cutoff]

        # Falls im Zeitfenster nichts übrig bleibt → grau
        if df_window.empty:
            return FARBCODES["gray"], 0.5, "Ampel 1: Noch keine aktuellen Daten im Zeitfenster."

        # Trend-Flags + rel_pos + aktuelle Werte
        up_trend, down_trend, rel_pos, v_now, i_now = _amp1_trend_flags(df_window)

        vola_name = {
            "Dax": "VDAX",
            "S&P 500": "VIX",
            "EURO STOXX 50": "VSTOXX",
            "Dow Jones": "VXD",
            "Nasdaq 100": "VXN",
        }.get(selected_underlying, "Vola")

        tstamp = df_window["timestamp"].iloc[-1]
        tstr = tstamp.strftime("%H:%M") if hasattr(tstamp, "strftime") else str(tstamp)

        # Baseline nach Relativlage (Priorität)
        if "AMP1_BASELINE_LAST" not in globals():
            globals()["AMP1_BASELINE_LAST"] = {}
        last_base = globals()["AMP1_BASELINE_LAST"].get(selected_underlying, FARBCODES["green"])

        if v_now > i_now:
            base_color = FARBCODES["red"]
            base_text  = f"{vola_name} über {selected_underlying} → Risiko erhöht."
        elif v_now < i_now:
            base_color = FARBCODES["green"]
            base_text  = f"{vola_name} unter {selected_underlying} → positives Umfeld."
        else:
            base_color = last_base
            base_text  = f"{vola_name} ≈ {selected_underlying} → Basis unverändert."

        # Startzustand: nur Baseline (Ampel sofort rot/grün/grau möglich)
        color = base_color
        text  = base_text

        # Wieviele Punkte im Zeitfenster für Orange verfügbar?
        num_points_window = df_window["volatility_change"].notna().sum()

        # Zusatz: Index-Richtung kurz prüfen (3 Ticks)
        idx_diffs = df_window["index_change"].dropna().tail(4).diff().tail(3)
        idx_up   = int((idx_diffs > 0).sum()) >= 2
        idx_down = int((idx_diffs < 0).sum()) >= 2

        # Orange-Logik nur, wenn genug Daten vorhanden
        if num_points_window >= A1_MIN_POINTS_FOR_ORANGE:
            if base_color == FARBCODES["green"] and up_trend:
                color = FARBCODES["orange"]
                text  = f"{selected_underlying} ↑, {vola_name} ↑ deutlich → Trendwende möglich."
            elif base_color == FARBCODES["red"] and down_trend:
                color = FARBCODES["orange"]
                text  = f"{selected_underlying} ↓, {vola_name} ↓ deutlich → Entspannung möglich."
            else:
                if idx_up and up_trend:
                    color = FARBCODES["orange"]
                    text  = f"{selected_underlying} ↑, {vola_name} ↑ deutlich → Trendwende möglich."
                elif idx_down and down_trend:
                    color = FARBCODES["orange"]
                    text  = f"{selected_underlying} ↓, {vola_name} ↓ deutlich → Entspannung möglich."
        # Wenn num_points_window < A1_MIN_POINTS_FOR_ORANGE:
        # → keine Orange-Übersteuerung, Baseline (rot/grün/grau) bleibt

        # Min/Max-Info wie zuvor
        vmin = float(df_window['volatility_change'].min())
        vmax = float(df_window['volatility_change'].max())
        text += f" {vola_name}: {v_now:+.2f} %, ( Min {vmin:.2f}%, Max {vmax:.2f}% )."

        # --- Kleiner Zeitpuffer gegen Flackern ---
        HOLD_SEC_ORANGE_RED = 8
        now_ts = time.time()

        if "AMP1_STATE" not in globals():
            globals()["AMP1_STATE"] = {}  # key: underlying -> {"color": str, "t": float}

        st = globals()["AMP1_STATE"].get(selected_underlying, {"color": None, "t": 0.0})
        last_color = st["color"]
        last_t     = st["t"]

        if last_color is not None and color != last_color:
            is_orange_red_jump = (
                (color == FARBCODES["orange"] and last_color == FARBCODES["red"]) or
                (color == FARBCODES["red"]    and last_color == FARBCODES["orange"])
            )
            if is_orange_red_jump and (now_ts - last_t) < HOLD_SEC_ORANGE_RED:
                color_effective = last_color
            else:
                color_effective = color
                st = {"color": color_effective, "t": now_ts}
                globals()["AMP1_STATE"][selected_underlying] = st
        else:
            color_effective = color
            if last_color is None:
                st = {"color": color_effective, "t": now_ts}
                globals()["AMP1_STATE"][selected_underlying] = st

        globals()["AMP1_BASELINE_LAST"][selected_underlying] = base_color
        return color_effective, float(rel_pos), text

    except Exception as e:
        return FARBCODES["gray"], 0.5, f"Fehler Ampel 1: {e}"





########################### USA Ampel 4 Upgrade RSI+Fear ##################
def bewerte_ampel4_usa(rsi: float, fear: float):
    """
    Kombiniert RSI und CNN Fear&Greed für US-Indizes.
    Gibt Farbe ("green","orange","red","gray") und Kommentar-Text zurück.
    """



    # Fallback: neutral, wenn Fear ungültig
    if fear is None or not math.isfinite(fear):
        fear = 50  # neutral
        fear_valid = False
    else:
        fear_valid = True

    # Mini-Ampeln
    rsi_led  = "🟢" if rsi < RSI_WARN else ("🟠" if rsi < RSI_OVERBOUGHT else "🔴")
    if fear < 25:
        fear_led = "🔴"  # Extreme Angst
    elif fear <= 75:
        fear_led = "⚪"  # Neutral
    else:
        fear_led = "🔴"  # Extreme Gier

    # Bestimme die Hauptfarbe basierend auf der schlechtesten Mini-Ampel
    if rsi_led == "🔴" or fear_led == "🔴":
        color = "red"
    elif rsi_led == "🟠" or fear_led == "🟠":
        color = "orange"
    else:
        color = "green"

    if rsi is not None and math.isfinite(rsi) and fear_valid:
        # Kombinationsmatrix inkl. RSI_WARN–RSI_OVERBOUGHT Bereich
        if rsi < 30 and fear < 25:
            note = "Extreme Angst + Überverkauft. Antizyklisch Long begünstigt."
        elif 30 <= rsi < RSI_WARN and fear < 25:
            note = "Extreme Angst bei neutralem RSI. Pullback-Long nur mit Trendfilter."
        elif rsi < 30 and 25 <= fear <= 75:
            note = "Überverkauft. Technischer Rebound möglich."
        elif 30 <= rsi < RSI_WARN and fear > 75:
            note = "Euphorie ohne Überkauft-Bestätigung. Rückschlagrisiko erhöht."
        elif RSI_WARN <= rsi < RSI_OVERBOUGHT and 25 <= fear <= 75:
            note = "RSI-Warnung bei neutralem Sentiment. Rückfallrisiko erhöht."
        elif RSI_WARN <= rsi < RSI_OVERBOUGHT and fear > 75:
            note = "RSI-Warnung + Gier. Rückschlagrisiko."
        elif RSI_WARN <= rsi < RSI_OVERBOUGHT and fear < 25:
            note = "Widerspruch: RSI-Warnung bei Angst. Kein klares Signal."
        elif rsi >= RSI_OVERBOUGHT and 25 <= fear <= 75:
            note = "Überkauft bei neutralem Sentiment. Gewinnsicherung ratsam."
        elif rsi >= RSI_OVERBOUGHT and fear > 75:
            note = "Überkauft + Extreme Gier. Short-Setup begünstigt."
        elif rsi < 30 and fear > 75:
            note = "Widerspruch: Überverkauft bei extremer Gier. Kein Signal."
        elif rsi >= RSI_OVERBOUGHT and fear < 25:
            note = "Widerspruch: Überkauft bei extremer Angst. Kein Signal."
        else:
            note = "Neutraler Bereich. Kein klares Signal."
    else:
        note = "Keine validen Werte. Ampel neutral."

    # Ausgabe-Kommentar
    _, _, rsi_text = bewerte_rsi_ampel(rsi)
    rsi_comment = f"{rsi_led} {rsi_text}"
    fear_comment = f"{fear_led} Fear & Greed = {fear:.0f}"
    line = f"{rsi_comment}<br>{fear_comment} — {note}"

    return color, line


import os, csv, datetime as dt, re, requests
from bs4 import BeautifulSoup

FNG_CSV = "data/fear_greed_us.csv"
# CNN Fear & Greed JSON-API
_CNN_FNG_API = "https://production.dataviz.cnn.io/index/fearandgreed/graphdata"
_CNN_FNG_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en-US,en;q=0.9",
    "Referer": "https://edition.cnn.com/markets/fear-and-greed",
    "Origin": "https://edition.cnn.com",
    "Connection": "keep-alive",
}


def _read_fng_cache():
    if not os.path.exists(FNG_CSV): return None
    rows = {}
    with open(FNG_CSV, newline="", encoding="utf-8") as f:
        for d,v in csv.reader(f):
            rows[d] = int(v)
    return rows

def _write_fng_cache(rows: dict):
    os.makedirs(os.path.dirname(FNG_CSV), exist_ok=True)
    with open(FNG_CSV, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f); [w.writerow([d, rows[d]]) for d in sorted(rows)]

# in fetch_cnn_fng()
from decimal import Decimal, ROUND_HALF_UP

def fetch_cnn_fng() -> int:
    r = requests.get(_CNN_FNG_API, headers=_CNN_FNG_HEADERS, timeout=20)
    r.raise_for_status()
    js = r.json()
    fg = js.get("fear_and_greed")
    score = fg.get("score") if isinstance(fg, dict) else fg
    # half-up statt Abriss
    return int(Decimal(str(score)).quantize(0, rounding=ROUND_HALF_UP))


def get_seasonal_image() -> str:
    """Liefert den Bildnamen je nach Jahreszeit."""
    month = datetime.now().month
    if month in (12, 1, 2):
        return "meinbild_winter.jpg"
    elif month in (3, 4, 5):
        return "meinbild_fruehling.jpg"
    elif month in (6, 7, 8):
        return "meinbild_sommer.jpg"
    elif month in (9, 10, 11):
        return "meinbild_herbst.jpg"
    return "meinbild2.jpg"  # Fallback

# Falls du Fasching extra willst:
def get_seasonal_image() -> str:
    month, day = datetime.now().month, datetime.now().day
    if (month == 2 and 1 <= day <= 20):  # grob Faschingszeitraum
        return "meinbild_fasching.jpg"
    elif month in (12, 1, 2):
        return "meinbild_winter.jpg"
    elif month in (3, 4, 5):
        return "meinbild_fruehling.jpg"
    elif month in (6, 7, 8):
        return "meinbild_sommer.jpg"
    elif month in (9, 10, 11):
        return "meinbild_herbst.jpg"
    return "meinbild2.jpg"



def get_fng_today(force_refresh: bool = False, min_refresh_sec: int = 900) -> int:
    today = dt.date.today().isoformat()
    now = time.time()
    rows = _read_fng_cache() or {}

    if not force_refresh and today in rows and now - _FNG_RT["ts"] < min_refresh_sec:
        return rows[today]

    try:
        val = fetch_cnn_fng()
        rows[today] = int(val)
        _write_fng_cache(rows)
        _FNG_RT.update({"ts": now, "val": val})
        return rows[today]
    except Exception:
        return rows.get(today, 50)

##################################################


def _scrape_finanztreff_header(names):
    d = get_driver("general", KEY_GLOBAL)
    d.get("https://www.finanztreff.de/")
    _ft_accept_cookies(d)
    WebDriverWait(d, WAIT_BODY, poll_frequency=POLL).until(
        EC.presence_of_element_located((By.TAG_NAME, "body"))
    )
    # Warten bis irgendwo ein % auftaucht
    WebDriverWait(d, WAIT_READY, poll_frequency=POLL).until(
        lambda drv: "%" in (drv.page_source or "")
    )

    text = d.find_element(By.TAG_NAME, "body").text
    out = {}
    for name in names:
        m = re.search(re.escape(name), text, flags=re.I)
        if not m: 
            continue
        snippet = text[m.end(): m.end() + 160]
        m_pct = re.search(r"([+-]?\d+[.,]\d+)\s*%", snippet)
        if m_pct:
            out[name] = float(m_pct.group(1).replace(",", "."))
    return out




def _scrape_finanztreff_markets_estoxx50():
    d = get_driver("general", KEY_GLOBAL)
    d.get("https://www.finanztreff.de/")
    _ft_accept_cookies(d)

    WebDriverWait(d, 10).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
    # Warten bis Märkte-Tabelle geladen ist (heuristisch: irgendein % auftaucht)
    WebDriverWait(d, 5).until(lambda drv: "%" in (drv.page_source or ""))

    soup = BeautifulSoup(d.page_source, "html.parser")
    target = None
    for t in soup.find_all(string=re.compile(r"\bE\.?\s*Stoxx\s*50\b", re.I)):
        node = t.parent
        for _ in range(5):
            if node and node.name in ("div", "tr"):
                target = node; break
            node = node.parent
        if target: break
    if not target:
        return None

    row_text = target.get_text(" ", strip=True)
    m_pct = re.search(r"([+-]?\d+[.,]\d+)\s*%", row_text)
    if not m_pct:
        for cell in target.find_all(["span", "td", "div"]):
            txt = cell.get_text(" ", strip=True)
            m_pct = re.search(r"([+-]?\d+[.,]\d+)\s*%", txt)
            if m_pct:
                break
    return float(m_pct.group(1).replace(",", ".")) if m_pct else None


def get_index_change_from_finanztreff(underlying):
    """
    Backup-Lieferant für %-Änderung:
    - EURO STOXX 50 -> aus Märkte-Tabelle ('E. Stoxx 50')
    - Dax, S&P 500, Nasdaq, Dow Jones -> aus Header-Leiste
    """
    if underlying == "EURO STOXX 50":
        try:
            return _scrape_finanztreff_markets_estoxx50()
        except Exception as e:
            print("finanztreff ES50 fail:", e)
            return None
    label_map = {
        "Dax": "DAX",
        "S&P 500": "S&P 500",
        "Nasdaq 100": "NASDAQ 100",
        "Dow Jones": "Dow 30",
    }
    label = label_map.get(underlying)
    if not label:
        return None
    try:
        vals = _scrape_finanztreff_header((label,))
        return vals.get(label)
    except Exception as e:
        print("finanztreff header fail:", e)
        return None
# === /finanztreff.de Backup ===

#Fallback vstoxx
def _stoxx_accept_cookies(d, timeout=10):
    try:
        WebDriverWait(d, timeout).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        # häufig OneTrust
        for how, sel in [
            (By.CSS_SELECTOR, "button#onetrust-accept-btn-handler"),
            (By.XPATH, "//button[contains(., 'Accept All') or contains(., 'Akzeptieren') or contains(., 'Zustimmen')]"),
        ]:
            try:
                btn = d.find_element(how, sel)
                if btn.is_displayed():
                    btn.click(); time.sleep(0.6); break
            except Exception:
                pass
    except Exception:
        pass



############



# --- VDAX Fallback über finanztreff.de (robust, mit Mini-Cache) ---
# --- VDAX Fallback über finanztreff.de: immer % zurückgeben ---
_FT_VDAX_CACHE = {"ts": 0.0, "val": None}

# --- VDAX Fallback über finanztreff.de: garantiert Prozent, nie Punkte ---

# --- VDAX Fallback über finanztreff.de: garantiert Prozent, nie Punkte ---
def get_vdax_change_finanztreff(timeout=6) -> float | None:
    """
    VDAX %-Änderung von finanztreff.de via gezielten Selektoren.
    Kein page_source, keine Volltext-Regex.
    """
    url = "https://www.finanztreff.de/index/vdax-new"
    d = get_driver("general", KEY_GLOBAL)

    try:
        d.get(url)
    except Exception:
        return None

    # Einmalig Cookies wegklicken, falls Helper existiert
    try:
        _ft_accept_cookies(d)
    except Exception:
        pass

    # Seite bereit
    try:
        WebDriverWait(d, timeout, poll_frequency=0.20).until(
            EC.presence_of_element_located((By.TAG_NAME, "body"))
        )
    except Exception:
        return None

    # 1) Direkt den %-Wert greifen (typisch in einem <span> o.ä.)
    try:
        el = WebDriverWait(d, timeout, poll_frequency=0.20).until(
            EC.visibility_of_element_located((
                By.XPATH,
                # nimm das erste sichtbare Element, das ein Prozentzeichen enthält
                "(//span[contains(normalize-space(.), '%')]"
                " | //div[contains(normalize-space(.), '%')]"
                " | //td[contains(normalize-space(.), '%')])[1]"
            ))
        )
        txt = el.text.strip()
        # Prozent extrahieren ohne page_source
        m = re.search(r"([+\-]?\d+(?:[.,]\d+)?)\s*%", txt)
        if m:
            return round(float(m.group(1).replace(",", ".")), 2)
    except Exception:
        pass

    # 2) Fallback ohne page_source:
    #    Aus "Aktuell" und "Vortag/Schluss" die Punkte lesen und prozentuale Änderung berechnen.
    def _num_from_label(label_xp: str) -> float | None:
        try:
            # Zelle mit Label finden, dann die erste Zahl rechts daneben greifen
            lab = d.find_element(By.XPATH, label_xp)
            cell = lab.find_element(By.XPATH, "following::td[1]//*[self::span or self::div or self::td]")
            txtn = cell.text.strip()
            # Zahl tolerant parsen (1.234,56 oder 1234,56)
            n = re.search(r"\d{1,3}(?:\.\d{3})*(?:,\d+)?|\d+(?:,\d+)?", txtn)
            if not n:
                return None
            return float(n.group(0).replace(".", "").replace(",", "."))
        except Exception:
            return None

    cur = _num_from_label("//td[.//text()[contains(., 'Aktuell') or contains(., 'Zuletzt') or contains(., 'Letzter')]]")
    prev = _num_from_label("//td[.//text()[contains(., 'Vortag') or contains(., 'Schluss') or contains(., 'Vorh.')]]")

    if cur is not None and prev and prev > 0:
        return round(((cur - prev) / prev) * 100.0, 2)

    return None




def get_vdax_change_yahoo():
    """Versucht ^VDAX, danach ^VDAXI. Liefert %-Tagesänderung."""
    for ticker in ("^VDAX", "^VDAXI"):
        try:
            data = yf.Ticker(ticker).history(period="2d")
            if len(data) >= 2:
                prev = data["Close"].iloc[-2]
                curr = data["Close"].iloc[-1]
                return round((curr - prev) / prev * 100, 2)
        except Exception:
            continue
    return None

#########Hebelabruf soll nicht ganze Programm verzögern, extre Prozess andere aktualisieren weiter##########
def _leverage_loop():
    global _LEVER_CACHE
    # Start-Offset, damit der erste Hebelabruf nicht mit dem ersten Update tick kollidiert
    try:
        time.sleep(2.0)
    except Exception:
        pass

    tick = time.monotonic()
    while not stop_event.is_set():
        start = time.monotonic()
        try:
            u = get_selected_underlying()
            urls = UNDERLYINGS.get(u, {})
            if not urls:
                time.sleep( max(5, int(refresh_interval) + 2) )
                continue

            # schnelle Einzel-Scrapes
            lv = scrape_average_leverage(urls.get("long"),  urls.get("long_finanzen"))
            sv = scrape_average_leverage(urls.get("short"), urls.get("short_finanzen"))

            # Cache aktualisieren
            now = time.time()
            entry = _LEVER_CACHE.setdefault(u, {"long": None, "short": None, "ts": 0})
            if lv is not None:
                entry["long"] = float(lv); entry["ts"] = now
            if sv is not None:
                entry["short"] = float(sv); entry["ts"] = now

        except Exception as e:
            print(f"⚠ update_data: {e}")
        tick += refresh_interval

        # Periodisierung: Hauptintervall + 2 s Abstand
        delay = max(0.0, tick - time.monotonic())
        time.sleep(delay)


def last_query_badge(underlying:str, thresh=30):
    lb, _ = _read_health()                    # last_beat, last_ok
    ts = int(lb) if lb else 0
    txt = "—" if not ts else time.strftime("%H:%M:%S", time.localtime(ts))
    age = 1e9 if not ts else (time.time() - ts)
    color = "red" if age > thresh else "#888"
    return f"Letzte Abfrage: {txt}", color



def start_leverage_thread():
    global _lever_thread, stop_event
    if 'stop_event' not in globals() or stop_event is None:
        stop_event = threading.Event()
    if _lever_thread and _lever_thread.is_alive():
        return
    _lever_thread = threading.Thread(target=_leverage_loop, name="leverage_loop", daemon=True)
    _lever_thread.start()
###########
def _cached_future_change(u: str):
    now = time.time()
    ent = _FUTURES_CACHE
    if ent["u"] == u and (now - ent["ts"]) < FUTURES_TTL:
        return ent["val"]
    try:
        v = get_future_change_pct(u)
    except Exception:
        v = None
    ent.update({"u": u, "val": v, "ts": now})
    return v

def _cached_index_change(u: str):
    now = time.time()
    ent = _INDEX_CACHE
    if ent["u"] == u and (now - ent["ts"]) < INDEX_TTL:
        return ent["val"]
    val = None
    try:
        idx = get_index_data(u)
        if idx and len(idx) == 3:
            val = idx[0]
        if val is None:
            ft = get_index_change_from_finanztreff(u)
            if ft is not None:
                val = ft
    except Exception:
        pass
    ent.update({"u": u, "val": val, "ts": now})
    return val


# oben einfügen
_last_csv_write = {"ts": 0}

def update_data():
    global last_fetch_time
    global _last_csv_write
    if 'first_run' not in globals():
        globals()['first_run'] = True
        _LEVER_CACHE.clear()
        print("✅ Cache beim Start geleert")    

    while not stop_event.is_set():
        _beat()  # <— Loop lebt
        try:
            # aktuelles Underlying
            cu = get_selected_underlying()
            urls = UNDERLYINGS.get(cu, {})
            if not urls or "long" not in urls or "short" not in urls:
                print(f"⚠️ Keine URLs für {cu}")
                time.sleep(refresh_interval)
                continue

            # --- Hebel: nur Cache verwenden, IO entkoppelt ---
            cache = _LEVER_CACHE.get(cu, {})
            is_fresh = (time.time() - float(cache.get("ts", 0))) < _LEVER_TTL
            long_cached  = cache.get("long", None)  if is_fresh else None
            short_cached = cache.get("short", None) if is_fresh else None

            # Fallbacks: wenn Cache leer, nimm letzten Filter-Wert
            long_avg_raw  = long_cached  if long_cached  is not None else LEVER_LONG_FILTER.last()
            short_avg_raw = short_cached if short_cached is not None else LEVER_SHORT_FILTER.last()

            # --- Indexänderung (%): Nasdaq zuerst Finanztreff (strict/validated), sonst Standard ---
            index_change_raw, index_display_value = (None, "-")
            if cu == "Nasdaq 100":
                try:
                    index_change_raw = (
                        get_nasdaq_change_finanztreff_validated()
                        or (get_index_data(cu) or (None, "-", None))[0]
                    )
                except NameError:
                    ft_change = get_index_change_from_finanztreff(cu)
                    if ft_change is not None:
                        index_change_raw = ft_change
                    else:
                        idx = get_index_data(cu)
                        if idx and len(idx) == 3:
                            index_change_raw, index_display_value, _ = idx
            else:
                idx = get_index_data(cu)
                if idx and len(idx) == 3:
                    index_change_raw, index_display_value, _ = idx
                if index_change_raw is None:
                    ft_change = get_index_change_from_finanztreff(cu)
                    if ft_change is not None:
                        index_change_raw = ft_change
            # --- Futures (% ggü. Vortagesschluss) ---
            try:
                futures_now_raw = get_future_change_pct(cu)   # bleibt live, ohne TTL
            except Exception:
                futures_now_raw = None
            futures_now = futures_now_raw

            # --- Volatilität ---
            vola_change_raw = get_volatility_change(cu)

            # --- Top-10 Ø gleichgewichtet ---




            # --- Filter ---
            long_avg  = LEVER_LONG_FILTER.update(long_avg_raw)
            short_avg = LEVER_SHORT_FILTER.update(short_avg_raw)

            tmp = INDEX_FILTER.update(index_change_raw)
            index_change = tmp if tmp is not None else INDEX_FILTER.last()

            vola_change = VOL_FILTER.update(vola_change_raw)
            if vola_change is None:
                vola_change = VOL_FILTER.last()

           

            print(f"Volatility change for {cu}: {vola_change}")

            # --- Persistenz ---
            if index_change is not None and abs(index_change) < 10:
                timestamp = pd.Timestamp.now(tz=TZ_BERLIN)
                filename = get_csv_filename(cu)

                row = {
                    "timestamp": timestamp,
                    "long_avg": long_avg if long_avg is not None else np.nan,
                    "short_avg": short_avg if short_avg is not None else np.nan,
                    "index_change": index_change,
                    "volatility_change": vola_change,
                    "futures_avg": futures_now if futures_now is not None else np.nan,
                }

                # Throttle: nur 1x pro Intervall schreiben
                now = time.time()
                if now - _last_csv_write["ts"] >= refresh_interval:
                    try:
                        if os.path.exists(filename):
                            try:
                                old = pd.read_csv(filename)
                                if not old.empty:
                                    if "futures_avg" not in old.columns:
                                        old["futures_avg"] = np.nan
                                    new_row = pd.DataFrame([row])
                                    # Spalten angleichen, um FutureWarning zu vermeiden
                                    for col in set(old.columns) - set(new_row.columns):
                                        new_row[col] = np.nan
                                    for col in set(new_row.columns) - set(old.columns):
                                        old[col] = np.nan
                                    df = pd.concat([old, new_row], ignore_index=True, copy=False)
                                else:
                                    df = pd.DataFrame([row])
                            except Exception as e:
                                print(f"⚠️ Konnte alte CSV nicht lesen: {e}")
                                df = pd.DataFrame([row])
                        else:
                            df = pd.DataFrame([row])

                        atomic_write_csv(df, filename)
                        _last_csv_write["ts"] = now
                    except Exception as e:
                        print(f"⚠️ Konnte CSV nicht schreiben: {e}")

                last_fetch_time = timestamp.strftime("%H:%M:%S")

        except Exception as e:
            print(f"⚠️ Fehler in update_data: {e}")

        time.sleep(refresh_interval)



def stop_update_thread(timeout=5):
    """Update-Loop anhalten und Thread ggf. joinen."""
    global update_thread, stop_event
    try:
        if 'stop_event' in globals() and stop_event:
            stop_event.set()
    except Exception:
        pass
    if 'update_thread' in globals() and update_thread and update_thread.is_alive():
        update_thread.join(timeout=timeout)
    update_thread = None

def start_update_thread():
    """Update-Loop nur starten, wenn keiner läuft."""
    global update_thread, stop_event
    if 'stop_event' not in globals() or stop_event is None:
        stop_event = threading.Event()
    else:
        stop_event.clear()

    if 'update_thread' in globals() and update_thread and update_thread.is_alive():
        return

    # Wichtig: target = update_data
    update_thread = threading.Thread(target=update_data, name="update_loop", daemon=True)
    update_thread.start()





def _ft_html():
    d = get_driver("general")
    d.get("https://www.finanztreff.de/")
    _ft_accept_cookies_quick(d)
    WebDriverWait(d, 15).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
    time.sleep(1.0)
    return d.page_source

def _yf_pct_ndx():
    # kurze Yahoo-Kontrolle für Plausibilität
    try:
        import yfinance as yf
        t = yf.Ticker("^NDX")
        fi = getattr(t, "fast_info", {}) or {}
        last = fi.get("last_price"); prev = fi.get("previous_close")
        if last and prev and prev > 0:
            return 100.0 * (last/prev - 1.0)
        df = t.history(period="1d", interval="1m", prepost=True, auto_adjust=False)
        if df is not None and not df.empty:
            base = float(df["Close"].iloc[0]); cur = float(df["Close"].iloc[-1])
            if base > 0:
                return 100.0 * (cur/base - 1.0)
    except Exception:
        return None
    return None

def get_nasdaq_change_finanztreff_strict():
    """
    Extrahiert NUR den Wert direkt im Umfeld von 'Nasdaq-100'.
    Vermeidet News-/Seitenleisten-Treffer.
    """
    try:
        html = _ft_html()
        # auf kleine Segmente um das Label 'Nasdaq-100' beschränken
        for pat in ("NASDAQ-100", "Nasdaq-100", "NASDAQ 100", "Nasdaq 100"):
            i = html.find(pat)
            if i == -1:
                continue
            seg = html[i:i+220]  # nur unmittelbares Umfeld
            text = BeautifulSoup(seg, "html.parser").get_text(" ", strip=True)
            m = re.search(r"([+-]?\d{1,2}[.,]\d{2})\s*%", text)
            if m:
                return float(m.group(1).replace(",", "."))
    except Exception as e:
        print(f"⚠️ get_nasdaq_change_finanztreff_strict: {e}")
    return None

def get_nasdaq_change_finanztreff_validated():
    ft = get_nasdaq_change_finanztreff_strict()
    if ft is None:
        return None
    yf = _yf_pct_ndx()
    # nur verwerfen, wenn signifikant abweichend
    if yf is not None and abs(ft - yf) > 0.35:
        print(f"⚠️ Nasdaq FT≠YF ({ft:.2f}% vs {yf:.2f}%) → nutze Yahoo")
        return yf
    return ft



def get_vol_label(selected_underlying):
    return {"Dax":"VDAX (niedrig=gut)","S&P 500":"VIX (niedrig=gut)","EURO STOXX 50":"VSTOXX (niedrig=gut)","Dow Jones":"VXD (niedrig=gut)","Nasdaq 100":"VXN (niedrig=gut)"}.get(selected_underlying,"Volatilität")

#Für Umschalter Dax Variante#
UNDERLYING_OPTIONS_ALL = [{'label': ('Nasdaq 100' if k=='Nasdaq 100' else k), 'value': k}
                          for k in UNDERLYINGS.keys()]
UNDERLYING_OPTIONS_DAX = [{'label': 'Dax', 'value': 'Dax'}]

# -----------------------------------------------
# -----------------------------------------------
# Layout
# -----------------------------------------------
# Graph-Höhe je nach Variante
GRAPH_HEIGHT = "90vh"
if SERVER_VARIANT:
    GRAPH_HEIGHT = "40vh"   # oder "55vh" / "50vh", nach Geschmack testen


app.layout = html.Div([
    dcc.Store(id="app_state", data={"shutdown": False}),

    html.Div([
        html.H1("Leverage Lens", id="exit-title", style={
            "fontSize": "56px",
            "fontWeight": "bold",
            "textAlign": "center",
            "background": "linear-gradient(90deg, red, orange, yellow, green, blue, violet)",
            "WebkitBackgroundClip": "text",
            "WebkitTextFillColor": "transparent",
            "cursor": "pointer",
            "display": "inline-block",
            "marginRight": "10px"
        }),
        html.Span("v1.92", style={"fontSize": "16px", "color": "#666", "verticalAlign": "super"}),
        dcc.ConfirmDialog(id="confirm-exit", message="- Leverage Lens - beenden? Dannach Fenster schließen")
    ], style={"textAlign": "center", "marginBottom": "20px"}),

    html.Div(
        dcc.Dropdown(
            id="underlying-dropdown",
            options=(UNDERLYING_OPTIONS_DAX if DEMO_DAX_ONLY else UNDERLYING_OPTIONS_ALL),
            value=('Dax' if DEMO_DAX_ONLY else selected_underlying),
            style={"width": "300px", "fontWeight": "bold", "fontSize": "22px"}
        ),
        style={"display": "flex", "justifyContent": "center", "margin": "5px 0"}
    ),

    html.Div(
        id="index-info",
        children=[
            html.Div(id="last-fetch-time", style={"fontSize": "16px", "color": "#555", "margin": "20px 0"}),
            html.Div(id="index-display", style={"fontWeight": "bold"})
        ],
        style={"display": "flex", "flexDirection": "column", "rowGap": "4px", "margin": "10px 0"}
    ),

    html.Div([
        dcc.Input(
            id="interval-input",
            type="number",
            value=refresh_interval,
            min=5,
            disabled=SERVER_VARIANT,
            step=1,
            style={"width": "60px", "fontSize": "18px", "fontWeight": "bold", "textAlign": "center"}
        ),
        html.Button("Abruf Intervall (Sek)", id="set-interval-btn", style={"marginLeft": "7px", "fontSize": "18px"}),
        html.Button("Reset", id="reset-btn", disabled=SERVER_VARIANT, style={"marginLeft": "7px", "fontSize": "18px"})
    ], style={"margin": "15px 0"}),

    html.Div([
        dcc.Checklist(
            id="sound-toggle",
            options=[{"label": "🔔", "value": "on"}],
            value=["on"],  
            inline=True,
            persistence=False,
            persistence_type="local",
            style={
                "display": "inline-block", 
                "marginRight": "10px",
                "transform": "scale(1.5)"  # Gleiche Größe wie Volatilitäts-Checkbox
            }
        ),
        html.Label(
            "Sound an/aus", 
            style={
                "display": "inline-block",
                "fontSize": "16px",  # Gleiche Textgröße
                "fontWeight": "bold"  # Gleicher Textstil
            }
        )
   ], style={
       "marginTop": "10px", 
       "textAlign": "left",
        "display": "flex", 
        "alignItems": "center",
        "padding": "10px",  # Gleicher Abstand
      # "backgroundColor": "#f0f0f0",  # Gleiche Hintergrundfarbe
        "borderRadius": "5px",
        "marginLeft": "5px"   # Gleiche abgerundete Ecken
    }),
# Ersetzen Sie diesen Abschnitt:


# Durch diesen Abschnitt:
html.Div([
    dcc.Checklist(
        id='volatility-toggle',
        options=[{'label': '', 'value': 'on'}],
        value=[],
        inline=True,
        style={'display': 'inline-block','marginRight': '10px','transform': 'scale(1.5)'},
    ),
    html.Label(
        id="vola-label",  # <— ID hinzufügen
        children="Volatilität einblenden",
        style={'display': 'inline-block','fontSize': '16px','fontWeight': 'bold','color':'black'}
    )
], style={'marginBottom': '15px','display':'flex','alignItems':'center',
          "padding": "10px","marginTop": "10px"}),  # doppelte marginTop entfernt


html.Div([
    dcc.Checklist(
        id='futures-toggle',
        options=[{'label': '', 'value': 'on'}],
        value=[],
        inline=True,
        style={'display': 'inline-block','marginRight':'10px','transform':'scale(1.5)'},
    ),
    html.Label(
        id='futures-label',       # ← neu
        children='Futures (FDAX) einblenden',
        style={'display':'inline-block','fontSize':'16px','fontWeight':'bold','color':'black'}
    )
], style={'marginBottom':'15px','display':'flex','alignItems':'center',
          'padding':'5px','marginLeft':'5px'}),



    html.Div([
        html.Div([
            html.Label("Dein Basis-Hebel", style={"fontSize": "18px", "fontWeight": "600", "marginRight": "8px"}),
            dcc.Input(
                id="base-leverage-input",
                type="number",
                value=BASE_LEVERAGE_DEFAULT,
                min=LEVER_MIN,
                max=LEVER_MAX,
                step=0.5,
                persistence=True,
                persistence_type="local",
                style={
                    "width": "60px",   # hier die Breite
                    "height": "36px",
                    "fontSize": "18px",
                    "padding": "4px 10px",
                    "textAlign": "right",
                    "fontWeight": "600",
                    "border": "1px solid #888",
                    "borderRadius": "6px"
                }
            )
        ], style={"display": "flex", "alignItems": "center", "gap": "8px"}),
#Balkengrafik, Ampel 5
        html.Div(
            id="vola-strip",
            style={
                "position": "absolute",
                "left": "50%",
                "transform": "translateX(-50%)",
                "display": "flex",
                "flexDirection": "row",
                "alignItems": "center",
                "justifyContent": "center",
                "gap": "4px",
                "height": "40px", # Höhe
                "margin": "0"
            }
        )
    ], style={
        "position": "relative",
        "height": "80px", # Höhe
        "paddingBottom": "6px",
        "marginTop": "10px",
        "marginBottom": "20px",
        "width": "100%"
    }),

    html.Div(id="vola-metrics", style={"textAlign": "center", "fontSize": "12px", "color": "#666", "marginBottom": "5px"}),
    html.Div(id="vola-leverage", style={"textAlign": "center", "fontSize": "14px", "fontWeight": "bold", "color": "#0066cc"}),

    html.Div(
        id="vola-description", # Text Ampel5 Besschriftung
        style={
        "textAlign": "left", 
        "fontSize": "120%", 
        "color": "black", 
        "marginTop": "0px", 
        "fontStyle": "standard",
        #"backgroundColor": "#f0f0f0",
        "paddingLeft": "300px", 
        "borderRadius": "6px",
        "maxWidth": "800px",
        "margin": "0 auto"
        }
    ),


    # NEU: Ampel 6 Platzhalter


    # danach wie gehabt:


    dcc.Graph(
        id="leverage-graph",
        config={
            "displaylogo": False,
            "modeBarButtonsToRemove": ["zoomIn2d", "zoomOut2d"],
            "displayModeBar": True
        },
        style={"height": GRAPH_HEIGHT}
    ),

# Platzhalter für News unter der Grafik – wird im Callback gefüllt
    html.Div(id="news-block-server"),

#########Neuen Auto-Reset-Timer ins Layout einbauen##########

    dcc.Interval(
        id="interval-component",
        interval=refresh_interval * 1000,
        n_intervals=0
    ),
    dcc.Interval(
        id="atr-interval",
        interval=300000,
        n_intervals=0
    ),
    # Auto-Reset: alle 60 Minuten nur im Server-Modus aktiv
    dcc.Interval(
        id="auto-reset-interval",
        interval=60 * 60 * 1000,          # 60 Minuten in Millisekunden
        n_intervals=0,
        disabled=not SERVER_VARIANT       # im Desktop-Modus komplett inaktiv
    ),
##############Ende: Neuen Auto-Reset-Timer ins Layout einbauen################


html.Audio(id="alarm-audio", src="", autoPlay=True, controls=False, style={"display": "none"}),
html.Audio(id="gong-audio", src="", autoPlay=True, controls=False, style={"display": "none"}),



    # Bild zuletzt, klickbar (öffnet jurina.biz)
    html.A(
        html.Img(
            src=app.get_asset_url(get_seasonal_image()),
            style={
                "position": "absolute",
                "top": "30px",
                "right": "30px",
                "width": "auto",
                "height": "220px",
                "zIndex": "1",
                "cursor": "pointer",
                "display": "none" if SERVER_VARIANT else "block",
            },
            draggable="false",
        ),
        href="https://jurina.biz",
        target="_blank",
        rel="noopener"
    ),
])




@app.callback(
    Output("app_state", "data"),
    Input("btn-exit", "n_clicks"),  # oder Klick auf Logo
    prevent_initial_call=True
)


@app.callback(
    Output("main-interval", "disabled"),
    Input("app_state", "data"),
    prevent_initial_call=True
)
def stop_intervals(state):
    return bool(state and state.get("shutdown"))


# ---- Sound-Status Callback (einzig) ----
@app.callback(
    Output("sound-toggle", "options"),
    Input("sound-toggle", "value"),
)
def on_sound_toggle(value):
    on = bool(value) and ("on" in value)
    set_sound_enabled(on)
    # zeigt Glocke an/aus im Kästchen
    return [{"label": "🔔" if on else "🔕", "value": "on"}]


     
# === Hebel aus gemeinsamer Ampel-5-Basis (r_eff) =============================
def _recommend_leverage_eff(r_eff: float, base_leverage: float | None) -> float | None:
    """
    Korrigierte Hebelempfehlung die die ursprüngliche Logik beibehält:
    - Bei niedriger Vola (r_eff < 1) → höherer Hebel
    - Bei hoher Vola (r_eff > 1) → niedrigerer Hebel
    """
    try:
        # Eingabevalidierung
        if (r_eff is None or not math.isfinite(r_eff) or r_eff <= 0):
            return None
            
        if base_leverage is None:
            base_leverage = BASE_LEVERAGE_DEFAULT
            
        base = max(LEVER_MIN, min(float(base_leverage), LEVER_MAX))
        
        # URSPRÜNGLICHE LOGIK BEIBEHALTEN: base / r_eff
        raw = base / float(r_eff)
        
        # Nur extrem unplausible Werte filtern (nicht die Business-Logik ändern)
        if raw > LEVER_MAX * 2:  # Nur extrem hohe Werte begrenzen
            print(f"⚠️ Extrem hoher Hebel korrigiert: {raw} -> {LEVER_MAX}")
            raw = LEVER_MAX
        elif raw < LEVER_MIN * 0.5:  # Nur extrem niedrige Werte begrenzen
            raw = LEVER_MIN
            
        clipped = float(np.clip(raw, LEVER_MIN, LEVER_MAX))
        
        # Auf 0.5-Schritte runden
                # --- dynamische Rundung je nach Hebelbereich ---
        if clipped < 10:
            result = round(clipped * 20) / 20   # 0.05-Schritte unter 10x
        elif clipped < 20:
            result = round(clipped * 10) / 10   # 0.1-Schritte zwischen 10x und 20x
        else:
            result = round(clipped * 2) / 2     # 0.5-Schritte ab 20x
        
        return result
        
    except Exception as e:
        print(f"⚠️ Fehler in _recommend_leverage_eff: {e}")
        return None

# --- Parameter für Momentum-Einfluss auf die effektive Vola (fein justierbar) ---
MOM_ALPHA = 0.60
MOM_BETA  = 0.30

def _recommend_leverage(x, m, base_leverage=None, underlying=None):
    if not x or not m or x <= 0 or m <= 0:
        return None
    if base_leverage is None:
        base_leverage = BASE_LEVERAGE_DEFAULT
    base_leverage = max(BASE_LEVERAGE_MIN, float(base_leverage))

    r = float(x) / float(m)
    raw = base_leverage * (1.0 / r)   # <- exakt deine alte Berechnung

    # Momentum holen
    L = 0.0
    try:
        if not underlying:
            underlying = get_selected_underlying()
        if underlying:
            L = float(_get_live_movement_pct(underlying))
    except Exception:
        L = 0.0

    # nur als Korrekturfaktor draufmultiplizieren
    factor = (1.0 + MOM_ALPHA * max(0, L)) * (1.0 + MOM_BETA * min(0, L))
    raw *= factor

    # clamp und runden
    clipped = float(np.clip(raw, LEVER_MIN, LEVER_MAX))
    return round(clipped * 2.0) / 2.0

# === Ampel 5: 60/40 ATR & Momentum ===

def _amp5_metrics(u: str, base: float):
    """
    Ampel 5 mit korrigierter Kategorisierung
    """
    try:
        # 1) Basiswerte
        m = _get_baseline_m(u)          # 60T-Median ATR5%
        x = _get_current_x(u)           # Aktueller ATR5%
        L_pct = _get_live_movement_pct(u) or 0.0
        
        print(f"🔍 ATR-DEBUG für {u}:")
        print(f"   Baseline ATR (m): {m}")
        print(f"   Current ATR (x): {x}")
        print(f"   Momentum (L_pct): {L_pct}")
        
        if not m or not x or m <= 0 or x <= 0:
            print(f"   ⚠️ Ungültige ATR-Werte: m={m}, x={x}")
            return None

        # KORREKTUR: Momentum begrenzen
        L_pct_clipped = float(np.clip(L_pct, -0.5, 1.0))  # Max +100%, Min -50%


        # 2) Cross-Index-Kalibrierung (±20%)
        avg_m = _mean_baseline_vola(exclude=None)
        if avg_m and avg_m > 0 and m > 0:
            calibration_ratio = avg_m / m
            
            # AUSREISSER FILTERN (Ratio > 3.0 oder < 0.33)
            if calibration_ratio > 3.0 or calibration_ratio < 0.33:
                print(f"🔍 AUSREISSER GEFUNDEN: calibration_ratio={calibration_ratio:.3f}")
                print(f"   → Verwende Standard-Basishebel (keine Kalibrierung)")
                base_star = float(base)
            else:
                # ±20% BEGRENZUNG
                max_adjustment = 1.2  # +20%
                min_adjustment = 0.8  # -20%
                
                limited_ratio = np.clip(calibration_ratio, min_adjustment, max_adjustment)
                base_star = base * limited_ratio
                base_star = float(np.clip(round(base_star * 2) / 2.0, LEVER_MIN, LEVER_MAX))
                
   
        else:
            base_star = float(base)
        

        # 3) Live-Momentum der Indexlinie (bereits geclippt)
        L_pct_clipped = float(np.clip(L_pct_clipped, -0.60, 1.60))
   

        # 4) KORREKTE KATEGORISIERUNG basierend auf Volatilität
        vola_ratio = x / m
        
        # KORREKTUR: Richtige Kategorisierung
        if vola_ratio < VOLA_THRESH["very_low"]:
            cat = "very_low"
            vola_level = 1
        elif vola_ratio < VOLA_THRESH["low"]:
            cat = "low" 
            vola_level = 2
        elif vola_ratio <= VOLA_THRESH["high"]:
            cat = "normal"
            vola_level = 3
        elif vola_ratio <= VOLA_THRESH["very_high"]:
            cat = "elevated"
            vola_level = 4
        else:
            cat = "very_high"
            vola_level = 5
        


        # 5) Momentum-Stufe berechnen
        def _momentum_to_level(mom_pct: float) -> int:
            mom_abs = abs(mom_pct)
            if mom_abs < 0.1:   return 3  # Neutral
            elif mom_abs < 0.3: return 2  # Leicht
            elif mom_abs < 0.5: return 4  # Mittel
            else:               return 5  # Stark
        
        L_lvl = _momentum_to_level(L_pct_clipped)
        print(f"   Momentum-Stufe (L_lvl): {L_lvl}")

        # 6) Kombinierte Stufe (40% Vola + 60% Momentum)
        combined_level = int(np.clip(round(0.4 * vola_level + 0.6 * L_lvl), 1, 5))
        final_cat = {1:"very_low", 2:"low", 3:"normal", 4:"elevated", 5:"very_high"}[combined_level]
        
      

        # 7) Effektive Ratio für Hebelberechnung (40% ATR + 60% Momentum)
        momentum_component = 1.0 + (L_pct_clipped * 0.7)  # Nur 70% des Momentums
        r_eff = 0.40 * (x / m) + 0.60 * momentum_component
    

        return {
            "m": float(m), "x": float(x), "L_pct": float(L_pct_clipped),
            "vola_ratio": float(vola_ratio), "vola_level": vola_level, "L_lvl": L_lvl,
            "lvl": combined_level, "cat": final_cat, "base_star": base_star, "r_eff": float(r_eff)
        }
        
    except Exception as e:
        print(f"⚠️ Fehler in _amp5_metrics für {u}: {e}")
        import traceback
        traceback.print_exc()
        return None
        
# Callback: Hebel via r_eff und Feld-Clamp (Normal = ±10 % vom Basishebel)
@app.callback(
    [Output("vola-strip", "children"),
     Output("vola-metrics", "children"),
     Output("vola-leverage", "children"),
     Output("vola-description", "children")],
    [Input("atr-interval", "n_intervals"),
     Input("underlying-dropdown", "value"),
     Input("base-leverage-input", "value")]
)
def update_vola_strip(_n, u, base_leverage):
    base = float(base_leverage if base_leverage is not None else BASE_LEVERAGE_DEFAULT)
    met = _amp5_metrics(u, base)
    
    if not met:
        return build_vola_strip("off", base, None), "", "", VOLA_DESCRIPTIONS["off"]

    cat = met["cat"]
    base_star = met["base_star"]
    r_eff = met["r_eff"]

    # Hebelempfehlung nach ursprünglicher Formel
    L_raw = _recommend_leverage_eff(r_eff, base_star)
    L_rec = _clamp_leverage_to_field(base_star, cat, L_raw)

    # Detaillierte Debug-Information
    debug_info = [
        f"Basishebel: {base} → {base_star:.2f}",
        f"ATR-Relativ: {met['x']/met['m']:.3f}",
        f"Momentum: {met['L_pct']:+.3f}",
        f"r_eff: {r_eff:.3f}",
       # f"Empfohlen: {L_raw:.2f} → {L_rec:.2f}"
    ]
    
    print(f"🎯 {u}: {', '.join(debug_info)}")

    strip = build_vola_strip(cat, base_star, L_rec)
    metrics_text = " | ".join(debug_info)
    desc = VOLA_DESCRIPTIONS.get(cat, VOLA_DESCRIPTIONS["off"])
    
    return strip, metrics_text, "", desc




#hebel 50/50 ATR/Index+vola
# ==== Color helpers (einfügen nach FARBCODES) ====
HEX2NAME = {
    "#90EE90": "green",   # LightGreen
    "#FFA500": "orange",  # Orange
    "#ff0000": "red",     # Rot (klein)
    "#FF0000": "red",     # Rot (groß)
    "#808080": "gray",    # Grau
    "#FFFF00": "orange"   # optional Gelb
}

def _hex_to_name(c: str) -> str:
    """Nimmt Hex oder Namen und gibt konsistent den Farbnamen zurück."""
    if not c:
        return "gray"
    c = str(c).strip()
    # Wenn bereits Farbname
    if c in ("green","orange","red","gray","orange"):
        return c
    # Wenn Hex
    return HEX2NAME.get(c, "gray")

def _combine_colors(a: str, b: str) -> str:
    """Kombiniert zwei Ampelfarben nach Priorität: red > orange > green > gray."""
    a = _hex_to_name(a); b = _hex_to_name(b)
    prio = {"red": 3, "orange": 2, "green": 1, "gray": 0, "orange": 1}
    # Höhere Priorität gewinnt
    return a if prio.get(a,0) >= prio.get(b,0) else b


#####ENDE für Vola + Hebelempfehlung++++++++++++++



# ---- Haupt-Callback inkl. Sound-Wert ----
@app.callback(
    Output('leverage-graph', 'figure'),
    Output('last-fetch-time', 'children'),
    Output('index-display', 'children'),
    Output('alarm-audio', 'src'),
    Output('gong-audio', 'src'),  # NEU: Gong-Audio Output
    Output("news-block-server", "children"),   # NEU
    Input('interval-component', 'n_intervals'),
    Input('underlying-dropdown', 'value'),
    Input('volatility-toggle', 'value'),
    Input('futures-toggle','value'),
    Input('sound-toggle', 'value'),
)
def update_graph(n, selected, volatility_toggle, futures_toggle, sound_value):
    global selected_underlying, last_fetch_time, show_volatility, _last_alarm_state
    #selected = get_selected_underlying()
    # --- NEU: Ampel 4 Descriptor dynamisch setzen ---
    ampel4_descriptor_div = html.Div(
        _ampel4_descriptor_for(selected),
        style={"fontSize": "14px", "marginTop": "4px", "color": "#444"}
    )


    # Underlying-Wechsel -> Reset
    if selected != selected_underlying:
        switch_underlying(selected)
     

    # Sound
    sound_on = bool(sound_value) and ("on" in sound_value)
    set_sound_enabled(sound_on)
    alarm_src = ""
    gong_src = "" 
    gong_src = get_gong_sound() 

    # Schalter
    show_volatility = ('on' in volatility_toggle) if isinstance(volatility_toggle, (list, tuple, set)) else False
    show_futures = ('on' in futures_toggle) if isinstance(futures_toggle, (list, tuple, set)) else False

    # Index-Anzeige vorbereiten
    index_display_percentage = "N/A"
    index_display_color = "gray"
    index_change = None
    day_minmax_text = ""
    age_sec = None

    # Letzten Indexwert aus CSV für Anzeige
    csv_file_display = get_csv_filename(selected)
    if os.path.exists(csv_file_display):
        try:
            df_tmp = pd.read_csv(csv_file_display, encoding='utf-8')
            try:
                ts = pd.to_datetime(df_tmp['timestamp'].iloc[-1])
                age = (pd.Timestamp.now(tz=TZ_BERLIN) - ts).total_seconds()
                age_sec = age  # für Farbe rot bei Abrufintervall
                if age > max(15, 3*refresh_interval):
                    start_update_thread()
            except Exception:
                pass
            if not df_tmp.empty and 'index_change' in df_tmp.columns:
                index_change = float(df_tmp['index_change'].iloc[-1])
                index_display_percentage = f"{index_change:.2f}%"
                index_display_color = "red" if index_change < 0 else ("green" if index_change > 0 else "gray")
        except Exception as _e:
            pass


    # Tages-Min/Max aus Yahoo (robust, wie get_index_data)
    index_prev_close = None
    day_minmax_text = ""
    try:
        import yfinance as yf
        _ticker_map = {
            "Dax": "^GDAXI",
            "S&P 500": "^GSPC",
            "EURO STOXX 50": "^STOXX50E",
            "Dow Jones": "^DJI",
            "Nasdaq 100": "^NDX",
            "Nasdaq": "^NDX",
        }
        _sym = _ticker_map.get(selected)
        if _sym:
            t = yf.Ticker(_sym)

            # 1) PrevClose bevorzugt fast_info → Fallback Tagesdaten
            try:
                fi = getattr(t, "fast_info", None)
                if fi is not None:
                    pc = fi.previous_close
                    if pc and float(pc) > 0:
                        index_prev_close = float(pc)
            except Exception:
                index_prev_close = None

            if not index_prev_close or index_prev_close <= 0:
                d = yf.download(
                    _sym,
                    period="5d",
                    interval="1d",
                    auto_adjust=False,
                    progress=False,
                    threads=False,
                )
                if d is not None and not d.empty and "Close" in d:
                    cc = d["Close"].dropna()
                    if len(cc) >= 2:
                        index_prev_close = float(cc.iloc[-2])

            # 2) Intraday-Min/Max aus 1m inkl. Pre/Post
            if index_prev_close and index_prev_close > 0:
                intra = yf.download(
                    _sym,
                    period="1d",
                    interval="1m",
                    auto_adjust=False,
                    progress=False,
                    threads=False,
                    prepost=True,
                )
                if intra is not None and not intra.empty:
                    hi = float(intra["High"].max())
                    lo = float(intra["Low"].min())
                    max_pct = (hi - index_prev_close) / index_prev_close * 100.0
                    min_pct = (lo - index_prev_close) / index_prev_close * 100.0
                    day_minmax_text = f"Min: {min_pct:.2f}% · Max: {max_pct:.2f}%"
    except Exception as e:
        print("Min/Max-Berechnung fehlgeschlagen:", e)


    # Haupt-CSV laden
    csv_file = get_csv_filename(selected_underlying)
    lock = FILE_LOCKS[csv_file]
    with lock:
        if os.path.exists(csv_file):
            try:
                df = pd.read_csv(csv_file, parse_dates=['timestamp'], encoding='utf-8')
            except Exception:
                df = pd.DataFrame(columns=["timestamp","long_avg","short_avg","index_change","volatility_change","futures_avg"])
        else:
            df = pd.DataFrame(columns=["timestamp","long_avg","short_avg","index_change","volatility_change","futures_avg"])

    # Grundsäuberung
    try:
        if not df.empty:
            for col in ['long_avg','short_avg','index_change']:
                if col not in df.columns:
                    df[col] = np.nan
            if 'volatility_change' in df.columns:
                df['volatility_change'] = df['volatility_change'].ffill().bfill()
            if 'futures_avg' in df.columns:
                df['futures_avg'] = df['futures_avg'].ffill().bfill()
            df = df.ffill()
        else:
            # leere Startdatei sicherstellen
            empty = pd.DataFrame(columns=["timestamp","long_avg","short_avg","index_change","volatility_change","futures_avg"])
            atomic_write_csv(empty, csv_file)
    except Exception as e:
        print(f"Fehler beim Aufbereiten der CSV: {e}")
        df = pd.DataFrame(columns=["timestamp","long_avg","short_avg","index_change","volatility_change","futures_avg"])

    # Plot
    fig = go.Figure()
    if not df.empty and len(df) > 1:
        # Hebel-Serien
        fig.add_trace(go.Scatter(
            x=df['timestamp'], y=df['long_avg'],
            mode='lines+markers', name='Long Hebel',
            line=dict(color='LightGreen', width=2),
            marker=dict(size=5), opacity=0.8
        ))
        fig.add_trace(go.Scatter(
            x=df['timestamp'], y=df['short_avg'],
            mode='lines+markers', name='Short Hebel',
            line=dict(color='red', width=2),
            marker=dict(size=5), opacity=0.8,
            connectgaps=True
       ))

        # Index
        fig.add_trace(go.Scatter(
            x=df['timestamp'], y=df['index_change'],
            mode='lines', name=f"Index: {selected}",   
            line=dict(color='cyan', width=4),
            yaxis='y2',
            hovertemplate="%{x|%H:%M:%S}<br>%{y:.2f}%<extra></extra>"
        ))
        # Vola
        if show_volatility and 'volatility_change' in df.columns and df['volatility_change'].notna().any():
            fig.add_trace(go.Scatter(
                x=df['timestamp'], y=df['volatility_change'],
                mode='lines',
                name=get_vol_label(selected),
                line=dict(color='rgb(255,128,255)', width=3),   # <- hier Farbe = blau
                yaxis='y2',
                hovertemplate="%{x|%H:%M:%S}<br>%{y:.2f}%<extra></extra>"
            ))

        # Top-10
# Top-10
        if show_futures and 'futures_avg' in df.columns:
            f = pd.to_numeric(df['futures_avg'], errors='coerce').ffill()

            idx = None
            if 'index_change' in df.columns:
                idx = pd.to_numeric(df['index_change'], errors='coerce').ffill()
    
    # Nur anzeigen, wenn gültige Daten vorhanden sind
            if idx is not None and f.notna().any() and idx.notna().any():
        # Mindestens 2 gültige Werte für sinnvolle Darstellung
                valid_futures = f.dropna()
                if len(valid_futures) >= 2:
                    fut_val = float(f.iloc[-1])
                    idx_val = float(idx.iloc[-1])

            # Formel: (F / I) - 1
                    delta = fut_val - idx_val

                    name_txt = f"Index Futures {fut_val:.2f}% ({delta:+.2f} pp vs Index)"

                    fig.add_trace(go.Scatter(
                        x=df['timestamp'],
                        y=f.interpolate(),
                        mode='lines',
                        name=name_txt,
                        line=dict(color='#FF5F1F', width=2),
                        yaxis='y2',
                        hovertemplate="%{x|%H:%M:%S}<br>%{y:.2f}%<extra></extra>",
                        connectgaps=True
                    ))


        # Y2 Range
        y2_series = df['index_change']
        if show_volatility and 'volatility_change' in df.columns:
            y2_series = pd.concat([y2_series, df['volatility_change']], axis=0)
        if show_futures and 'futures_avg' in df.columns:
            y2_series = pd.concat([y2_series, df['futures_avg']], axis=0)
        min_val = float(_to_scalar(y2_series.min()))
        max_val = float(_to_scalar(y2_series.max()))
        span = max_val - min_val
        min_range = 1.0
        padding = 0.1
        if span < min_range:
            center = (min_val + max_val) / 2.0
            y2_range = [center - min_range/2 - padding, center + min_range/2 + padding]
        else:
            y2_range = [min_val - padding, max_val + padding]
            
        fig.update_layout(
            uirevision="keep",                   # behält User-Zoom/Pan
            xaxis=dict(
                rangeslider=dict(visible=False),
                rangeselector=dict(buttons=[
                    dict(count=15, label="15m", step="minute", stepmode="backward"),
                    dict(count=30, label="30m", step="minute", stepmode="backward"),
                    dict(count=45, label="45m", step="minute", stepmode="backward"),
                    dict(count=60, label="60m", step="minute", stepmode="backward"),
                    dict(count=90, label="90m", step="minute", stepmode="backward"),
                    dict(step="all", label="All")
                ])
           ),
           yaxis=dict(autorange=True)
        )

        fig.update_layout(
            title={
                'text': f"Leverage Lens – {selected_underlying} : {index_display_percentage} ",
                'y': 0.95, 'x': 0.5, 'xanchor': 'center', 'yanchor': 'top',
                'font': {'size': 18, 'weight': 'bold', "color": "blue"}
            },
            xaxis=dict(
                title=dict(text='Zeit', font=dict(color='black', size=18)),
                tickfont=dict(color='black', size=14),
                gridcolor="gray",  
                zeroline=True,
                zerolinecolor="lightgray",
               # zerolinewidth=0.5,  
                linecolor='black',
                showline=True
            ),
            yaxis=dict(
                title=dict(text='Durchschnittlicher Hebel', font=dict(color='black', size=16)),
                side='left',
                showgrid=True,
                gridcolor="gray",  
                zeroline=True,
                zerolinecolor="lightgray",
                tickfont=dict(color='black', size=14),
                linecolor='black',
                showline=True
            ),
            yaxis2=dict(
                title=dict(text="Index / Vola / Top-10 (%)", font=dict(color='blue', size=16)),
                overlaying='y',
                side='right',
                showgrid=False,
                zeroline=True,
                zerolinecolor="lightgray",
               # zerolinewidth=0.5,  
                range=y2_range,
                tickfont=dict(color='blue', size=14),
                linecolor='black',
                showline=True
            ),
            legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="right", x=1, font=dict(size=16)  ),
            margin=dict(l=50, r=50, b=50, t=80, pad=4),
            height=500,
            plot_bgcolor='rgba(47,47,47,0.8)'
        )
    else:
        fig.update_layout(
            title="Keine Daten verfügbar",
            plot_bgcolor='rgba(47,47,47,0.8)'
        )
        now = datetime.now(TZ_BERLIN)
        placeholder_text = "Warte auf ausreichende Daten..." if (not df.empty and len(df) == 1) else "Warte auf erste Daten..."
        fig.add_annotation(text=placeholder_text, xref="paper", yref="paper",
                           x=0.5, y=0.5, showarrow=False, font=dict(size=12, color="gray"))
        fig.add_trace(go.Scatter(x=[now - timedelta(minutes=5), now], y=[0, 50],
                                 mode='lines', line=dict(width=0), showlegend=False, hoverinfo='none'))

    # Anzeige-String für Kopf
    index_display_text = f"{index_display_percentage} {day_minmax_text}"

    # Ampel 1 / Ampel 2 werden hiernach berechnet …
    # Ampel 3

    alle_ereignisse = lade_oder_erstelle_ereignisse()
    ampel3_color, ampel3_text = bewerte_ampel_3(alle_ereignisse, selected_underlying)
    if str(ampel3_color).strip().lower() in ("yellow", "#ffff00"):
        ampel3_color = FARBCODES["orange"]


    # Signale
    # --- SOFR-Defaults sofort setzen, damit HTML-Build nie crasht ---
    sofr_text = "SOFR-Proxy: keine Daten."
    sofr_mini_color = FARBCODES["gray"]
    sofr_mini_emoji = "⚪"

    try:
        rel_pos, ampel3_signal, hebel_signal, datenpunkt_info, _, tagesverlauf = determine_ampel_signal(df)

        ampel1_color, _amp1_relpos, ampel1_text_local = get_ampel1_status(df, selected_underlying)

#neutrale Initialisierung ersetzen. Ampel 2
        ampel2_color = FARBCODES["gray"]
            
# --- SOFR-Proxy-Werte holen -      
        #     
# robuste Defaults VOR dem try
        sofr_bps = 0
        sofr_text = "SOFR-Proxy: keine Daten."
        sofr_mini_color = FARBCODES["gray"]
        sofr_mini_emoji = "⚪"

        try:
    # ... determine_ampel_signal etc. ...
    # SOFR aus Cache holen
 #####
            try:
                sofr_bps, sofr_text = get_sofr_proxy_comment()
            except (TypeError, ValueError):
                sofr_bps = 0
                sofr_text = "SOFR-Proxy: keine Daten."
 
                
    # Miniampel/Farbe
            if abs(sofr_bps) >= RSI_OVERBOUGHT:
                sofr_mini_color = FARBCODES["red"];   sofr_mini_emoji = "🔴"
            elif abs(sofr_bps) >= 40:
                sofr_mini_color = FARBCODES["orange"];sofr_mini_emoji = "🟠"
            else:
                sofr_mini_color = FARBCODES["green"]; sofr_mini_emoji = "🟢"
                
           # === Ampel 2 final: schlechteste Miniampel zählt ===
    

            hebel_mini_color = (
                FARBCODES["red"]    if "🔴" in hebel_signal else
                FARBCODES["orange"] if ("🟠" in hebel_signal or "🟠" in hebel_signal) else
               FARBCODES["green"]  if ("🟢" in hebel_signal or "Positiv:" in hebel_signal) else
                FARBCODES["gray"]
            )

            if FARBCODES["red"] in (hebel_mini_color, sofr_mini_color):
                ampel2_color = FARBCODES["red"]
            elif FARBCODES["orange"] in (hebel_mini_color, sofr_mini_color):
                ampel2_color = FARBCODES["orange"]
            elif hebel_mini_color == FARBCODES["gray"] and sofr_mini_color == FARBCODES["gray"]:
                ampel2_color = FARBCODES["gray"]
            else:
                ampel2_color = FARBCODES["green"]


        except Exception as e:
            print(f"Fehler bei Signalberechnung: {e}")
            # sichere Defaults, damit das Layout nie crasht
            ampel3_signal = "System initialisiert"
            hebel_signal  = "Warte auf Daten"
            datenpunkt_info = "Initialisierung läuft"
            tagesverlauf = "-"
            ampel3_color = FARBCODES["gray"]
            ampel1_color = FARBCODES["gray"]
            ampel2_color = FARBCODES["gray"]
            ampel1_text_local = ampel1_text
            # SOFR-Defaults unbedingt auch hier:
            sofr_bps = 0
            sofr_text = "SOFR-Proxy: keine Daten."
            sofr_mini_color = FARBCODES["gray"]
            sofr_mini_emoji = "⚪"
            # SOFR-Defaults auch im Fehlerfall
            sofr_bps = 0
            sofr_text = "SOFR-Proxy: keine Daten."
            sofr_mini_color = FARBCODES["gray"]
            sofr_mini_emoji = "⚪"


            
        else:
    # Your existing SOFR processing logic
           if abs(sofr_bps) > 100:
               sofr_text = "Extrem (Systemkrise): >100 bps – Historisch nur in Krisen (2007–2008 bis 465 bps, Corona 2020 ca. 140 bps). Signal: akute Banken-/Fundingkrise"
               sofr_mini_color = FARBCODES["red"]
               sofr_mini_emoji = "🔴"
           elif abs(sofr_bps) >= RSI_OVERBOUGHT:
               sofr_text = "Kritisch (Liquiditätsstress): >100 Banken leihen zögerlich. Meist Vorbote stärkerer Abverkäufe."
               sofr_mini_color = FARBCODES["red"]
               sofr_mini_emoji = "🔴"
           elif abs(sofr_bps) >= 40:
               sofr_text = "Erhöht (Markt wird nervös): >40 Leichte Spannungen im Interbankmarkt. Frühwarnsignal für knapper werdende Liquidität."
               sofr_mini_color = FARBCODES["orange"]
               sofr_mini_emoji = "🟠"
           elif abs(sofr_bps) >= 10:
               sofr_text = "Normalbereich (kein Stress): 10–40 bps – Typisch in ruhigen Marktphasen."
               sofr_mini_color = FARBCODES["green"]
               sofr_mini_emoji = "🟢"
           else:
               sofr_text = "Unter Normalbereich (<10 bps) – sehr ruhige Interbank-Lage"
               sofr_mini_color = FARBCODES["green"]
               sofr_mini_emoji = "🟢"
         
            
                       
            #
# Miniampel/Farbe bestimmen
        if abs(sofr_bps) >= RSI_OVERBOUGHT:
            sofr_mini_color = FARBCODES["red"]
            sofr_mini_emoji = "🔴"
        elif abs(sofr_bps) >= 40:
            sofr_mini_color = FARBCODES["orange"]
            sofr_mini_emoji = "🟠"
        else:
            sofr_mini_color = FARBCODES["green"]
            sofr_mini_emoji = "🟢"
# Ampel 2 hart überschreiben, wenn Stress hoch        
        if abs(sofr_bps) >= RSI_OVERBOUGHT:
            ampel2_color = FARBCODES["red"]
        elif abs(sofr_bps) >= 40 and ampel2_color != FARBCODES["red"]:
            ampel2_color = FARBCODES["orange"]
              
    # nur gelb markieren, falls nicht bereits rot aus anderer Logik
      


        # Browser-Alarm nur bei Zustandswechsel und nur wenn sound_on

        amp1_rot = (ampel1_color == FARBCODES["red"])
        # Ampel-Status (rot = True)
        amp1_rot = (ampel1_color == FARBCODES["red"])
        amp2_rot = (ampel2_color == FARBCODES["red"])
        amp5_rot = bool(_AMP5_RED_FLAG)

        u = selected or selected_underlying  # aktuelles Underlying

        # Latch zurücksetzen, sobald Ampel 1 grün ist
        if _hex_to_name(ampel1_color) == "green":
            _A1_RED_LATCH[u] = False

        # Erstes Rot seit "grün" erlaubt Alarm
        first_a1_red = False
        if amp1_rot and not _A1_RED_LATCH.get(u, False):
            first_a1_red = True
            _A1_RED_LATCH[u] = True

        # Ampel 3 aktuell nicht genutzt für Alarm
        amp3_rot = False

        # Ampel 4: rot, wenn ampel4_color rot ist
        amp4_rot = ('ampel4_color' in locals()) and (ampel4_color == FARBCODES["red"])

        # Vorheriger Zustand (Ampel 1, 2, 4, 5)
        prev_state = _last_alarm_state or (False, False, False, False)
        current_state = (amp1_rot, amp2_rot, amp4_rot, amp5_rot)

        # Orange→Rot-Re-Trigger blocken, solange seit "grün" schon einmal Rot gemeldet wurde
        ignore_amp1_retrigger = (not prev_state[0]) and amp1_rot and (not first_a1_red)

        if current_state != prev_state and not ignore_amp1_retrigger:
            ts = f"{time.time():.3f}"
            if sound_on:
                alarm_src = None
                if any([amp1_rot, amp2_rot, amp3_rot, amp4_rot]):
                    alarm_src = f'{app.get_asset_url("Alarm1.wav")}?ts={ts}'
                if amp5_rot:
                    alarm_src = f'{app.get_asset_url("Alarm2.wav")}?ts={ts}'

        # Zustand immer aktualisieren
            _last_alarm_state = current_state

            ts = f"{time.time():.3f}"
            if sound_on:
                alarm_src = None
                if any([amp1_rot, amp2_rot, amp3_rot, amp4_rot]):
                    alarm_src = f'{app.get_asset_url("Alarm1.wav")}?ts={ts}'
                    # Ampel 5 → Alarm 2 (hat Vorrang)
                if amp5_rot:
                    alarm_src = f'{app.get_asset_url("Alarm2.wav")}?ts={ts}'

# Zustand immer aktualisieren
        _last_alarm_state = current_state


    except Exception as e:
        print(f"Fehler bei Signalberechnung: {e}")
        ampel3_signal = "System initialisiert"; hebel_signal = "Warte auf Daten"; datenpunkt_info = "Initialisierung läuft"
        tagesverlauf = "-"; ampel3_color = FARBCODES["gray"]; ampel1_color = FARBCODES["gray"]; ampel2_color = FARBCODES["gray"]; ampel1_text_local = ampel1_text

    # RSI / Ampel 4 / USA
# --- Ampel 4: RSI + (für USA) Fear & Greed ---
    rsi_ticker = get_rsi_for_underlying(selected)
    rsi_value  = get_rsi(rsi_ticker) if rsi_ticker else None


    if selected in ("S&P 500", "Dow Jones", "Nasdaq", "Nasdaq 100"):
        fear = get_fng_today(force_refresh=True)
        color, line = bewerte_ampel4_usa(
            float(_to_scalar(rsi_value)) if rsi_value is not None else float("nan"),
            float(_to_scalar(fear)) if fear is not None else float("nan")
        )

        # US-Net-Liquidity als zusätzlicher Indikator
        _, nl_cat, nl_emoji, nl_text = get_us_net_liquidity()

        # „Schlechtester“ Indikator bestimmt die Hauptampel:
        # color (RSI+Fear) vs. nl_cat (US-Net-Liquidity)
        order = {"red": 3, "orange": 2, "green": 1, "gray": 0}
        base_cat = color if color in order else "gray"
        worst_cat = base_cat
        if order.get(nl_cat, 0) > order.get(worst_cat, 0):
            worst_cat = nl_cat

        ampel4_color = FARBCODES.get(worst_cat, FARBCODES["gray"])
        ampel4_title = "Ampel 4: Marktstimmung"

# Anzeige-Reihenfolge der Miniampeln:
# 1) US-Net-Liquidity (Makro, langsam aber dominierend)
# 2) RSI (taktisch, schnell)
# 3) Fear & Greed (Sentiment)
        ampel4_text  = f"{nl_emoji} {nl_text}"
        ampel4_text += "<br>" + line  # line enthält RSI- und Fear-Miniampel



        # DAX/EURO STOXX: RSI + USA-Breite (zweite Miniampel)
    else:
        # DAX/EURO STOXX: RSI + USA-Breite + US-Net-Liquidity (dritte Miniampel)
        rsi_status, rsi_title, rsi_text = bewerte_rsi_ampel(rsi_value)  # liefert Hex-Farbe + Text

        # RSI-Miniampel-Emoji + Kategorie
        if rsi_value is None:
            rsi_emoji, rsi_cat = "⚪", "gray"
        elif rsi_value >= RSI_OVERBOUGHT:
            rsi_emoji, rsi_cat = "🔴", "red"
        elif rsi_value >= RSI_WARN:
            rsi_emoji, rsi_cat = "🟠", "orange"
        else:
            rsi_emoji, rsi_cat = "🟢", "green"

        # USA-Breite (zweite Miniampel)
        usa_emoji, usa_cat, usa_text = miniampel_usa_breadth()

        # US-Net-Liquidity (dritte Miniampel)
        _, nl_cat, nl_emoji, nl_text = get_us_net_liquidity()

        # Hauptampel nimmt den „schlechtesten“ Wert (rot > orange > grün > grau)
        order = {"red": 3, "orange": 2, "green": 1, "gray": 0}
        worst_cat = rsi_cat
        if order.get(usa_cat, 0) > order.get(worst_cat, 0):
            worst_cat = usa_cat
        if order.get(nl_cat, 0) > order.get(worst_cat, 0):
            worst_cat = nl_cat

        ampel4_color = FARBCODES.get(worst_cat, FARBCODES["gray"])

        ampel4_title = "Ampel 4: Marktstimmung"
        # drei Zeilen Kommentar
    # drei Zeilen Kommentar – sortiert nach „Einflussgeschwindigkeit“:
    # 1) US-Net-Liquidity (globaler Makro-Hintergrund)
    # 2) USA-Breite (intraday Rücken-/Gegenwind für DAX/ESTOXX)
    # 3) RSI (lokaler technischer Zustand)
        ampel4_text  = f"{nl_emoji} {nl_text}"
        ampel4_text += "<br>" + f"{usa_emoji} {usa_text}"
        ampel4_text += "<br>" + f"{rsi_emoji} {rsi_text}"
        
        
        ampel4_lines = ampel4_text.split("<br>")
        html.Div([
            html.Span("Kommentar: "),
            html.Span(ampel4_lines[0]),
            html.Br(),
    # zweite Zeile ~10 Zeichen einrücken
            html.Span(
                ampel4_lines[1] if len(ampel4_lines) > 1 else "",
                style={"display": "inline-block", "marginLeft": "10ch"}  # ← Einzug
            )
        ], style={"marginLeft":"40px","fontSize":"90%","color":"#333"})



    kommentar = hebel_signal
    num_pages = max(1, math.ceil(NEWS_TOTAL_ITEMS / NEWS_PAGE_SIZE))
    page_index = (n // NEWS_SWITCH_EVERY_N_INTERVALS) % num_pages if NEWS_SWITCH_EVERY_N_INTERVALS > 0 else 0
    news_or_info_block = get_news_block(page_index) if SHOW_NEWS_INSTEAD_OF_COMMENT else html.Div([
        html.Div(datenpunkt_info, style={"fontStyle": "normal","fontSize": "90%","color": "#333","backgroundColor": "#e0e0e0","padding": "4px 8px","borderRadius": "6px","display": "inline-block","marginBottom": "6px"}),
        html.Br(),
        html.Div(tagesverlauf, style={"fontStyle": "normal","fontSize": "90%","color": "#333","backgroundColor": "#e0e0e0","padding": "4px 8px","borderRadius": "6px","display": "inline-block","marginBottom": "20px"}),
    ], style={"marginBottom": "16px"})

        # Wohin mit dem Block?

    # Wohin mit dem Block? (oben oder unten)
    if SERVER_VARIANT:
        # Server/Handy: News unter der Grafik
        news_top = None
        news_bottom = news_or_info_block
    else:
        # Desktop: News bei "Index aktuell"
        news_top = news_or_info_block
        news_bottom = None


    # Farbe für "Letzte Abfrage": rot, wenn älter als Abrufintervall + 30s
    
   #age_sec = 9999 #Test FArbe rot, wenn kein Index Abruf
    try:
        thr = float(refresh_interval) + 30.0
    except Exception:
        thr = 30.0
    is_stale = (isinstance(age_sec, (int, float)) and age_sec > thr)
    _last_fetch_el = html.Span(
        f"Letzte Abfrage: {last_fetch_time}",
        style={"color": ("red" if is_stale else "black"), "fontSize": "16px", "fontWeight": "bold" if is_stale else "bold"}
    )
    if is_stale:
        fig.update_layout(
            xaxis=dict(
                tickfont=dict(color="red" if is_stale else "black")
            )
        )


    WINDOW_MIN = 40  # Ziel-Fenster



    if not df.empty and "timestamp" in df.columns:
        ts = pd.to_datetime(df["timestamp"])
        start, end = ts.iloc[0].to_pydatetime(), ts.iloc[-1].to_pydatetime()
        span = end - start

    # solange <30 Min → komplette Daten zeigen
        if span < timedelta(minutes=WINDOW_MIN):
            left = start
            right = end
            slider_visible = False
        else:
            left = end - timedelta(minutes=WINDOW_MIN)
            right = end
            slider_visible = False

        fig.update_layout(
            xaxis=dict(
                range=[left, right],
                rangeslider=dict(visible=slider_visible)
            ),
            yaxis=dict(autorange=True)
        )


    
    return (
        fig,

        # 2) last-fetch-time.children  -> "Letzte Abfrage …" + Börsenstatus in einer Zeile
        html.Div([
            _last_fetch_el,
            html.Span(
                is_market_open(selected),
                style={"fontSize": "18px", "color": "#444", "marginLeft": "12px"}
            ),
        ], style={"display": "flex", "alignItems": "center"}),

        # 3) index-display.children  -> Index-Zeile mit Min/Max + ATR-Hinweis, plus restlicher Content
        html.Div([
            html.Div([
                html.Span(
                    f"Index aktuell: {index_display_percentage}",
                    style={"color": index_display_color, "fontWeight": "bold", "fontSize": "25px", "marginRight": "12px"}
                ), 
                html.Span(
                    day_minmax_text,
                    style={"color": "#000", "fontSize": "18px", "marginRight": "12px"}
                ),
                html.Span(
                     _p80_text(selected, index_change if index_change is not None else 0),
                    style={"fontSize": "25px", "marginRight": "18px"}
                ),
            ], style={"display": "flex", "alignItems": "center"}),

            html.Br(),
            news_top,  #wegen server variante, news unten




            html.Div([
                html.Div(style={"width": "35px","height": "35px","borderRadius": "50%","backgroundColor": ampel1_color,"display": "inline-block","marginRight": "15px","marginTop": "4px","boxShadow": "0 0 8px 2px rgba(255, 255, 255, 0.5)","border": "2px solid #666","boxSizing": "border-box"}),
                html.Div([
                    html.Div(get_ampel1_title(selected), style={"fontSize": "100%","fontWeight": "bold"}),
                    html.Div("Erkennt: Vola steigt häufig vor oder während fallender Kurse. Wenn plötzlich die Vola mehr steigt als der Index → Warnsignal:", style={"marginLeft": "20px","fontSize": "90%","color": "#333"}),
                    html.Div(f"Kommentar: {ampel1_text_local}", style={"marginLeft": "40px","fontSize": "90%","color": "#333"}),
                ])
            ], style={"display": "flex","alignItems": "flex-start","marginBottom": "14px"}),
            html.Div([
                html.Div(style={"width": "35px","height": "35px","borderRadius": "50%","backgroundColor": ampel2_color,"display": "inline-block","marginRight": "15px","marginTop": "4px","boxShadow": "0 0 8px 2px rgba(255, 255, 255, 0.5)","border": "2px solid #666","boxSizing": "border-box"}),
                html.Div([
                    html.Div(f"Ampel 2: Hebel Watch - Banken Trendfrüherkennung: Long oder Short? (5 bis 30 Minuten)", style={"fontSize": "100%","fontWeight": "bold"}),
                    html.Div("Erkennt: ob Banken verstärkt Longs oder Shorts anbieten, also wo sie - in diesem Augenblick - Risiken sehen", style={"marginLeft": "20px","fontSize": "90%","color": "#333","fontStyle": "normal"}),
                    html.Br(),
                    #html.Span("Kommentar: ", style={"marginLeft": "40px", "fontSize": "90%", "color": "#333", "fontStyle": "normal"}),
                    html.Div(f"{kommentar}", style={"marginLeft": "40px","fontSize": "90%","color": "#333","fontStyle": "normal"}),
                    html.Div([
                        html.Span(sofr_mini_emoji, style={"marginRight": "6px"}),
                        html.Span(f"SOFR-Spread: {sofr_bps} bps – {sofr_text}")
                    ], style={"marginLeft": "40px","fontSize": "90%","color": "#333","fontStyle": "normal"}),
    ])
         #       ])
            ], style={"display": "flex","alignItems": "flex-start","marginBottom": "20px"}),
            html.Div([
                html.Div(style={"width": "35px","height": "35px","borderRadius": "50%","backgroundColor": ampel3_color,"display": "inline-block","marginRight": "15px","marginTop": "4px","boxShadow": "0 0 8px 2px rgba(255, 255, 255, 0.5)","border": "2px solid #666","boxSizing": "border-box"}),
                html.Div([
                    html.Div("Ampel 3: Börsen Ereignisse (1 Tag vorher + Termintag)", style={"fontSize": "100%","fontWeight": "bold"}),
                    html.Div("Erkennt: Termine - Zinsentscheide, Hexensabbat, Quartalsberichte = Risiko", style={"marginLeft": "20px","fontSize": "90%","color": "#333"}),
                    html.Div([elem for i, line in enumerate((ampel3_text or "").splitlines())
     for elem in ((html.Span(line),) if i == 0 else (html.Br(), html.Span(line)))],
    style={"marginLeft": "40px","fontSize": "90%","color": "#333"})
                ])
            ], style={"display": "flex","alignItems": "flex-start","marginBottom": "20px"}),
            html.Div([
                html.Div(style={"width": "35px","height": "35px","borderRadius": "50%","backgroundColor": ampel4_color,"display": "inline-block","marginRight": "15px","marginTop": "4px","boxShadow": "0 0 8px 2px rgba(255, 255, 255, 0.5)","border": "2px solid #666","boxSizing": "border-box"}),
                html.Div([
                    html.Div(f"{ampel4_title}", style={"fontSize": "100%","fontWeight": "bold"}),
                    html.Div(_ampel4_descriptor_for(selected), style={"marginLeft": "15px","fontSize": "90%","color": "#333"}),

                    html.Div([
                        html.Br(),
                       #html.Span("Kommentar: ", style={"display": "block"}),
                        html.Span(ampel4_text.replace('<br>', '\n'), 
                                 style={"display": "block", "marginLeft": "0px", "fontSize": "90%", "color": "#333", "whiteSpace": "pre-line"})
                    ], style={"marginLeft": "40px"})
                ])
            ], style={"display": "flex","alignItems": "flex-start","marginBottom": "20px"}),
        ]),
        alarm_src,gong_src,news_bottom,

    )

# Interval/Reset
@app.callback(
    Output("interval-component", "interval"),
    Input("set-interval-btn", "n_clicks"),
    State("interval-input", "value"),
    prevent_initial_call=True
)
def change_interval(n_clicks, value):
    global refresh_interval
    if value and value >= 5:
        refresh_interval = int(value)
    return refresh_interval * 1000

@app.callback(
    Output("reset-btn", "n_clicks"),
    Input("reset-btn", "n_clicks"),              # manueller Reset (Desktop)
    Input("auto-reset-interval", "n_intervals"), # Auto-Reset (Server)
    prevent_initial_call=True
)
def reset_csv_files(n_clicks, auto_n):
    # Diese Funktion wird ausgelöst,
    # - wenn im Desktop-Modus der Reset-Button geklickt wird
    # - oder im Server-Modus der Auto-Timer tickt

    # 1) CSVs je Underlying leeren/neu anlegen
    for u in UNDERLYINGS.keys():
        file = get_csv_filename(u)
        try:
            if os.path.exists(file):
                os.remove(file)
        except Exception:
            pass
        empty = pd.DataFrame(columns=["timestamp", "long_avg", "short_avg", "index_change"])
        try:
            atomic_write_csv(empty, file)
        except Exception:
            pass

    # 2) Nur log_index.csv entfernen (log_ampel.csv existiert nicht mehr)
    try:
        p = os.path.join(CSV_FOLDER, "log_index.csv")
        if os.path.exists(p):
            os.remove(p)
    except Exception:
        pass

    # 3) Diverse Caches leeren
    for _clear in (
        lambda: _ATR_CACHE_BASE.clear(),
        lambda: _ATR_CACHE_CURR.clear(),
        lambda: _volatility_cache.clear(),
        lambda: _FINANZEN_CACHE.clear(),
        lambda: _P80_BAND_CACHE.clear(),
        lambda: _LM_CACHE.clear(),
        lambda: _LEVER_CACHE.clear(),
    ):
        try:
            _clear()
        except Exception:
            pass

    # News-/RSI-/SOFR-Cache
    try:
        _news_cache.update({"ts": 0, "items": []})
    except Exception:
        pass
    try:
        clear_rsi_cache()
    except Exception:
        pass
    try:
        reset_sofr_cache()
    except Exception:
        pass

    # 4) Sprung-Filter und Ampel-5-Testzustand zurücksetzen
    try:
        reset_jump_filters()
    except Exception:
        pass
    try:
        global _AMP5_RED_FLAG, TEST_AMP5_FORCE
        _AMP5_RED_FLAG = False
        TEST_AMP5_FORCE = None
    except Exception:
        pass

    # Rückgabe-Wert ist egal, Hauptsache der Output ist gesetzt
    # Wir setzen den Button-Zähler einfach auf 0 zurück.
    return 0




# globaler Lock sicherstellen
if "_DRIVER_POOL_LOCK" not in globals():
    _DRIVER_POOL_LOCK = threading.Lock()

def cleanup():
    global _DRIVER_POOL, _TMP_PROFILE_DIR
    closed = 0

    # 1) Pool-Inhalte unter Lock entnehmen, dann Dict leeren
    with _DRIVER_POOL_LOCK:
        items = list(_DRIVER_POOL.items())
        _DRIVER_POOL.clear()

    # 2) Außerhalb des Locks beenden
    for use_case, driver in items:
        if driver:
            with suppress(Exception):
                driver.quit()
                closed += 1

    # 3) Temp-Profile entfernen
    if _TMP_PROFILE_DIR and os.path.exists(_TMP_PROFILE_DIR):
        with suppress(Exception):
            shutil.rmtree(_TMP_PROFILE_DIR, ignore_errors=True)
        _TMP_PROFILE_DIR = None

    print(f"✅ Cleanup done (drivers={closed}).")

# einmalig registrieren:

if not globals().get("_CLEANUP_REGISTERED", False):
    atexit.register(cleanup)
    _CLEANUP_REGISTERED = True


# Erst beim Klick den Dialog öffnen
@app.callback(
    Output("confirm-exit", "displayed"),
    Input("exit-title", "n_clicks"),
    prevent_initial_call=True
)
def show_confirm(n_clicks):
    return True  # Dialog anzeigen


# oben:
import signal, threading, flask
from dash.exceptions import PreventUpdate

def _graceful_exit():
    """Ordnungsgemäßes Beenden der Anwendung."""
    print("🛑 Starte ordnungsgemäßes Beenden...")
    
    # 1) Threads stoppen
    try:
        stop_event.set()
    except:
        pass
        
    # 2) Driver und Services beenden
    try:
        shutdown_all_drivers()
    except Exception as e:
        print(f"⚠️ Fehler beim Beenden der Driver: {e}")
    
    # 3) Kurz warten damit Cleanup abgeschlossen wird
    import time
    time.sleep(1)
    
    # 4) Prozess beenden
    print("✅ Anwendung beendet.")
    os._exit(0)

@app.callback(
    Output("exit-title","children"),
    Input("confirm-exit","submit_n_clicks"),
    prevent_initial_call=True
)
def close_app(n):
    if not n:
        raise PreventUpdate
    threading.Thread(target=_graceful_exit, daemon=True).start()
    return "Beendet"


from contextlib import suppress
import threading, platform, subprocess, shutil

# gemeinsame Locks sicherstellen
if "_DRIVER_POOL_LOCK" not in globals():
    _DRIVER_POOL_LOCK = threading.Lock()
if "DRIVERS" not in globals(): DRIVERS = {}
if "_DRIVER_POOL" not in globals(): _DRIVER_POOL = {}
if "_DRIVERS" not in globals(): _DRIVERS = []
if "_SERVICES" not in globals(): _SERVICES = []
if "_SERVICE_PIDS" not in globals(): _SERVICE_PIDS = []
try:
    import psutil  # optional
except Exception:
    psutil = None

def shutdown_all_drivers():
    """Beendet alle WebDriver/Services prozesssicher und räumt auf."""
    import time
    to_quit = []
    to_stop = []
    pids = []

    # 1) Referenzen einsammeln & Container leeren (unter Lock)
    with _DRIVER_POOL_LOCK:
        to_quit.extend([d for d in DRIVERS.values() if d])
        DRIVERS.clear()

        to_quit.extend([d for d in _DRIVER_POOL.values() if d])
        _DRIVER_POOL.clear()

        to_quit.extend(list(_DRIVERS))
        _DRIVERS.clear()

        to_stop.extend(list(_SERVICES))
        _SERVICES.clear()

        pids.extend(list(_SERVICE_PIDS))
        _SERVICE_PIDS.clear()

    # 2) Driver beenden (außerhalb des Locks)
    for d in to_quit:
        with suppress(Exception):
            try:
                d.quit()
            except:
                pass
        time.sleep(0.1)  # Kurze Pause zwischen den Quits

    # 3) Services stoppen
    for s in to_stop:
        with suppress(Exception):
            try:
                s.stop()
            except:
                pass

    # 4) Prozesse terminieren - zuerst sanft, dann hart
    for pid in pids:
        with suppress(Exception):
            if psutil:
                try:
                    proc = psutil.Process(pid)
                    proc.terminate()  # Sanftes Beenden
                    proc.wait(timeout=3)  # Warten auf Beendigung
                except (psutil.NoSuchProcess, psutil.TimeoutExpired):
                    pass

    # 5) OS-weite Reste killen (best effort)
    time.sleep(1)  # Warten bevor hard kill
    if platform.system() == "Windows":
        kill_commands = [
            ["taskkill", "/F", "/IM", "chromedriver.exe", "/T"],
            ["taskkill", "/F", "/IM", "chrome.exe", "/T"]
        ]
    else:
        # Linux/macOS
        kill_commands = [
            ["pkill", "-9", "-f", "chromedriver"],
            ["pkill", "-9", "-f", "chrome"],
            ["pkill", "-9", "-f", "google-chrome"],
            ["pkill", "-9", "-f", "chrome_crashpad_handler"]
        ]

    for cmd in kill_commands:
        with suppress(Exception):
            subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)

    # 6) temporäre Profile entfernen
    with suppress(Exception):
        tmp = globals().get("_TMP_PROFILE_DIR")
        if tmp and os.path.exists(tmp):
            shutil.rmtree(tmp, ignore_errors=True)
            globals()["_TMP_PROFILE_DIR"] = None

    print("✅ Alle WebDriver/Prozesse bereinigt.")

# atexit nur einmal registrieren
if not globals().get("_CLEANUP_REGISTERED", False):
    atexit.register(shutdown_all_drivers)
    _CLEANUP_REGISTERED = True


def _register_shutdown_hooks():
    """Sorgt dafür, dass _cleanup bei Exit und Signalen aufgerufen wird."""
    import signal, atexit, threading
    global _CLEANUP_REGISTERED
    if _CLEANUP_REGISTERED:
        return

    # atexit zuletzt registrieren
    atexit.register(_cleanup)

    # Signale abfangen
    if threading.current_thread() is threading.main_thread():
        for s in (getattr(signal, "SIGINT", None),
                  getattr(signal, "SIGTERM", None),
                  getattr(signal, "SIGBREAK", None)):
            if s:
                try:
                    signal.signal(s, _signal_handler)
                except Exception:
                    pass

    _CLEANUP_REGISTERED = True



@callback(
    Output("last_update_time", "children"),
    Output("last_update_time", "style"),
    Input("ui-interval", "n_intervals"),
    prevent_initial_call=False
)
def _cb_last_query(_n):
    lb, _ = _read_health()
    ts = int(lb) if lb else 0
    txt = "—" if not ts else time.strftime("%H:%M:%S", time.localtime(ts))
    age = float("inf") if not ts else (time.time() - ts)
    color = "red" if age > 30 else "#888"
    return f"Letzte Abfrage: {txt}", {"color": color}

@app.callback(
    Output('futures-label', 'children'),
    Input('underlying-dropdown', 'value'),
)
def update_future_label(u):
    return _future_label_for(u)

@callback(
    Output("vola-label", "children"),
    Input("underlying-dropdown", "value"),
    Input("volatility-toggle", "value"),
)
def update_vola_label(underlying, toggle_val):
    u = underlying or "S&P 500"
    short = _vola_short(u)  # <— statt _vola_label_for
    active = 'ausblenden' if ('on' in (toggle_val or [])) else 'einblenden'
    return f"Volatilität ({short}) {active}"




# --- App-Start (lokal & Render) -----------------------------------
if __name__ == "__main__":
    reset_jump_filters()
    _LEVER_CACHE.clear()

    cleanup_stale_processes() 
    import os, sys, threading, traceback

    _register_shutdown_hooks()  # einmalig Hooks setzen

    # Hintergrund-Jobs (nicht blockierend)
    try:
        start_watchdog()
        start_update_thread()
        start_leverage_thread()
        warmup_drivers()
        warmup_requests()
    except Exception:
        traceback.print_exc()

    # Bind-Logik: Render setzt PORT -> 0.0.0.0; lokal -> 127.0.0.1
    port = int(os.getenv("PORT", 8050))
    on_render = "PORT" in os.environ
    host = "0.0.0.0" if on_render else os.getenv("HOST", "127.0.0.1")
    debug = (os.getenv("DASH_DEBUG", "0") == "1") and not on_render

    # Browser nur lokal öffnen
    if not on_render:
        try:
            import webbrowser
            threading.Timer(0.8, lambda: webbrowser.open(f"http://{host}:{port}")).start()
        except Exception:
            pass

    print(f"[bind] {host}:{port} (debug={debug})", flush=True)

    try:
       # Dash bevorzugt
         app.run(host=host, port=port, debug=debug, use_reloader=False)
         if __name__ == "__main__":
             if SERVER_VARIANT:
                 app.run_server(host=host, port=port, debug=debug, use_reloader=False)
         else:
                 app.run(host=host, port=port, debug=debug, use_reloader=False)

   # für "Render" diese Zeile nehmen, anstelle der oberen,(geht unter Windows nicht)    
        #app.run_server(host=host, port=port, debug=debug, use_reloader=False)
    except TypeError:
        # Fallback, falls app.run(...) erwartet wird
        app.run(host=host, port=port, debug=debug, use_reloader=False)



