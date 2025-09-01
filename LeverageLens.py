# Hebelwatch Markus Jurina (markus@jurina.biz) 31.08.2025 v69
# SOFR +Öffnungszeit update #
# Kontrolle bei Programmstart - notwendige Module

required_modules = {
    "pandas": "pandas",
    "dash": "dash",
    "selenium": "selenium",
    "webdriver_manager": "webdriver-manager",
    "yfinance": "yfinance",
    "simpleaudio": "simpleaudio"
}

fehlende_module = []
try:
    import selenium
except ImportError:
    fehlende_module.append("selenium")

try:
    import webdriver_manager
except ImportError:
    fehlende_module.append("webdriver-manager")

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
import platform
import pandas as pd
from bs4 import BeautifulSoup
from dash import Dash, dcc, html
from dash.dependencies import Output, Input, State
import plotly.graph_objs as go
import threading
import requests
from contextlib import contextmanager
from selenium import webdriver
from ereignisse_abruf import lade_oder_erstelle_ereignisse, bewerte_ampel_3
from ereignisse_abruf import compute_us_market_holidays
from selenium.webdriver.chrome.service import Service
from webdriver_manager.chrome import ChromeDriverManager
from selenium.webdriver.chrome.options import Options
import tempfile, shutil, atexit
from datetime import timedelta
import gc
import yfinance as yf
from functools import lru_cache
import math
import numpy as np
import pytz
from datetime import datetime
from contextlib import suppress
from threading import Lock
import re
import signal
import os, sys

# --- Imports (einmalig oben) ---
from selenium.webdriver.common.by import By
from collections import defaultdict
FILE_LOCKS = defaultdict(Lock)
from concurrent.futures import ThreadPoolExecutor
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
driver_pool = ThreadPoolExecutor(max_workers=2)  # Nur 2 gleichzeitige Driver
from selenium.common.exceptions import (
    StaleElementReferenceException,
    TimeoutException,
    NoSuchElementException,
    WebDriverException,
)
os.environ["ABSEIL_LOGGING_STDERR_THRESHOLD"] = "3"   # nur Errors
os.environ["GLOG_minloglevel"] = "3"
os.environ["NO_AT_BRIDGE"] = "1"  # weniger GTK-Warnungen
_FNG_RT = {"ts": 0, "val": None}
KEY_GLOBAL = "__global__"
DRIVERS: dict[str, "WebDriver"] = {}
DRIVER_LOCKS = defaultdict(threading.Lock)
import atexit, signal, sys, subprocess
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
# Ampel 1 – Empfindlichkeit + Trend-Filter (skaleninvariant)
AMP1_POS_DELTA       = 0.35   # symmetrisch: 0.5±DELTA → 0.85/0.15
AMP1_RECENT_WIN      = 60     # Punkte für Trendmessung (~10 min bei 10s-Takt)
AMP1_MIN_MOVE_SIGMA  = 1.2    # Faktor * Std der jüngsten Bewegungen
AMP1_MIN_MOVE_FLOOR  = 0.05   # absoluter Mindestschwellwert
_US_HOLI = {"year": None, "dates": set()}
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
    def __init__(self, rel_thresh=0.10):
        self.rel_thresh = rel_thresh
        self._last = None
        self._lock = Lock()
        self._just_blocked = False  # merkt sich, ob der letzte Tick geblockt wurde

    def reset(self):
        with self._lock:
            self._last = None
            self._just_blocked = False

    def update(self, x):
        with self._lock:
            if not _is_num(x):
                return self._last

            if self._last is None:
                self._last = x
                self._just_blocked = False
                return x

            # relativer Sprung?
            base = max(1e-12, abs(self._last))
            is_jump = abs(x - self._last) / base > self.rel_thresh

            if is_jump and not self._just_blocked:
                # genau *einmal* blocken
                self._last = x        # neuen Level merken
                self._just_blocked = True
                return None           # 1 Tick auslassen
            else:
                # danach sofort echte Werte übernehmen
                self._last = x
                self._just_blocked = False
                return x

# Instanzen
LEVER_LONG_FILTER  = OneOutlierFilter(rel_thresh=0.10)
LEVER_SHORT_FILTER = OneOutlierFilter(rel_thresh=0.10)
VOL_FILTER         = OneOutlierFilter(rel_thresh=0.10)
INDEX_FILTER       = OneOutlierFilter(rel_thresh=0.10)

def reset_jump_filters(_=None):
    LEVER_LONG_FILTER.reset()
    LEVER_SHORT_FILTER.reset()
    VOL_FILTER.reset()
    INDEX_FILTER.reset()



def get_driver(*args, headless=True):
    # args werden ignoriert, nur für Kompatibilität zu get_driver("role", key)
    if SHUTTING_DOWN:
        raise RuntimeError("Shutdown in progress")

    # vorhandenen Driver wiederverwenden
    for d in list(_DRIVERS):
        try:
            _ = d.title
            return d
        except:
            pass


    from selenium.webdriver.chrome.service import Service
    from webdriver_manager.chrome import ChromeDriverManager

    opts = webdriver.ChromeOptions()
    if headless:
        opts.add_argument("--headless=new")
    opts.add_experimental_option("detach", False)
    opts.add_argument("--disable-background-networking")
    opts.add_argument("--disable-features=OptimizationGuideModelDownloading")
    # Wichtige Optionen für sauberes Beenden
    opts.add_argument("--no-sandbox")
    opts.add_argument("--disable-dev-shm-usage")
    opts.add_argument("--disable-gpu")
    opts.add_argument("--log-level=3")
    opts.add_experimental_option('excludeSwitches', ['enable-logging', 'enable-automation'])
    opts.add_experimental_option('useAutomationExtension', False)

    service = Service(ChromeDriverManager().install())
    drv = webdriver.Chrome(service=service, options=opts)

    _DRIVERS.append(drv)
    _SERVICES.append(service)
    try:
        if getattr(service, "process", None):
            _SERVICE_PIDS.append(service.process.pid)
    except:
        pass
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
    import atexit, sys, subprocess
    try:
        for d in list(_DRIVERS):
            try: d.quit()
            except: pass
        for s in list(_SERVICES):
            try:
                p = getattr(s, "process", None)
                if p:
                    try: p.terminate()
                    except: pass
            except: pass
    finally:
        # Windows-Fallback: hart killen
        for im in ("chromedriver.exe", "chrome.exe"):
            try:
                subprocess.run(["taskkill", "/F", "/IM", im, "/T"],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            except: pass
atexit.register(_cleanup)

def _signal_handler(sig, frame):
    _cleanup()
    sys.exit(0)





# Signale registrieren
def _register_signals():
    import threading
    if threading.current_thread() is threading.main_thread():
        for s in (getattr(signal, "SIGINT", None),
                  getattr(signal, "SIGTERM", None),
                  getattr(signal, "SIGBREAK", None)):
            if s:
                signal.signal(s, _signal_handler)

atexit.register(_cleanup)



TZ_BERLIN = pytz.timezone("Europe/Berlin")


# für Ampel 2 erweiterung########

# --- SOFR-Proxy (TED ersatz) --------------------------------------------------
FRED_API_KEY = "ac24c6331bbe4bd92e5cc0ce443d4d2e"
_FRED_URL = "https://api.stlouisfed.org/fred/series/observations"
_SOFR_CACHE = {"ts": 0, "bps": None, "text": "SOFR-Proxy: keine Daten."}

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

def find_text_retry(driver, locator: tuple[str, str], wait_s=10, retries=3):
    for _ in range(retries):
        try:
            el = WebDriverWait(driver, wait_s).until(EC.visibility_of_element_located(locator))
            return el.text
        except StaleElementReferenceException:
            continue
    raise TimeoutException("stale after retries")


def get_sofr_proxy_comment(cache_sec=1800):
    """Gibt (bps:int, text:str). Cacht für cache_sec Sekunden."""
    import time
    now = time.time()
    if now - _SOFR_CACHE["ts"] < cache_sec and _SOFR_CACHE["bps"] is not None:
        return _SOFR_CACHE["bps"], _SOFR_CACHE["text"]

    sofr = _fred_last("SOFR")              # Overnight SOFR, % p.a.
    tb3m = _fred_last("DGS3MO") or _fred_last("TB3MS")  # 3M T-Bill, % p.a.
    if sofr is None or tb3m is None:
        return _SOFR_CACHE["bps"] or 0, "SOFR-Proxy: keine Daten."

    spread_pp = sofr - tb3m
    bps = int(round(spread_pp * 100))
  #  bps = 45 # Test SOFR Override   5 45 75

    # Kategorie-Text gemäß deiner Skala
    if abs(bps) > 100:
        txt = "Extrem (Systemkrise): >100 bps – Historisch nur in Krisen (2007 Bankenkrise bis 465 bps, Corona 2020 140 bps)."
    elif abs(bps) >= RSI_OVERBOUGHT:
        txt = "Kritisch (Liquiditätsstress): RSI_OVERBOUGHT–100 bps – Banken leihen zögerlich. Meist Vorbote stärkerer Abverkäufe."
    elif abs(bps) >= 40:
        txt = "Erhöht (Interbankmarkt wird nervös): 40–RSI_OVERBOUGHT bps – Frühwarnsignal für knapper werdende Liquidität."
    elif abs(bps) >= 10:
        txt = "Normalbereich (kein Stress): 10–40 bps – Typisch in ruhigen Marktphasen."
    else:
        txt = "Unter Normalbereich (<10 bps) – sehr ruhige Interbank-Lage"

    _SOFR_CACHE.update({"ts": now, "bps": bps, "text": txt})
    return bps, txt
##################################################################################################
def scrape_onvista_leverage(current_underlying: str) -> list[float]:
    key = f"onvista_{current_underlying}"
    lock = DRIVER_LOCKS[key]
    with lock:
        drv = get_driver("onvista", current_underlying)
        url_long = ONVISTA_URLS[current_underlying]["long"]
        drv.get(url_long)

        WebDriverWait(drv, 10).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "main, #page, .content"))
        )

        with suppress(Exception):
            table_txt = find_text_retry(drv, (By.CSS_SELECTOR, "table tbody"), wait_s=10, retries=3)
            vals = _parse_leverage_numbers(table_txt)
            if vals:
                return vals

        drv.get(ONVISTA_URLS[current_underlying]["short"])
        WebDriverWait(drv, 10).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "main, #page, .content"))
        )
        table_txt = find_text_retry(drv, (By.CSS_SELECTOR, "table tbody"), wait_s=10, retries=3)
        return _parse_leverage_numbers(table_txt)

def switch_underlying(new_underlying: str):
    # A) laufenden Loop sauber stoppen
    stop_event.set()
    if update_thread and update_thread.is_alive():
        update_thread.join(timeout=5)

    # B) alte Driver schließen
    reset_drivers_on_underlying_change(old_underlying=selected_underlying)

    # C) globalen Zustand setzen
    set_selected_underlying(new_underlying)  # deine Setter-Funktion
    for k in list(_volatility_cache.keys()):
        _volatility_cache[k] = {"value": None, "ts": 0}

    # D) Caches leeren
    with suppress(Exception):
        scrape_average_leverage.cache_clear()
    # weitere @lru_cache-Funktionen hier leeren

    # E) neu starten
    stop_event.clear()
    start_update_thread()



def get_vstoxx_change_stock3(driver=None, timeout=25, retries=3):
    global _last_vstoxx_change
    url = "https://stock3.com/indizes/vstoxx-volatilitaetsindex-17271029/"

    if driver is None:
        driver = get_driver("general", KEY_GLOBAL)

    for attempt in range(retries):
        try:
            driver.get(url + f"?t={int(time.time())}")
            try:
                accept_cookies_if_present(driver, timeout=5)
            except Exception:
                pass

            WebDriverWait(driver, timeout).until(lambda d: _parse_vstoxx_value(d) is not None)
            val = _parse_vstoxx_value(driver)
            if val is not None and val != 0.0:
                _last_vstoxx_change = round(val, 2)
                print(f"✔️ VSTOXX Veränderung: {_last_vstoxx_change} % (stock3)")
                return _last_vstoxx_change

            driver.refresh()
            time.sleep(2)
        except (TimeoutException, StaleElementReferenceException, WebDriverException) as e:
            print(f"⚠️ VSTOXX Versuch {attempt+1}: {e}")
            time.sleep(3)
    print(f"⚠️ VSTOXX: Fallback auf letzten Wert: {_last_vstoxx_change}")
    return _last_vstoxx_change

def get_vstoxx_change_onvista():
    try:
        d = get_driver("general", KEY_GLOBAL)
        d.get("https://www.onvista.de/index/VSTOXX-Volatilitaetsindex-Index-12105800")
        time.sleep(2.5)
        # Positiv/negativ wird per Klasse markiert; Wert steckt im value-Attribut des <data>-Tags.
        try:
            el = d.find_element(By.CSS_SELECTOR, "data.text-positive.whitespace-nowrap.ml-4")
        except Exception:
            el = d.find_element(By.CSS_SELECTOR, "data.text-negative.whitespace-nowrap.ml-4")
        vstoxx_change = el.get_attribute("value")
        return float(str(vstoxx_change).replace(",", "."))
    except Exception as e:
        print(f"⚠️ OnVista VSTOXX Fehler: {e}")
        return None


def _parse_vstoxx_value(driver):
    """
    Hilfsfunktion: Liest den Prozentwert aus dem VSTOXX-Element.
    Gibt einen float oder None zurück.
    """
    try:
        el = driver.find_element(By.CSS_SELECTOR, "span.instrument-value.changePerc")
        raw = (el.text or el.get_attribute("data-inst-formatted") or "").strip()
        # Bereinige den String und konvertiere ihn in eine float-Zahl
        txt = (raw.replace('%', '')
                  .replace('\xa0', ' ')
                  .replace(' ', '')
                  .replace('−', '-')
                  .replace('+', '')
                  .replace(',', '.'))
        return float(txt)
    except (NoSuchElementException, ValueError, Exception):
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
LEVER_MIN, LEVER_MAX = 2.0, 30.0
BASE_LEVERAGE_DEFAULT = 20.0  # Startwert im UI und Fallback


# Kategorien relativ zum 30-T-Median m (x = aktueller ATR5% geglättet)
# r = x/m
VOLA_THRESH = {
    "very_low": 0.60,   # r < 0.60
    "low":      0.90,   # 0.60 ≤ r < 0.90
    "high":     1.10,   # 0.90 ≤ r ≤ 1.10  -> normal
    "very_high":1.50,   # 1.10 < r ≤ 1.50  -> erhöht
}                       # r > 1.50 -> sehr hoch

VOLA_COLORS = {
    "very_low":  "#d93636",  # rot
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
    "Nasdaq": "^IXIC",
}

VOLA_DESCRIPTIONS = {
    "very_low": "Volatilität unter 60% des Medians → Handel nicht empfohlen, da ein Trend schwer erkennbar ist",
    "low": "60-90% des Medians → unterdurchschn. Volatilität; Es empfiehlt sich einen anderen Index anzuschauen",
    "normal": "90-110% des Medians → typische Marktvolatilität",
    "elevated": "110-150% des Medians → überdurchschn. Volatilität, Chancen steigen, aber der Hebel sollte angepasst werden",
    "very_high": "über 150% des Medians → extreme Volatilität, Hebel-anpassung und News prüfen",
    "off": "Keine Volatilitätsdaten verfügbar"
}

_ATR_CACHE_BASE = {}   # {underlying: {"ts": epoch, "m": float}}
_ATR_CACHE_CURR = {}   # {underlying: {"ts": epoch, "x": float}}

def _trading_hours(underlying: str):
    if underlying in ("Dax", "EURO STOXX 50"):
        return ("09:00", "17:35")
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
    return df.between_time(start, end)

def _atr5pct(df: "pd.DataFrame"):
    if df.empty: return pd.Series(dtype=float)
    o,h,l,c = df["Open"], df["High"], df["Low"], df["Close"]
    prev_c  = c.shift(1)
    tr = np.maximum(h-l, np.maximum((h - prev_c).abs(), (l - prev_c).abs()))
    atr = tr.ewm(span=14, adjust=False).mean()
    atr_pct = (atr / c) * 100.0
    return atr_pct
    
INDEX_POOL = ["Dax","EURO STOXX 50","S&P 500","Dow Jones","Nasdaq"]

def _mean_baseline_vola(exclude: str | None = None) -> float | None:
    vals = []
    for u2 in INDEX_POOL:
        if exclude and u2 == exclude:
            continue
        m2 = _get_baseline_m(u2)
        if m2 and m2 > 0:
            vals.append(float(m2))
    if not vals:
        return None
    return float(np.mean(vals))


def _get_baseline_m(underlying: str) -> float | None:
    now = time.time()
    ent = _ATR_CACHE_BASE.get(underlying, {})
    # Cache 30 Minuten
    if ent and now - ent.get("ts", 0) < 1800:
        return ent.get("m")
    sym = YF_SYMBOL.get(underlying)
    if not sym: return None
    df = _yf_5m(sym, period=f"{ATR_BASE_DAYS}d")
    df = _filter_hours(df, underlying)
    atr_pct = _atr5pct(df)
    m = float(_to_scalar(atr_pct.median())) if not atr_pct.empty else None  # Fixed line
    if m and m > 0:
        _ATR_CACHE_BASE[underlying] = {"ts": now, "m": m}
    return m

def _get_current_x(underlying: str) -> float | None:
    now = time.time()
    ent = _ATR_CACHE_CURR.get(underlying, {})
    # wir aktualisieren im Callback durch Interval; hier kleiner Cache 60s
    if ent and now - ent.get("ts", 0) < 60:
        return ent.get("x")
    sym = YF_SYMBOL.get(underlying)
    if not sym: return None
    df = _yf_5m(sym, period="2d")
    df = _filter_hours(df, underlying)
    atr_pct = _atr5pct(df)
    if atr_pct.empty: 
        return None
    x = float(_to_scalar(atr_pct.ewm(span=ATR_EMA_SPAN, adjust=False).mean().iloc[-1]))  # Fixed line
    _ATR_CACHE_CURR[underlying] = {"ts": now, "x": x}
    return x

def _categorize(x: float, m: float) -> str:
    if not x or not m or m <= 0: return "off"
    r = x / m
    if r < VOLA_THRESH["very_low"]:             return "very_low"
    if r < VOLA_THRESH["low"]:                  return "low"
    if r <= VOLA_THRESH["high"]:                return "normal"
    if r <= VOLA_THRESH["very_high"]:           return "elevated"
    return "very_high"

def _recommend_leverage(x: float, m: float, base_leverage: float | None = None) -> float | None:
    if not x or not m or x <= 0 or m <= 0:
        return None
    if base_leverage is None:
        base_leverage = BASE_LEVERAGE_DEFAULT
    raw = base_leverage * (m / x)
    clipped = min(LEVER_MAX, raw)              # keine Untergrenze
    return round(clipped * 2) / 2.0



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

def build_vola_strip(category: str, base_leverage: float, recommended_leverage) -> list:
    labels = [("very_low","Sehr niedrig"), ("low","Niedrig"), ("normal","Normal"),
              ("elevated","Erhöht"), ("very_high","Sehr hoch")]
    segs = []

    # auf Skalar normieren, FutureWarning vermeiden
    base_leverage = _to_scalar(base_leverage)
    recommended_leverage = None if recommended_leverage is None else _to_scalar(recommended_leverage)

    for key, lab in labels:
        active = (key == category)
        bg = VOLA_COLORS.get(key, "#eee") if active else "#eeeeee"
        border = f"2px solid {VOLA_COLORS.get(key, '#aaa')}" if active else "1px solid #cccccc"

        if active:
            # immer variabel anzeigen (auch bei "normal")
            if recommended_leverage is not None:
                try:
                    val_txt = f"{float(_to_scalar(recommended_leverage)):.1f}×"
                except Exception:
                    val_txt = "\u00A0"
            else:
                val_txt = "\u00A0"
        else:
            # inaktive Felder bleiben leer
            val_txt = "\u00A0"

        segs.append(html.Div([
            html.Div(lab,     style={"fontSize":"16px","lineHeight":"1.05","fontWeight":"600","minHeight":"18px"}),
            html.Div(val_txt, style={"fontSize":"16px","lineHeight":"1.05","fontWeight":"600","minHeight":"18px"})
        ], style={
            "flex":"0 0 84px",
            "display":"flex","flexDirection":"column","alignItems":"center","justifyContent":"center",
            "textAlign":"center","padding":"6px 4px",
            "backgroundColor": bg, "border": border, "borderRadius":"6px",
            "marginRight":"4px","minHeight":"48px"
        }))
    segs[-1].style["marginRight"] = "0px"
    return segs




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

    service = Service(ChromeDriverManager().install())
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

FONT_STACK = "Segoe UI, Segoe UI Variable, Roboto, Helvetica Neue, Arial, Noto Sans, Liberation Sans, system-ui, -apple-system, sans-serif"


# Initialize the app mit korrektem Asset-Pfad (für PyInstaller-Linux wichtig)
app = Dash(
    __name__,
    assets_folder=resource_path("assets"),
    assets_url_path="/assets"
)


# -----------------------------------------------
# Konfiguration / Konstanten
# -----------------------------------------------
show_volatility = True
ampel1_text = "Standard Kommentar"
NEWS_REFRESH_SECONDS = 60
NEWS_TOTAL_ITEMS = 9
NEWS_PAGE_SIZE = 5
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

def is_market_open(underlying):
    tz = pytz.timezone('Europe/Berlin')
    now = datetime.now(tz)
    market = "USA" if underlying in ["Nasdaq", "S&P 500", "Dow Jones"] else "EUROPE"
    start_time = MARKET_TIMES[market]["start"]
    end_time = MARKET_TIMES[market]["end"]
    start_dt = now.replace(hour=start_time["hour"], minute=start_time["minute"], second=0, microsecond=0)
    end_dt   = now.replace(hour=end_time["hour"],   minute=end_time["minute"],   second=0, microsecond=0)
    market_hours = f"{start_time['hour']:02d}:{start_time['minute']:02d}-{end_time['hour']:02d}:{end_time['minute']:02d} Uhr MEZ"

    # Wochenende
    if now.weekday() >= 5:
        return f"❌ Börse geschlossen ({market_hours})"

    # Feiertage
    d_iso = now.date().isoformat()
    if market == "USA":
        if d_iso in _us_holiday_dates(now.year):
            return f"❌ Börse geschlossen (Feiertag, {market_hours})"
    else:
        if (now.month, now.day) in HOLIDAYS_FIXED.get("EUROPE", set()):
            return f"❌ Börse geschlossen (Feiertag, {market_hours})"

    return f"✅ Börse geöffnet ({market_hours})" if start_dt <= now <= end_dt else f"❌ Börse geschlossen ({market_hours})"



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


def accept_cookies_if_present(d, timeout=6):
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

# Beispiel:
# result = safe_concat([df1, df2, df3], ignore_index=True, sort=False, copy=False)


# News
SHOW_NEWS_INSTEAD_OF_COMMENT = True
_news_cache = {"ts": 0, "items": []}

def get_top_news(max_items=9, cache_seconds=60):
    now = time.time()
    if now - _news_cache["ts"] < cache_seconds and _news_cache["items"]:
        return _news_cache["items"]
    rss_url = "https://api.boerse-frankfurt.de/v1/feeds/news.rss"
   #rss_url = "https://www.tagesschau.de/wirtschaft/finanzen/index~rss2.xml"
    #rss_url = "https://www.finanztreff.de/feed/marktberichte.rss"
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
    page_items = headlines[start:end] if end <= total else (headlines[start:] + headlines[:end - total])
    page_info = f" {page_index + 1}/{num_pages}"
    return html.Div([
        html.Div([
            html.Span(f"Börsennachrichten (boerse-frankfurt.de) Seite {page_info}", style={"fontWeight": "bold", "display": "block"}),
            html.Span(f"Stand: {last_str}", style={"color": "#555", "fontSize": "90%", "display": "block"})
        ], style={"marginBottom": "10px"}),
        html.Ul([
            html.Li(
                html.A(title, href=link, target="_blank", style={"textDecoration": "none", "color": "#004c99"}),
                style={"marginBottom": "8px", "listStyleType": "none"}
            )
            for title, link in page_items
        ], style={"paddingLeft": "0", "marginTop": "0"})
    ], style={"position": "absolute","right": "30px","top": "460px","width": "400px","backgroundColor": "#e0e0e0","padding": "12px","borderRadius": "8px","zIndex": "1000"})

#Position news block top": "460px","width":


# RSI
def get_rsi(ticker_symbol, period=8):
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
        return rsi.iloc[-1]
    except Exception as e:
        print(f"Fehler bei RSI-Berechnung für {ticker_symbol}: {e}")
        return None

def bewerte_rsi_ampel(rsi_value):
    if rsi_value is None:
        return "#808080", "RSI: Keine Daten verfügbar", "Keine Daten"
    if rsi_value >= RSI_OVERBOUGHT:
        return "#ff0000", "RSI-Indikator", f"Risiko: Korrektur innerhalb 8 Tage wahrscheinlich! RSI={rsi_value:.1f}%"
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
    return {"Dax":"^GDAXI","S&P 500":"^GSPC","EURO STOXX 50":"^STOXX50E","Dow Jones":"^DJI","Nasdaq":"^IXIC"}.get(underlying,None)

FARBCODES = {"green":"#90EE90","yellow":"yellow","red":"red","gray":"gray","orange":"#FFA500"}

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
    "Nasdaq": {
        "long": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-NASDAQ-100?idExerciseRight=2",
        "short": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-NASDAQ-100?idExerciseRight=1",
       
    }
}

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

refresh_interval = 10
last_fetch_time = "-"
ALARM_THRESHOLD = 999
stop_event = threading.Event()
update_thread = None

#_last_vdax_change = None
#_last_EURO_STOXX_50_change = None
# Verwende ein Dictionary:
_volatility_cache = {
    "Dax": {"value": None, "ts": 0},
    "S&P 500": {"value": None, "ts": 0},
    "EURO STOXX 50": {"value": None, "ts": 0},
    "Dow Jones": {"value": None, "ts": 0},
    "Nasdaq": {"value": None, "ts": 0}
}

# Sichtbar konfigurierbar:
VDAX_WAIT_OVERRIDE = None  # z.B. 4 setzen, sonst dynamisch

def _extract_percent(text: str) -> float | None:
    m = re.search(r"([+-]?\d+[.,]\d+)\s*%", text)
    if not m:
        return None
    try:
        return float(m.group(1).replace(".", "").replace(",", "."))
    except ValueError:
        return None

def get_vdax_change(timeout=12):
    """
    VDAX %-Änderung von boerse-frankfurt.de robust auslesen.
    Probiert mehrere Selektoren. Kein None ins Cache schreiben.
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

    try:
        val = _try_once()
        if val is None:
            # Driver neu und zweiter Versuch
            with _DRIVER_POOL_LOCK:
                key = f"general_{selected_underlying}"
                drv = _DRIVER_POOL.get(key)
                try:
                    if drv: drv.quit()
                except Exception:
                    pass
                _DRIVER_POOL.pop(key, None)
            val = _try_once()
    except Exception as e:
        print(f"⚠️ VDAX Frankfurt fehlgeschlagen: {e}")
        val = None

    if val is None:
        val = get_vdax_change_finanztreff()
   # if val is None:
  #      val = get_vdax_change_yahoo()

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

def get_index_data(underlying):
    """
    Liefert (prozentuale Tagesänderung, aktueller Close als String, Farbmarker).
    Nutzt Yahoo Finance via yfinance.
    """
    try:
        ticker = {
            "Dax": "^GDAXI",
            "S&P 500": "^GSPC",
            "EURO STOXX 50": "^STOXX50E",
            "Dow Jones": "^DJI",
            "Nasdaq": "^IXIC"
        }.get(underlying)

        if not ticker:
            print(f"Unbekannter Index: {underlying}")
            return None, "-", "gray"

        data = yf.Ticker(ticker).history(period="2d")
        if len(data) >= 2:
            prev = data["Close"].iloc[-2]
            curr = data["Close"].iloc[-1]
            change = ((curr - prev) / prev) * 100
        else:
            raise ValueError("Keine Daten von Yahoo verfügbar")

        return change, f"{curr:.2f}", "color"

    except Exception as e:
        print(f"Fehler bei Yahoo-Finance-Abfrage: {e}")
        return None, "-", "gray"


def cleanup_memory():
    gc.collect()
    # WebDriver-Cache leeren
    if _DRIVER:
        _DRIVER.execute_script("window.open('','_blank').close()")
        _DRIVER.execute_script("window.location.reload(true)")


def get_volatility_change(underlying):
    """
    Liefert die prozentuale Tagesänderung des passenden Volatilitätsindex
    mit unterlying-spezifischem Caching.
    """
    global _volatility_cache
    
    # Cache-Prüfung (5 Minuten Cache)
    now = time.time()
    cache_data = _volatility_cache.get(underlying, {"value": None, "ts": 0})
    if now - cache_data["ts"] < 10 and cache_data["value"] is not None:
        return cache_data["value"]
    
    try:
        if underlying == "EURO STOXX 50":
            val = get_vstoxx_change_onvista()            
        elif underlying == "Dax":
            val = get_vdax_change()
            if val is None:
                val = get_vdax_change_finanztreff()
        elif underlying == "S&P 500":
            val = get_vix_change_yahoo()
        elif underlying == "Dow Jones":
            val = get_vxd_change_yahoo()
        elif underlying == "Nasdaq":
            val = get_vxn_change_yahoo()
        else:
            val = None
            
        # Cache aktualisieren
        _volatility_cache[underlying] = {"value": val, "ts": now}
        return val
        
    except Exception as e:
        print(f"...{e}")
        if now - cache_data.get("ts", 0) < 60:
            return cache_data.get("value")
            return None

from contextlib import suppress

def reset_drivers_on_underlying_change(old_underlying: str | None = None):
    keys = list(DRIVERS.keys())
    if old_underlying is None:
        kill = [k for k in keys if k.startswith("onvista_")]
    else:
        kill = [k for k in keys if k.endswith(f"_{old_underlying}")]
    for k in kill:
        drv = DRIVERS.pop(k, None)
        if drv:
            with suppress(Exception):
                drv.quit()
        with suppress(Exception):
            DRIVER_LOCKS.pop(k, None)


import re

def _parse_leverage_numbers(txt: str) -> list[float]:
    # erfasst z.B. "x24,58" oder "24.58" oder "24,58"
    nums = re.findall(r"(?:x)?(\d{1,3}(?:[.,]\d{1,2})?)", txt, flags=re.IGNORECASE)
    out = []
    for n in nums:
        n = n.replace(".", "").replace(",", ".")
        try:
            v = float(n)
            if 0.5 <= v <= 200:   # 0 und Kleinkram raus, Obergrenze bleibt wie besprochen
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
INDEX_POOL = ["Dax","EURO STOXX 50","S&P 500","Dow Jones","Nasdaq"]  # deine 5

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

def log_ampel_event(timestamp, delta_long, delta_short, ampel, kommentar):
    filename = os.path.join(CSV_FOLDER, "log_ampel.csv")
    log_exists = os.path.exists(filename)
    with open(filename, mode='a', newline='', encoding='utf-8') as file:
        writer = csv.writer(file, lineterminator='\n')
        if not log_exists:
            writer.writerow(["timestamp", "delta_long", "delta_short", "ampel", "kommentar"])
        writer.writerow([timestamp, delta_long, delta_short, ampel, kommentar])

def log_index_event(timestamp, index_change):
    filename = os.path.join(CSV_FOLDER, "log_index.csv")
    log_exists = os.path.exists(filename)
    with open(filename, mode='a', newline='', encoding='utf-8') as file:
        writer = csv.writer(file, lineterminator='\n')
        if not log_exists:
            writer.writerow(["timestamp", "index_change"])
        writer.writerow([timestamp, index_change])

def _wait_onvista_table(d, timeout=20):
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
    key = f"onvista_{get_selected_underlying()}"
    with DRIVER_LOCKS[key]:
        d = get_driver("onvista", get_selected_underlying())
        for attempt in range(2):
            d.get(url_onvista)
            accept_cookies_if_present(d, timeout=6)
            try:
                _wait_onvista_table(d, timeout=20)
                txt = find_text_retry(d, (By.CSS_SELECTOR, "table tbody"), wait_s=10, retries=3)
                vals = _parse_leverage_numbers(txt or "")
                if vals: 
                    print(f"Gefundene Hebelwerte von OnVista: {vals}")
                    return sum(vals)/len(vals)
            except TimeoutException:
                pass
            d.refresh(); time.sleep(1.0)
    print("Keine Hebelwerte gefunden (nur OnVista aktiv)."); return None

    


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
        ampel_symbol = "🟡"; base_kommentar = "🟡 Neutral: Long- und Short-Hebel gleich. Evtl: Programm neu starten und CSV löschen"
    thresholds = get_dynamic_thresholds(df_history if df_history is not None else pd.DataFrame())
    rel_delta_long = (long_now - long_prev) / long_prev * 100 * thresholds['leverage_volatility_factor'] if long_prev != 0 else 0
    rel_delta_short = (short_now - short_prev) / short_prev * 100 * thresholds['leverage_volatility_factor'] if short_prev != 0 else 0
    if rel_delta_short <= thresholds['short_crash']:
        ampel_symbol = "🔴"; base_kommentar = f"🔴 Crash-Alarm: Shorts ↓{abs(rel_delta_short):.1f}% (Volatilität: {thresholds['leverage_volatility_factor']:.1f}x)"
    elif rel_delta_short <= thresholds['short_warning']:
        ampel_symbol = "🟠"; base_kommentar = f"🟠 Frühwarnung: Shorts ↓{abs(rel_delta_short):.1f}% (Schwelle: {thresholds['short_warning']}%)"
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
        log_ampel_event(timestamp, rel_delta_long, rel_delta_short, ampel_symbol, kommentar)
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
    market_hours = MARKET_TIMES.get("USA", {"start": {"hour": 15, "minute": 30}, "end": {"hour": 22, "minute": 0}})
    return f"{market_comment} (Öffnungszeiten: {market_hours['start']['hour']:02d}:{market_hours['start']['minute']:02d}-{market_hours['end']['hour']:02d}:{market_hours['end']['minute']:02d} Uhr MEZ)"


def _ft_accept_cookies_quick(d, timeout=6):
    _ft_accept_cookies(d, timeout=timeout)


def get_ampel1_status(df, selected_underlying):
    # skaleninvarianter Orange-Filter; Grundstruktur aus Originalfunktion. :contentReference[oaicite:0]{index=0}
    if len(df) < 20 or 'volatility_change' not in df.columns:
        return FARBCODES["gray"], 0.5, "Nicht genug Daten. 50 sec warten."
    try:
        df_window = df.iloc[-min(len(df), 654):]
        v_now = df_window['volatility_change'].iloc[-1]
        i_now = df_window['index_change'].iloc[-1]
        timestamp = df_window['timestamp'].iloc[-1]
        schnittzeit = timestamp.strftime("%H:%M")
        vola_min = df_window['volatility_change'].min()
        vola_max = df_window['volatility_change'].max()
        rel_pos = (v_now - vola_min) / (vola_max - vola_min) if vola_max != vola_min else 0.5
        minmax_text = f"Min: {vola_min:.2f} %, Max: {vola_max:.2f} %"
        vola_wert = f"{v_now:.2f} %"
        kommentar_vorab = {"Dax": "VDAX", "S&P 500": "VIX", "EURO STOXX 50": "VSTOXX", "Dow Jones": "VXD"}.get(selected_underlying, "VXN")

        # --- skaleninvarianter Trend-Filter (Fallbacks, falls Konstanten noch nicht gesetzt sind) ---
        AMP1_POS_DELTA      = float(globals().get("AMP1_POS_DELTA", 0.35))   # symmetrisch: 0.5±DELTA → 0.85/0.15
        AMP1_RECENT_WIN     = int(globals().get("AMP1_RECENT_WIN", 60))      # Punkte für Trendmessung
        AMP1_MIN_MOVE_SIGMA = float(globals().get("AMP1_MIN_MOVE_SIGMA", 1.2))
        AMP1_MIN_MOVE_FLOOR = float(globals().get("AMP1_MIN_MOVE_FLOOR", 0.05))

        d = df_window["volatility_change"].diff().dropna()
        recent = d.tail(AMP1_RECENT_WIN)
        sigma = float(recent.std(ddof=0)) if len(recent) else 0.0
        min_move = max(AMP1_MIN_MOVE_FLOOR, AMP1_MIN_MOVE_SIGMA * sigma)

        w = min(AMP1_RECENT_WIN, max(1, len(df_window) - 1))
        delta_w = float(v_now - df_window['volatility_change'].iloc[-1 - w])

        POS_RISE = 0.5 + AMP1_POS_DELTA
        POS_FALL = 0.5 - AMP1_POS_DELTA

        # --- Logik ---
        if v_now < i_now and rel_pos < 0.6:
            return FARBCODES["green"], rel_pos, f"{kommentar_vorab} – Vola unter Index – Entspannt.(Veränderung: {vola_wert}, {minmax_text})"

        # unter Index, hoch im Tagesband → ORANGE nur bei jüngstem Aufwärts-Trend
        elif (v_now < i_now and rel_pos >= POS_RISE and delta_w > 0 and abs(delta_w) >= min_move):
            return FARBCODES["orange"], rel_pos, f"{kommentar_vorab} – Vola unter Index (gut), aber steigender Trend.(Veränderung: {vola_wert}, {minmax_text})"

        # über Index, tief im Tagesband → ORANGE nur bei jüngstem Abwärts-Trend
        elif (v_now > i_now and rel_pos <= POS_FALL and delta_w < 0 and abs(delta_w) >= min_move):
            return FARBCODES["orange"], rel_pos, f"{kommentar_vorab} – Vola über Index, aber klar rückläufig – Entspannung möglich.(Veränderung: {vola_wert}, {minmax_text})"

        if v_now > i_now:
            return FARBCODES["red"], rel_pos, f"{kommentar_vorab} – Vola über Index – Warnung! Tipp: In Grafik einblenden (Rot seit {schnittzeit}, Veränderung: {vola_wert}, {minmax_text})"
        if vola_max == vola_min and v_now < i_now:
            return FARBCODES["green"], 0.5, f"{kommentar_vorab} – Vola konstant unter Index – Ruhiger Markt (Veränderung: {vola_wert}, Min/Max = {vola_min:.2f} %)"
    except Exception as e:
        return FARBCODES["gray"], 0.5, f"Fehler in Ampel 1 Analyse: {e}"


# === finanztreff.de Backup ===


def _ft_accept_cookies(d, timeout=8):
    try:
        WebDriverWait(d, timeout).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        for how, sel in [
            (By.CSS_SELECTOR, "button#onetrust-accept-btn-handler"),
            (By.XPATH, "//button[contains(., 'Akzeptieren') or contains(., 'Zustimmen')]"),
        ]:
            try:
                btn = d.find_element(how, sel)
                if btn.is_displayed():
                    btn.click()
                    time.sleep(0.4)
                    break
            except Exception:
                pass
    except Exception:
        pass


########################### USA Ampel 4 Upgrade RSI+Fear ##################
def bewerte_ampel4_usa(rsi: float, fear: float):
    """
    Kombiniert RSI und CNN Fear&Greed für US-Indizes.
    Gibt Farbe ("green","orange","red","gray") und Kommentar-Text zurück.
    """

    import math

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

    if rsi is not None and math.isfinite(rsi) and fear_valid:
        # Kombinationsmatrix inkl. RSI_WARN–RSI_OVERBOUGHT Bereich
        if rsi < 30 and fear < 25:
            color, note = "green", "Extreme Angst + Überverkauft. Antizyklisch Long begünstigt."
        elif 30 <= rsi < RSI_WARN and fear < 25:
            color, note = "green", "Extreme Angst bei neutralem RSI. Pullback-Long nur mit Trendfilter."
        elif rsi < 30 and 25 <= fear <= 75:
            color, note = "green", "Überverkauft. Technischer Rebound möglich."
        elif 30 <= rsi < RSI_WARN and fear > 75:
            color, note = "orange", "Euphorie ohne Überkauft-Bestätigung. Rückschlagrisiko erhöht."
        elif RSI_WARN <= rsi < RSI_OVERBOUGHT and 25 <= fear <= 75:
            color, note = "orange", "RSI-Warnung bei neutralem Sentiment. Rückfallrisiko erhöht."
        elif RSI_WARN <= rsi < RSI_OVERBOUGHT and fear > 75:
            color, note = "orange", "RSI-Warnung + Gier. Rückschlagrisiko."
        elif RSI_WARN <= rsi < RSI_OVERBOUGHT and fear < 25:
            color, note = "gray", "Widerspruch: RSI-Warnung bei Angst. Kein klares Signal."
        elif rsi >= RSI_OVERBOUGHT and 25 <= fear <= 75:
            color, note = "orange", "Überkauft bei neutralem Sentiment. Gewinnsicherung ratsam."
        elif rsi >= RSI_OVERBOUGHT and fear > 75:
            color, note = "red", "Überkauft + Extreme Gier. Short-Setup begünstigt."
        elif rsi < 30 and fear > 75:
            color, note = "gray", "Widerspruch: Überverkauft bei extremer Gier. Kein Signal."
        elif rsi >= RSI_OVERBOUGHT and fear < 25:
            color, note = "gray", "Widerspruch: Überkauft bei extremer Angst. Kein Signal."
        else:
            color, note = "green", "Neutraler Bereich. Kein klares Signal."
    else:
        color, note = "gray", "Keine validen Werte. Ampel neutral."

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
    WebDriverWait(d, 15).until(EC.presence_of_element_located((By.TAG_NAME, "header")))
    time.sleep(1.0)
    soup = BeautifulSoup(d.page_source, "html.parser")
    text = soup.get_text(" ", strip=True)
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
    WebDriverWait(d, 15).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
    time.sleep(1.2)
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
            if m_pct: break
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
        "Nasdaq": "NASDAQ 100",
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



def get_vdax_change_finanztreff():
    """
    Sucht 'VDAX' auf der Startseite und zieht die nächste %-Zahl im selben Block/Text.
    Null-sicher, ohne .parent-Annäherung.
    """
    try:
        d = get_driver("general")
        d.get("https://www.finanztreff.de/")
        _ft_accept_cookies_quick(d)
        WebDriverWait(d, 15).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        time.sleep(1.0)
        html = d.page_source
        soup = BeautifulSoup(html, "html.parser")

        # Variante A: zuerst kompaktes Text-Matching
        text = soup.get_text(" ", strip=True)
        m = re.search(r"VDAX[^%]{0,120}?([+-]?\d+[.,]\d+)\s*%", text, flags=re.I)
        if m:
            val = float(_to_scalar(m.group(1).replace(",", ".")))
            print(f"✔️ VDAX (finanztreff/Text): {val:.2f} %")
            return val

        # Variante B: gezielte Suche in Elementen, ohne .parent-Ketten
        for node in soup.find_all(string=re.compile(r"\bVDAX\b", re.I)):
            block = node
            # suche im selben Container-Text eine Prozentzahl
            container = block.parent
            for _ in range(4):
                if not container: break
                txt = container.get_text(" ", strip=True)
                m2 = re.search(r"([+-]?\d+[.,]\d+)\s*%", txt)
                if m2:
                    val = float(_to_scalar(m2.group(1).replace(",", ".")))
                    print(f"✔️ VDAX (finanztreff/Block): {val:.2f} %")
                    return val
                container = container.parent
    except Exception as e:
        print(f"⚠️ VDAX finanztreff Fallback fehlgeschlagen: {e}")
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

def _safe_spread_pct(long_avg, short_avg):
    if long_avg is None or short_avg is None:
        return None
    if long_avg == 0.0:
        return None
    try:
        return (short_avg / long_avg - 1.0) * 100.0
    except Exception:
        return None

def update_data():
    global last_fetch_time

    while not stop_event.is_set():
        try:
            cu = get_selected_underlying()  # <- statt current_underlying
            urls = UNDERLYINGS.get(cu, {})
            if not urls:
                print(f"⚠️ Keine URLs für {cu}")
                time.sleep(refresh_interval)
                continue

            # --- Rohwerte holen ---
            long_avg_raw  = scrape_average_leverage(urls["long"])
            short_avg_raw = scrape_average_leverage(urls["short"])

            index_change_raw, index_display_value = (None, "-")
            idx = get_index_data(cu)
            if idx and len(idx) == 3:
                index_change_raw, index_display_value, _ = idx

            if index_change_raw is None:
                ft_change = get_index_change_from_finanztreff(cu)
                if ft_change is not None:
                    index_change_raw = ft_change

            vola_change_raw = get_volatility_change(cu)

            # --- 10%-Bestätigungsfilter ---
            long_avg     = LEVER_LONG_FILTER.update(long_avg_raw)
            short_avg    = LEVER_SHORT_FILTER.update(short_avg_raw)
            index_change = INDEX_FILTER.update(index_change_raw)
            vola_change  = VOL_FILTER.update(vola_change_raw)

            print(f"Volatility change for {cu}: {vola_change}")

            # --- Werte prüfen und CSV schreiben ---
            if None not in (long_avg, short_avg, index_change) and abs(index_change) < 10:
                timestamp = pd.Timestamp.now(tz=TZ_BERLIN)
                filename = get_csv_filename(cu)
                row = {
                    "timestamp": timestamp,
                    "long_avg": long_avg,
                    "short_avg": short_avg,
                    "index_change": index_change,
                    "index_display_value": index_display_value,
                    "volatility_change": vola_change,
                }

                df = pd.DataFrame([row])
                if os.path.exists(filename):
                    try:
                        old = pd.read_csv(filename)
                        if not old.empty:
                            df = pd.concat([old, df], ignore_index=True)
                    except Exception as e:
                        print(f"⚠️ Konnte alte CSV nicht lesen: {e}")

                try:
                    atomic_write_csv(df, filename)
                except Exception as e:
                    print(f"⚠️ Konnte CSV nicht schreiben: {e}")

                last_fetch_time = timestamp.strftime("%H:%M:%S")

        except Exception as e:
            print(f"⚠️ Fehler in update_data: {e}")

        time.sleep(refresh_interval)


def start_update_thread():
    global update_thread, stop_event
    stop_event.set()
    if update_thread is not None:
        update_thread.join(timeout=1)
    stop_event.clear()
    update_thread = threading.Thread(target=update_data, daemon=True)
    update_thread.start()
    time.sleep(1)

def get_vol_label(selected_underlying):
    return {"Dax":"VDAX","S&P 500":"VIX","EURO STOXX 50":"VSTOXX","Dow Jones":"VXD","Nasdaq":"VXN"}.get(selected_underlying,"Volatilität")

# -----------------------------------------------
# -----------------------------------------------
# Layout
# -----------------------------------------------
# Layout (v69) mit Bild am Ende + pointerEvents
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
        html.Span("v69", style={"fontSize": "16px", "color": "#666", "verticalAlign": "super"}),
        dcc.ConfirmDialog(id="confirm-exit", message="- Leverage Lens - beenden?")
    ], style={"textAlign": "center", "marginBottom": "20px"}),

    html.Div(
        dcc.Dropdown(
            id="underlying-dropdown",
            options=[{"label": k, "value": k} for k in UNDERLYINGS.keys()],
            value=selected_underlying,
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
            step=1,
            style={"width": "40px", "fontSize": "18px", "fontWeight": "bold", "textAlign": "center"}
        ),
        html.Button("Intervall ändern (Sek)", id="set-interval-btn", style={"marginLeft": "7px", "fontSize": "18px"}),
        html.Button("Alle CSV löschen", id="reset-btn", style={"marginLeft": "7px", "fontSize": "18px"})
    ], style={"margin": "15px 0"}),

    html.Div([
        dcc.Checklist(
            id="sound-toggle",
            options=[{"label": "🔔", "value": "on"}],
            value=["on"],
            inline=True,
            persistence=True,
            persistence_type="local",
            style={"fontSize": "18px"}
        )
    ], style={"marginTop": "10px", "textAlign": "left"}),

    html.Div(
        dcc.RadioItems(
            id="volatility-toggle",
            options=[],
            value="off",
            labelStyle={"display": "inline-block", "margin-right": "15px"},
            style={"fontSize": "18px", "padding": "6px 10px", "textAlign": "left"},
            inputStyle={"transform": "scale(1.4)", "marginRight": "8px"}
        ),
        style={"textAlign": "left", "margin": "10px 0"}
    ),

    html.Div(style={"height": "12px"}),

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
                    "width": "40px",   # hier die Breite
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
        "textAlign": "center", 
        "fontSize": "16px", 
        "color": "black", 
        "marginTop": "0px", 
        "fontStyle": "standard",
        #"backgroundColor": "#f0f0f0",
        "padding": "8px",
        "borderRadius": "6px",
        "maxWidth": "800px",
        "margin": "0 auto"
        }
    ),

    dcc.Graph(id="leverage-graph"),

    dcc.Interval(id="interval-component", interval=refresh_interval * 1000, n_intervals=0),
    dcc.Interval(id="atr-interval", interval=300000, n_intervals=0),
    html.Audio(id="alarm-audio", src="", autoPlay=True, controls=False, style={"display": "none"}),

    # Bild zuletzt, klick-durchlässig
    html.Img(
        src=app.get_asset_url("meinbild2.jpg"),
        style={
            "position": "absolute",
            "top": "30px",
            "right": "30px",
            "width": "auto",
            "height": "220px",
            "zIndex": "1",
            "pointerEvents": "none"
        }
    )
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


# Volatilitäts-Label
@app.callback(
    Output('volatility-toggle', 'options'),
    Input('underlying-dropdown', 'value')
)
def update_volatility_label(selected_underlying):
    vol_label = get_vol_label(selected_underlying)
    return [
        {'label': f'Volatilität einblenden: {vol_label}', 'value': 'on'},
        {'label': f'ausblenden', 'value': 'off'}
    ]
#####für Vola + Hebelempfehlung++++++++++++++
# Dann den Callback aktualisieren:
@app.callback(
    [Output("vola-strip", "children"),
     Output("vola-metrics", "children"),
     Output("vola-leverage", "children"),
     Output("vola-description", "children")],  # Neuer Output
    [Input("atr-interval", "n_intervals"),
     Input("underlying-dropdown", "value"),
     Input("base-leverage-input", "value")]
)
def update_vola_strip(_n, u, base_leverage):
    base = float(base_leverage if base_leverage is not None else BASE_LEVERAGE_DEFAULT)

    # 30T-Baseline (m) und Live-ATR5% EMA(3) (x)
    m = _get_baseline_m(u)
    x = _get_current_x(u)
    if not m or not x:
        return build_vola_strip("off", base, None), "", "", VOLA_DESCRIPTIONS["off"]

    # Cross-Index-Faktor auf Basis der 30T-Baselines
    avg_m = _mean_baseline_vola(exclude=None)   # optional: exclude=u
    if avg_m and avg_m > 0:
        k = avg_m / m                           # hochvolatile Indizes -> k<1
        base_star = np.clip(round((base * k) * 2) / 2.0, LEVER_MIN, LEVER_MAX)
    else:
        base_star = base

    # Kategorie nach live (x vs m), Empfehlung nutzt korrigierte Basis
    cat = _categorize(x, m)
    L = _recommend_leverage(x, m, base_star)

    strip = build_vola_strip(cat, base_star, L)
    description = VOLA_DESCRIPTIONS.get(cat, VOLA_DESCRIPTIONS["off"])
    
    return strip, "", "", description

#####ENDE für Vola + Hebelempfehlung++++++++++++++



# ---- Haupt-Callback inkl. Sound-Wert ----
@app.callback(
    Output('leverage-graph', 'figure'),
    Output('last-fetch-time', 'children'),
    Output('index-display', 'children'),
    Output('alarm-audio', 'src'),
    Input('interval-component', 'n_intervals'),
    Input('underlying-dropdown', 'value'),
    Input('volatility-toggle', 'value'),
    Input('sound-toggle', 'value'),   # <- wichtig
)
def update_graph(n, selected, volatility_toggle, sound_value):
    global selected_underlying, last_fetch_time, show_volatility, _last_alarm_state


    if selected != selected_underlying:
        selected_underlying = selected
        reset_drivers_on_underlying_change()  # ← NEU: Driver zurücksetzen    
        reset_jump_filters(selected)  
        scrape_average_leverage.cache_clear()
        start_update_thread()
    # Sound-Schalter übernehmen
    sound_on = bool(sound_value) and ("on" in sound_value)
    set_sound_enabled(sound_on)
    alarm_src = ""                      # default: kein Sound

    # Volatilitäts-Schalter übernehmen
    show_volatility = (volatility_toggle == 'on')

    # Index-Anzeige vorbereiten
    index_display_percentage = "N/A"
    index_display_color = "gray"
    index_change = None

    csv_file_display = get_csv_filename(selected)
    if os.path.exists(csv_file_display):
        df_tmp = pd.read_csv(csv_file_display, encoding='utf-8')
        if not df_tmp.empty:
            index_change = df_tmp['index_change'].iloc[-1]
            index_display_percentage = f"{index_change:.2f}%"
            index_display_color = "red" if index_change < 0 else ("green" if index_change > 0 else "gray")

    # Haupt-CSV laden
    csv_file = get_csv_filename(selected_underlying)
    lock = FILE_LOCKS[csv_file]
    with lock:
        if os.path.exists(csv_file):
                df = pd.read_csv(csv_file, parse_dates=['timestamp'], encoding='utf-8')
        else:
                df = pd.DataFrame(columns=["timestamp","long_avg","short_avg","index_change","volatility_change"])


    try:
        if os.path.exists(csv_file):
            df = pd.read_csv(csv_file, parse_dates=['timestamp'], encoding='utf-8')
            for col in ['long_avg', 'short_avg', 'index_change']:
                if col not in df.columns:
                    df[col] = None
            df = df.ffill().fillna(0)
            if 'volatility_change' in df.columns:
                df['volatility_change'] = df['volatility_change'].ffill().bfill()
        else:
            empty = pd.DataFrame(columns=["timestamp", "long_avg", "short_avg", "index_change"])
            atomic_write_csv(empty, csv_file)   # statt: file
    except Exception as e:
        print(f"Fehler beim Lesen der CSV: {e}")
        df = pd.DataFrame()

    # Plot
    fig = go.Figure()
    if not df.empty and len(df) > 1:
        fig.add_trace(go.Scatter(x=df['timestamp'], y=df['long_avg'], mode='lines+markers', name='Long Hebel',
                                 line=dict(color='green', width=2), marker=dict(size=8), opacity=0.8))
        fig.add_trace(go.Scatter(x=df['timestamp'], y=df['short_avg'], mode='lines+markers', name='Short Hebel',
                                 line=dict(color='red', width=2), marker=dict(size=8), opacity=0.8))
        fig.add_trace(go.Scatter(x=df['timestamp'], y=df['index_change'], mode='lines', name='Index Veränderung (%)',
                                 line=dict(color='blue', width=3), marker=dict(size=6), yaxis='y2',
                                 hovertemplate="%{x|%H:%M:%S}<br>%{y:.2f}%<extra></extra>"))
        if show_volatility and 'volatility_change' in df.columns and df['volatility_change'].notna().any():
            fig.add_trace(go.Scatter(x=df['timestamp'], y=df['volatility_change'], mode='lines',
                                     name=get_vol_label(selected), line=dict(color='blue', width=3, dash='dot'),
                                     yaxis='y2', hovertemplate="%{x|%H:%M:%S}<br>%{y:.2f}%<extra></extra>"))
        y2_series = df['index_change']
        if show_volatility and 'volatility_change' in df.columns:
            y2_series = pd.concat([y2_series, df['volatility_change']], axis=0)
        min_val = float(_to_scalar(y2_series.min())); max_val = float(_to_scalar(y2_series.max()))
        span = max_val - min_val; min_range = 1.0; padding = 0.1
        if span < min_range:
            center = (min_val + max_val) / 2.0
            y2_range = [center - min_range / 2.0 - padding, center + min_range / 2.0 + padding]
        else:
            y2_range = [min_val - padding, max_val + padding]
        fig.update_layout(
            title={'text': f"Leverage Lens – {selected_underlying} : Ø Hebel & Marktbewegung",
                   'y': 0.95, 'x': 0.5, 'xanchor': 'center', 'yanchor': 'top',
                   'font': {'size': 18, 'weight': 'bold', "color": "black"}},  # Hier wurde 'font' hinzugefügt
            xaxis=dict(
                title=dict(text='Zeit', font=dict(color='black', size=18)),
                tickfont=dict(color='black', size=14),
                linecolor='black',
                showline=True
            ),
            yaxis=dict(
                title=dict(text='Durchschnittlicher Hebel', font=dict(color='black', size=16)),
                side='left',
                showgrid=True,
                tickfont=dict(color='black', size=14),
                linecolor='black',
                showline=True
            ),
            yaxis2=dict(
                title=dict(text="Index / Vola (%)", font=dict(color='blue', size=16)),
                overlaying='y',
                side='right',
                showgrid=False,
                range=y2_range,
                tickfont=dict(color='blue', size=14),
                linecolor='black',
                showline=True
            ),
            legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="right", x=1),
            margin=dict(l=50, r=50, b=50, t=80, pad=4),
            height=500,
            plot_bgcolor='rgba(200,200,200,0.8)'
        )

    else:
        now = datetime.now(TZ_BERLIN)
        placeholder_text = "Warte auf ausreichende Daten..." if len(df) == 1 else "Warte auf erste Daten..."
        fig.add_annotation(text=placeholder_text, xref="paper", yref="paper", x=0.5, y=0.5, showarrow=False, font=dict(size=12, color="gray"))
        fig.add_trace(go.Scatter(x=[now - timedelta(minutes=5), now], y=[0, 50], mode='lines', line=dict(width=0), showlegend=False, hoverinfo='none'))

    # Ampel 3
    alle_ereignisse = lade_oder_erstelle_ereignisse()
    ampel3_color, ampel3_text = bewerte_ampel_3(alle_ereignisse, selected_underlying)

    # Signale
    try:
        rel_pos, ampel3_signal, hebel_signal, datenpunkt_info, _, tagesverlauf = determine_ampel_signal(df)
        if len(df) >= 10:
            ampel1_color, ampel1_relpos, ampel1_text_local = get_ampel1_status(df, selected_underlying)
        else:
            ampel1_text_local = "Warte auf ausreichende Daten für Analyse (min. 20 Datenpunkte)"; ampel1_color = FARBCODES["gray"]
        if "🟢" in hebel_signal or "Positiv:" in hebel_signal:
            ampel2_color = FARBCODES["green"]
        elif "🔴" in hebel_signal or "Alarm:" in hebel_signal:
            ampel2_color = FARBCODES["red"]
        else:
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
            res = get_sofr_proxy_comment()
            if isinstance(res, tuple) and len(res) == 2:
                sofr_bps, sofr_text = res
    # Miniampel/Farbe
            if abs(sofr_bps) >= RSI_OVERBOUGHT:
                sofr_mini_color = FARBCODES["red"];   sofr_mini_emoji = "🔴"
            elif abs(sofr_bps) >= 40:
                sofr_mini_color = FARBCODES["orange"];sofr_mini_emoji = "🟠"
            else:
                sofr_mini_color = FARBCODES["green"]; sofr_mini_emoji = "🟢"

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

            
        else:
    # Your existing SOFR processing logic
           if abs(sofr_bps) > 100:
               sofr_text = "Extrem (Systemkrise): >100 bps – Historisch nur in Krisen (2007–2008 bis 465 bps, Corona 2020 ca. 140 bps). Signal: akute Banken-/Fundingkrise"
               sofr_mini_color = FARBCODES["red"]
               sofr_mini_emoji = "🔴"
           elif abs(sofr_bps) >= RSI_OVERBOUGHT:
               sofr_text = "Kritisch (Liquiditätsstress): RSI_OVERBOUGHT–100 bps – Banken leihen zögerlich. Meist Vorbote stärkerer Abverkäufe."
               sofr_mini_color = FARBCODES["red"]
               sofr_mini_emoji = "🔴"
           elif abs(sofr_bps) >= 40:
               sofr_text = "Erhöht (Markt wird nervös): 40–RSI_OVERBOUGHT bps – Leichte Spannungen im Interbankmarkt. Frühwarnsignal für knapper werdende Liquidität."
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
        amp2_rot = (ampel2_color == FARBCODES["red"])
        current_state = (amp1_rot, amp2_rot)
        if current_state != _last_alarm_state:
            ts = f"{time.time():.3f}"
            if sound_on:
                if amp1_rot and amp2_rot:
                    alarm_src = f'{app.get_asset_url("Alarm2.wav")}?ts={ts}'
                elif amp1_rot or amp2_rot:
                    alarm_src = f'{app.get_asset_url("Alarm1.wav")}?ts={ts}'
            _last_alarm_state = current_state

    except Exception as e:
        print(f"Fehler bei Signalberechnung: {e}")
        ampel3_signal = "System initialisiert"; hebel_signal = "Warte auf Daten"; datenpunkt_info = "Initialisierung läuft"
        tagesverlauf = "-"; ampel3_color = FARBCODES["gray"]; ampel1_color = FARBCODES["gray"]; ampel2_color = FARBCODES["gray"]; ampel1_text_local = ampel1_text

    # RSI / Ampel 4 / USA
# --- Ampel 4: RSI + (für USA) Fear & Greed ---
    rsi_ticker = get_rsi_for_underlying(selected)
    rsi_value  = get_rsi(rsi_ticker) if rsi_ticker else None

    if selected in ("S&P 500", "Dow Jones", "Nasdaq"):
        fear = get_fng_today(force_refresh=True)  # Cache: heute; sonst live; Datei data/fear_greed_us.csv
        color, line = bewerte_ampel4_usa(
            float(_to_scalar(rsi_value)) if rsi_value is not None else float("nan"),
            float(_to_scalar(fear)) if fear is not None else float("nan")
        )
        ampel4_color = FARBCODES[color]            # "green/orange/red/gray" → Hex
        ampel4_title = "Ampel 4: RSI (8) + Fear & Greed"
        ampel4_text  = line
    else:
    # DAX/EURO STOXX wie bisher nur RSI
        rsi_status, rsi_title, rsi_text = bewerte_rsi_ampel(rsi_value)
        # Miniampel-Emoji für RSI (nur Non-US)
        if rsi_value is None:
            rsi_emoji = "⚪"
        elif rsi_value >= RSI_OVERBOUGHT:
            rsi_emoji = "🔴"
        elif rsi_value >= RSI_WARN:
            rsi_emoji = "🟠"
        else:
            rsi_emoji = "🟢"


        ampel4_color = rsi_status
        ampel4_title = f"Ampel 4: {rsi_title} (8 Tage)"
        ampel4_text  = f"{rsi_emoji} {rsi_text}"
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


    
    return (
        fig,
        f"Letzte Abfrage: {last_fetch_time}",
        html.Div([
            html.Div([
                html.Span(f"Index aktuell: {index_display_percentage}", style={"color": index_display_color,"fontWeight": "bold","fontSize": "25px","marginRight": "12px"}),
                html.Span(is_market_open(selected), style={"fontSize": "18px","color": "#444"})
            ], style={"display": "flex","alignItems": "center"}),
            html.Br(),
            news_or_info_block,
            html.Div([
                html.Div(style={"width": "35px","height": "35px","borderRadius": "50%","backgroundColor": ampel1_color,"display": "inline-block","marginRight": "15px","marginTop": "4px","boxShadow": "0 0 8px 2px rgba(255, 255, 255, 0.5)","border": "2px solid #666","boxSizing": "border-box"}),
                html.Div([
                    html.Div(f"Ampel 1: Volatilitäts-Index (sofort)", style={"fontSize": "100%","fontWeight": "bold"}),
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
                    html.Div([html.Span(line) if i == 0 else html.Br() + html.Span(line) for i, line in enumerate(ampel3_text.splitlines())], style={"marginLeft": "40px","fontSize": "90%","color": "#333"})
                ])
            ], style={"display": "flex","alignItems": "flex-start","marginBottom": "20px"}),
            html.Div([
                html.Div(style={"width": "35px","height": "35px","borderRadius": "50%","backgroundColor": ampel4_color,"display": "inline-block","marginRight": "15px","marginTop": "4px","boxShadow": "0 0 8px 2px rgba(255, 255, 255, 0.5)","border": "2px solid #666","boxSizing": "border-box"}),
                html.Div([
                    html.Div(f"{ampel4_title}", style={"fontSize": "100%","fontWeight": "bold"}),
                    html.Div("Erkennt: RSI-Überkauft/-verkauft; in USA zusätzlich CNN Fear & Greed", style={"marginLeft": "15px","fontSize": "90%","color": "#333"}),
                    html.Div([
                        html.Br(),
                       #html.Span("Kommentar: ", style={"display": "block"}),
                        html.Span(ampel4_text.replace('<br>', '\n'), 
                                 style={"display": "block", "marginLeft": "0px", "fontSize": "90%", "color": "#333", "whiteSpace": "pre-line"})
                    ], style={"marginLeft": "40px"})
                ])
            ], style={"display": "flex","alignItems": "flex-start","marginBottom": "20px"}),
        ]),
        alarm_src
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
    Input("reset-btn", "n_clicks"),
    prevent_initial_call=True
)
def reset_csv_files(n_clicks):
    for u in UNDERLYINGS.keys():
        file = get_csv_filename(u)
        if os.path.exists(file):
            os.remove(file)
        empty = pd.DataFrame(columns=["timestamp","long_avg","short_avg","index_change"])
        atomic_write_csv(empty, file)
    # Logs optional lassen wie sie sind
    for fname in ["log_ampel.csv", "log_index.csv"]:
        path = os.path.join(CSV_FOLDER, fname)
        if os.path.exists(path):
            os.remove(path)
    return 0



def cleanup():
    global _DRIVER_POOL, _TMP_PROFILE_DIR
    # Beende beide Driver im Pool
    for use_case, driver in _DRIVER_POOL.items():
        if driver is not None:
            try:
                driver.quit()
                print(f"✅ Driver für '{use_case}' geschlossen.")
            except Exception as e:
                print(f"⚠️ Fehler beim Schließen des Drivers für '{use_case}': {e}")
            _DRIVER_POOL[use_case] = None

    # Alte Temp-Verzeichnis Bereinigung (falls vorhanden)
    if _TMP_PROFILE_DIR and os.path.exists(_TMP_PROFILE_DIR):
        try:
            shutil.rmtree(_TMP_PROFILE_DIR)
        except:
            pass

import webbrowser, threading

# Erst beim Klick den Dialog öffnen
@app.callback(
    Output("confirm-exit", "displayed"),
    Input("exit-title", "n_clicks"),
    prevent_initial_call=True
)
def show_confirm(n_clicks):
    return True  # Dialog anzeigen


# Reagiere auf Bestätigung
@app.callback(
    Output("exit-title", "children"),  # Dummy Output
    Input("confirm-exit", "submit_n_clicks"),
    prevent_initial_call=True
)
def close_app(n_clicks_submit):
    if n_clicks_submit:
        os._exit(0)
    return "Leverage Lens"  # unverändert

import atexit
from contextlib import suppress

def shutdown_all_drivers():
    """Beendet alle noch laufenden WebDriver-Instanzen und Chrome-Prozesse."""
    global DRIVERS, _DRIVER_POOL, _DRIVERS, _SERVICES, _SERVICE_PIDS
    
    # Beende alle Driver im DRIVERS-Dictionary
    for key, drv in list(DRIVERS.items()):
        try:
            drv.quit()
            print(f"✅ Driver '{key}' geschlossen.")
        except Exception as e:
            print(f"⚠️ Fehler beim Schließen des Drivers '{key}': {e}")
        finally:
            DRIVERS.pop(key, None)
    
    # Beende alle Driver im _DRIVER_POOL
    for use_case, driver in list(_DRIVER_POOL.items()):
        if driver is not None:
            try:
                driver.quit()
                print(f"✅ Driver für '{use_case}' geschlossen.")
            except Exception as e:
                print(f"⚠️ Fehler beim Schließen des Drivers für '{use_case}': {e}")
            finally:
                _DRIVER_POOL[use_case] = None
    
    # Beende alle globalen Driver
    for drv in list(_DRIVERS):
        try:
            drv.quit()
        except Exception:
            pass
        finally:
            if drv in _DRIVERS:
                _DRIVERS.remove(drv)
    
    # Beende Services
    for service in list(_SERVICES):
        try:
            service.stop()
        except Exception:
            pass
        finally:
            if service in _SERVICES:
                _SERVICES.remove(service)
    
    # Beende Prozesse anhand ihrer PIDs
    for pid in list(_SERVICE_PIDS):
        try:
            if psutil:
                proc = psutil.Process(pid)
                proc.terminate()
                proc.wait(timeout=5)
        except Exception:
            pass
        finally:
            if pid in _SERVICE_PIDS:
                _SERVICE_PIDS.remove(pid)
    
    # Windows-Fallback: Chrome-Prozesse hart beenden
    if platform.system() == "Windows":
        try:
            subprocess.run(["taskkill", "/F", "/IM", "chromedriver.exe", "/T"], 
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)
            subprocess.run(["taskkill", "/F", "/IM", "chrome.exe", "/T"], 
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)
        except Exception:
            pass
    
    # Temporäre Profile bereinigen
    global _TMP_PROFILE_DIR
    if _TMP_PROFILE_DIR and os.path.exists(_TMP_PROFILE_DIR):
        try:
            shutil.rmtree(_TMP_PROFILE_DIR, ignore_errors=True)
        except Exception:
            pass
        _TMP_PROFILE_DIR = None
    
    print("✅ Alle Chrome-Prozesse bereinigt.")

atexit.register(shutdown_all_drivers)




if __name__ == "__main__":
    try:
        start_update_thread()
        threading.Timer(0.8, lambda: webbrowser.open("http://127.0.0.1:8050")).start()
        
        # App starten
        app.run(debug=False, host="127.0.0.1", port=8050, use_reloader=False)
        
    except OSError as e:
        if "Address already in use" in str(e):
            print(f"Port 8050 is already in use. Trying port 8051...")
            app.run(debug=False, host="127.0.0.1", port=8051, use_reloader=False)
        else:
            raise e
    except Exception as e:
        print(f"Unerwarteter Fehler: {e}")
    finally:
        # Sicherstellen, dass alle Ressourcen bereinigt werden
        shutdown_all_drivers()
