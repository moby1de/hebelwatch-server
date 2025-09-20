# Hebelwatch Markus Jurina (markus@jurina.biz) 20.09.2025 v78 
# Schriftart im Projekt, gleich für alle#
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
from dash import html
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
import statistics
from collections import deque, defaultdict
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
_RSI_CACHE_TTL = 60 #sekunden
_last_csv_write = {"ts": 0}

from collections import defaultdict

_LEVER_CACHE = defaultdict(lambda: {"long": None, "short": None, "ts": 0})
_LEVER_TTL = 30  # Sekunden: Hebel gelten so lange als “frisch”
_lever_thread = None


################Browser blocken/Last reuduzieren
BLOCK_URLS_DEFAULT = [
    "*.png","*.jpg","*.jpeg","*.gif","*.webp","*.svg","*.ico",
    "*.css","*.woff*","*.ttf","*.otf",
    "*doubleclick*","*googletag*","*analytics*"
]

def _enable_cdp_blocking(driver, block_patterns=None):
    try:
        driver.execute_cdp_cmd("Network.enable", {})
        driver.execute_cdp_cmd("Network.setBlockedURLs", {
            "urls": block_patterns or BLOCK_URLS_DEFAULT
        })
    except Exception:
        pass

def _new_chrome(headless=True, block_patterns=None):
    opts = webdriver.ChromeOptions()
    if headless:
        opts.add_argument("--headless=new")
    opts.add_argument("--no-sandbox")
    opts.add_argument("--disable-dev-shm-usage")
    opts.add_argument("--disable-gpu")
    opts.add_argument("--lang=de-DE,de")
    opts.add_experimental_option('excludeSwitches', ['enable-logging', 'enable-automation'])
    opts.add_experimental_option('useAutomationExtension', False)

    # Kritisch: PageLoadStrategy = none
    opts.set_capability("pageLoadStrategy", "none")

    service = Service(ChromeDriverManager().install())
    drv = webdriver.Chrome(service=service, options=opts)

    # Ressourcen blocken (JS NICHT blocken!)
    _enable_cdp_blocking(drv, block_patterns)

    # Tracking für späteres Cleanup
    _DRIVERS.append(drv)
    _SERVICES.append(service)
    try:
        if getattr(service, "process", None):
            _SERVICE_PIDS.append(service.process.pid)
    except:
        pass

    return drv


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
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC

def close_onvista_popups(driver, timeout=4):
    wait = WebDriverWait(driver, timeout)

    # 1) Cookie/Consent (häufig Sourcepoint-iframe)
    try:
        # in iframe wechseln, Button klicken, zurück
        iframe = wait.until(EC.presence_of_element_located(
            (By.CSS_SELECTOR, "iframe[id^='sp_message_iframe']")))
        driver.switch_to.frame(iframe)
        for xp in [
            "//button[contains(., 'Zustimmen')]",
            "//button[contains(., 'Akzeptieren')]",
            "//button[contains(., 'Einverstanden')]",
            "//button[contains(., 'Alle akzeptieren')]",
            "//button[contains(., 'Ich stimme zu')]",
        ]:
            btns = driver.find_elements(By.XPATH, xp)
            if btns:
                btns[0].click()
                break
    except Exception:
        pass
    finally:
        try:
            driver.switch_to.default_content()
        except Exception:
            pass

    # 2) „Frischer Look“-Tour (Overlay/Modal)
    try:
        # Schließen-Buttons nach Text
        for xp in [
            "//button[contains(., 'nicht mehr anzeigen')]",
            "//button[contains(., 'Später')]",
            "//button[contains(., 'Schließen')]",
            "//div[@role='dialog']//button[.//span[contains(text(),'Später')]]",
            "//div[@role='dialog']//button[@aria-label='Schließen']",
        ]:
            btns = driver.find_elements(By.XPATH, xp)
            if btns:
                btns[0].click()
                break
        # Fallback: X-Icon
        if driver.find_elements(By.CSS_SELECTOR, "div[role='dialog'] button[aria-label='Schließen'], div[role='dialog'] svg"):
            driver.find_element(By.CSS_SELECTOR, "div[role='dialog'] button, div[role='dialog'] .close, div[role='dialog'] [aria-label='Schließen']").click()
    except Exception:
        pass

    # 3) OneTrust-Variante (falls Onvista umschaltet)
    try:
        btn = driver.find_element(By.ID, "onetrust-accept-btn-handler")
        btn.click()
    except Exception:
        pass

    # 4) Didomi-Variante
    try:
        for sel in [
            "#didomi-notice-agree-button",
            "button.didomi-components-button--color",
        ]:
            btns = driver.find_elements(By.CSS_SELECTOR, sel)
            if btns:
                btns[0].click()
                break
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

def on_program_start():
    """Diese Funktion wird beim Programmstart aufgerufen."""
    underlying = "DAX"  # Beispiel: Setze das Standard-Underlying (oder wähle es dynamisch)
    reset_cache_on_start_or_underlying_change(underlying)
    print("Programm gestartet und Cache initialisiert.")

def on_underlying_change(new_underlying: str):
    """Diese Funktion wird aufgerufen, wenn das Underlying gewechselt wird."""
    reset_cache_on_start_or_underlying_change(new_underlying)
    print(f"Underlying gewechselt zu {new_underlying} und Cache aktualisiert.")

def get_atr_value(underlying: str, cache_duration: int = 60 * 60 * 24):
    """Abruf der ATR-Daten aus dem Cache, falls diese noch gültig sind."""
    now = time.time()

    # Überprüfen, ob der Cache für das Underlying gültig ist
    if underlying in _ATR_CACHE_BASE:
        cache_entry = _ATR_CACHE_BASE[underlying]
        if now - cache_entry["ts"] < cache_duration:
            return cache_entry["m"]
    
    # Wenn Cache nicht gültig oder nicht vorhanden ist, dann neu berechnen
    return _get_baseline_m(underlying)




# --- Finanzen.net: schnelle %-Änderung (Requests, kein Selenium) ---
_FINANZEN_CACHE = {}  # {key: (ts, value)}

def _finanzen_pct(url: str, key: str, ttl: int = 5) -> float | None:
    try:
        import time, requests, re
        from bs4 import BeautifulSoup
        ts, val = _FINANZEN_CACHE.get(key, (0, None))
        if time.time() - ts < ttl and val is not None:
            return val
        headers = {"User-Agent": "Mozilla/5.0"}
        html = requests.get(url, headers=headers, timeout=4).text
        soup = BeautifulSoup(html, "html.parser")
        text = soup.get_text(" ", strip=True)
        m = re.search(r"([+-]?\d+[.,]\d+)\s?%", text)
        if not m: 
            return None
        val = float(m.group(1).replace(",", "."))
        _FINANZEN_CACHE[key] = (time.time(), val)
        return val
    except Exception:
        return None

def get_nasdaq_change_finanzen() -> float | None:
    # NASDAQ-100 auf finanzen.net
    url = "https://www.finanzen.net/index/nasdaq_100"
    return _finanzen_pct(url, key="ndx_fz")
    
    
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



def get_driver(*args, headless=True):
    """Gibt einen funktionsfähigen Chrome-WebDriver zurück und trackt ihn in _DRIVERS/_SERVICES."""
    if SHUTTING_DOWN:
        raise RuntimeError("Shutdown in progress")

    # Vorhandenen Driver wiederverwenden
    for d in list(_DRIVERS):
        try:
            _ = d.title  # wirft Exception, wenn Prozess tot ist
            return d
        except Exception:
            pass

    # Neu erstellen und REGISTRIEREN
    try:
        # Optionen
        try:
            opts = _make_chrome_options()
            if not headless:
                # Headless-Flag entfernen, falls über _make_chrome_options gesetzt
                opts.arguments = [a for a in getattr(opts, "arguments", []) if "headless" not in a]
        except Exception:
            # Fallback ohne _make_chrome_options
            opts = webdriver.ChromeOptions()
            if headless:
                opts.add_argument("--headless=new")
            opts.add_argument("--no-sandbox")
            opts.add_argument("--disable-dev-shm-usage")
            opts.add_argument("--disable-gpu")
            opts.add_experimental_option('excludeSwitches', ['enable-logging','enable-automation'])
            opts.add_experimental_option('useAutomationExtension', False)

        service = Service(ChromeDriverManager().install())
        drv = webdriver.Chrome(service=service, options=opts)
        _enable_cdp_blocking(drv)

        _DRIVERS.append(drv)
        _SERVICES.append(service)
        try:
            if getattr(service, "process", None):
                _SERVICE_PIDS.append(service.process.pid)
        except Exception:
            pass

        return drv
    except Exception as e:
        raise RuntimeError(f"Chrome WebDriver start failed: {e}")



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
    _cleanup()
    sys.exit(0)

#ampel 1 statt pfeile die man schlecht sieht, farbig
def build_dir_badges(idx_pct, vola_pct, underlying=None):
    import dash.html as html
    if underlying is None:
        try:
            underlying = get_selected_underlying()
        except Exception:
            underlying = "Index"
    vola_name = _vola_name(underlying)

    def chip(label, up=None):
        base = {
            "display":"inline-flex","alignItems":"center","gap":"6px",
            "padding":"2px 8px","borderRadius":"8px","border":"1px solid",
            "fontWeight":"600","fontSize":"90%"
        }
        if up is True:
            base.update({"background":"#e6f5ec","borderColor":"#0f7b3b","color":"#0f7b3b"})
        elif up is False:
            base.update({"background":"#fdeaea","borderColor":"#b42318","color":"#b42318"})
        else:
            base.update({"background":"#eee","borderColor":"#999","color":"#444"})
        return html.Span(label, style=base)

    parts = []
    if idx_pct is not None:
        parts.append(
            chip(f"{underlying} {'↑↑' if idx_pct>0 else '↓↓' if idx_pct<0 else '→'}",
                 True if idx_pct>0 else False if idx_pct<0 else None)
        )
    if vola_pct is not None:
        parts.append(
            chip(f"{vola_name} {'↑↑' if vola_pct>0 else '↓↓' if vola_pct<0 else '→'}",
                 True if vola_pct>0 else False if vola_pct<0 else None)
        )
    return parts





# Signale registrieren
def _register_signals():
    import threading
    if threading.current_thread() is threading.main_thread():
        for s in (getattr(signal, "SIGINT", None),
                  getattr(signal, "SIGTERM", None),
                  getattr(signal, "SIGBREAK", None)):
            if s:
                signal.signal(s, _signal_handler)





TZ_BERLIN = pytz.timezone("Europe/Berlin")


# für Ampel 2 erweiterung########

# --- SOFR-Proxy (TED ersatz) --------------------------------------------------
FRED_API_KEY = "ac24c6331bbe4bd92e5cc0ce443d4d2e"
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

def find_text_retry(driver, locator: tuple[str, str], wait_s=10, retries=3):
    for _ in range(retries):
        try:
            el = WebDriverWait(driver, wait_s).until(EC.visibility_of_element_located(locator))
            return el.text
        except StaleElementReferenceException:
            continue
    raise TimeoutException("stale after retries")

# ---- oben (globals) Filter Linien ----
_TOP10_LAST = {"val": None, "ts": 0}
_TOP10_EMA = None
_TOP10_ALPHA = 0.7           # Glättung 0..1
_TOP10_MIN_VALID = 3         # mind. 7/10 Werte nötig
_TOP10_MAX_JUMP = 0.50       # max. 12% Sprung vs. letztem Wert

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

def get_top10_eq_change_pct(underlying: str) -> float | None:
    """Stabiler gleichgewichteter Top-10-Mittelwert, mit Min-Count, EMA und Jump-Clamp."""
    tickers = _get_top10_tickers(underlying)
    symbols = [_yf_symbol(t) for t in tickers]

    vals = _yf_multi_intraday_vs_prevclose(symbols).values()
    vals = [float(v) for v in vals if v is not None and math.isfinite(v)]

    if len(vals) < _TOP10_MIN_VALID:
        return _TOP10_LAST["val"]

    med = float(np.median(vals))
    iqr = np.subtract(*np.percentile(vals, [75, 25]))
    lo, hi = med - 3*iqr, med + 3*iqr
    clipped = [min(hi, max(lo, v)) for v in vals]
    mean_now = float(np.mean(clipped))

    prev = _TOP10_LAST["val"]
    if prev is not None:
        base = max(1e-9, abs(prev))
        rel = abs(mean_now - prev) / base
        if rel > _TOP10_MAX_JUMP:
            mean_now = prev + math.copysign(base * _TOP10_MAX_JUMP, mean_now - prev)

    global _TOP10_EMA
    if _TOP10_EMA is None:
        _TOP10_EMA = mean_now
    else:
        _TOP10_EMA = _TOP10_ALPHA * mean_now + (1 - _TOP10_ALPHA) * _TOP10_EMA

    _TOP10_LAST.update({"val": _TOP10_EMA, "ts": time.time()})
    return _TOP10_EMA


def get_sofr_proxy_comment(cache_sec=900):
    """Gibt (bps:int, text:str). Cacht für cache_sec Sekunden."""
    import time
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

# Manuelles Cache-Reset falls benötigt
def reset_sofr_cache():
    """Setzt den SOFR-Cache zurück"""
    global _SOFR_CACHE
    _SOFR_CACHE = {"ts": 0, "bps": None, "text": "SOFR-Proxy: keine Daten."}
##################################################################################################
def scrape_onvista_leverage(current_underlying: str) -> tuple[list[float], list[float]]:
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
            d.get(UNDERLYINGS[current_underlying]["long"] + f"&t={int(time.time())}")
            _wait_body_present(d, timeout_s=2.0)
            with suppress(Exception):
                close_onvista_popups(d, timeout=3)
            t = _read_table_text(2.0)
            long_vals = _parse_leverage_numbers(t) if t else []
        except Exception:
            pass

        # SHORT
        try:
            d.get(UNDERLYINGS[current_underlying]["short"] + f"&t={int(time.time())}")
            _wait_body_present(d, timeout_s=2.0)
            with suppress(Exception):
                close_onvista_popups(d, timeout=3)
            t = _read_table_text(2.0)
            short_vals = _parse_leverage_numbers(t) if t else []
        except Exception:
            pass

        return long_vals, short_vals




def switch_underlying(new_underlying: str):
    global selected_underlying, stop_event, _volatility_cache

    # A) laufenden Loop sauber stoppen
    stop_update_thread(timeout=5)

    # B) alte Driver schließen
    reset_drivers_on_underlying_change(old_underlying=selected_underlying)

    # Fix für EURO STOXX 50: 'general'-Driver explizit freigeben
    if selected_underlying == "EURO STOXX 50":
        from contextlib import suppress
        with suppress(Exception):
            drv = _DRIVER_POOL.pop("general", None)
            if drv: drv.quit()
        with suppress(Exception):
            key = f"general_{selected_underlying}"
            drv2 = _DRIVER_POOL.pop(key, None)
            if drv2: drv2.quit()

    # C) globalen Zustand setzen
    set_selected_underlying(new_underlying)
    reset_jump_filters(new_underlying)
    for k in list(_volatility_cache.keys()):
        _volatility_cache[k] = {"value": None, "ts": 0}

    # D) Caches leeren
    from contextlib import suppress
    with suppress(Exception):
        scrape_average_leverage.cache_clear()

    # E) neu starten
    if stop_event:
        stop_event.clear()
    start_update_thread()
    start_leverage_thread()
    





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


def get_vstoxx_change_stock3(driver=None, timeout=10, retries=3):
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
    
def get_vstoxx_change_onvista(timeout=12):
    """
    VSTOXX %-Änderung von onvista.de robust auslesen.
    Versucht mehrere Selektoren und fällt auf beliebigen %-Text zurück.
    """
    try:
        d = get_driver("general", KEY_GLOBAL)
        d.get("https://www.onvista.de/index/VSTOXX-Volatilitaetsindex-Index-12105800")
        close_onvista_popups(d, timeout=6)
        WebDriverWait(d, timeout).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        time.sleep(1.2)

        # 1) Primär: <data ... class="text-... whitespace-nowrap ml-4" value="...">
        for how, sel in [
            (By.CSS_SELECTOR, "data.text-positive.whitespace-nowrap.ml-4"),
            (By.CSS_SELECTOR, "data.text-negative.whitespace-nowrap.ml-4"),
            # 2) Generischer: irgendein <data value="..."> im Kontext
            (By.XPATH, "(//data[@value])[1]"),
            # 3) Fallback: erster sichtbarer Textknoten mit '%'
            (By.XPATH, "(//*[contains(normalize-space(text()), '%')])[1]"),
        ]:
            try:
                el = d.find_element(how, sel)
                raw = (el.get_attribute("value") or el.text or "").strip()
                val = _parse_german_percent(raw) or _extract_percent(raw)
                if val is not None:
                    return round(float(val), 2)
            except Exception:
                pass

        # 4) Nichts gefunden
        return None
    except Exception as e:
        print(f"⚠️ OnVista VSTOXX Fehler: {e}")
        return None


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
LEVER_MIN, LEVER_MAX = 5.0, 30.0
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
    "Nasdaq": "^NDX",
}


VOLA_DESCRIPTIONS = {
    "very_low": html.Span([
        html.Span("Ampel 5:", style={"fontWeight": "bold"}),
        " Volatilität unter 60% des Medians → Handel nicht empfohlen"
    ]),
    "low": html.Span([
        html.Span("Ampel 5:", style={"fontWeight": "bold"}),
        " 60-90% des Medians → unterdurchschn. Volatilität; Es empfiehlt sich einen anderen Index anzuschauen"
    ]),
    "normal": html.Span([
        html.Span("Ampel 5:", style={"fontWeight": "bold"}),
        " 90-110% des Medians → typische Marktvolatilität"
    ]),
    "elevated": html.Span([
        html.Span("Ampel 5:", style={"fontWeight": "bold"}),
        " 110-150% des Medians → erhöhte Volatilität; Chancen steigen, Hebel prüfen"
    ]),
    "very_high": html.Span([
        html.Span("Ampel 5:", style={"fontWeight": "bold"}),
        " über 150% des Medians → extreme Volatilität, Hebel anpassen und News prüfen"
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
    out = df.between_time(start, end)
    return out if not out.empty else df


def _atr5pct(df: "pd.DataFrame"):
    if df.empty: return pd.Series(dtype=float)
    o,h,l,c = df["Open"], df["High"], df["Low"], df["Close"]
    prev_c  = c.shift(1)
    tr = np.maximum(h-l, np.maximum((h - prev_c).abs(), (l - prev_c).abs()))
    atr = tr.ewm(span=14, adjust=False).mean()
    atr_pct = (atr / c) * 100.0
    return atr_pct
    
INDEX_POOL = ["Dax","EURO STOXX 50","S&P 500","Dow Jones","Nasdaq"]
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



def _get_baseline_m(underlying: str) -> float | None:
    now = time.time()
    ent = _ATR_CACHE_BASE.get(underlying, {})
    if ent and now - ent.get("ts", 0) < 1800:
        return ent.get("m")
    sym = YF_SYMBOL.get(underlying)
    if not sym: 
        return None
    df = _yf_5m(sym, period=f"{ATR_BASE_DAYS}d")
    df = _filter_hours(df, underlying)
    atr_pct = _atr5pct(df)
    m = float(_to_scalar(atr_pct.median())) if not atr_pct.empty else None
    if m and m > 0:
        _ATR_CACHE_BASE[underlying] = {"ts": now, "m": m}
    return m

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

def _recommend_leverage(x: float, m: float, base_leverage: float | None = None) -> float | None:
    if not x or not m or x <= 0 or m <= 0:
        return None
    if base_leverage is None:
        base_leverage = BASE_LEVERAGE_DEFAULT
    base_leverage = max(BASE_LEVERAGE_MIN, base_leverage)   # <<< NEU
    raw = base_leverage * (m / x)
    clipped = min(LEVER_MAX, raw)
    return round(clipped * 2) / 2.0




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

    for key, lab in labels:
        active = (key == category)
        bg_col  = VOLA_COLORS.get(key, "#eee") if active else "#eeeeee"
        brd_col = VOLA_COLORS.get(key, "#aaa") if active else "#cccccc"

        if active and key == "very_high" and critical_red:
            bg_col  = VOLA_COLORS["very_low"]   # gleiches Rot wie „sehr niedrig“
            brd_col = VOLA_COLORS["very_low"]

        border = f"2px solid {brd_col}" if active else "1px solid #cccccc"

        if active:
            if recommended_leverage is not None and recommended_leverage >= 5.0:
                try:
                    val_txt = f"{float(_to_scalar(recommended_leverage)):.1f}×"
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
    
###start schneller#####################
def warmup_drivers():
    with _DRIVER_POOL_LOCK:
        for key in ("onvista", "general"):
            if _DRIVER_POOL.get(key) is None:
                try:
                    service = Service(ChromeDriverManager().install())
                    drv = webdriver.Chrome(service=service, options=_make_chrome_options())
                    _enable_cdp_blocking(drv)  # Bilder/CSS blocken
                    _DRIVER_POOL[key] = drv

                    # NEU: auch global registrieren, damit _cleanup sie findet
                    _DRIVERS.append(drv)
                    _SERVICES.append(service)
                    try:
                        if getattr(service, "process", None):
                            _SERVICE_PIDS.append(service.process.pid)
                    except:
                        pass

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
NEWS_REFRESH_SECONDS = 60
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

def _vola_name(u: str) -> str:
    return {
        "Dax": "VDAX",
        "EURO STOXX 50": "VSTOXX",
        "S&P 500": "VIX",
        "Dow Jones": "VXD",
        "Nasdaq": "VXN",
    }.get(u, "Vola")



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
def _ft_accept_cookies(d, timeout=8):
    try:
        WebDriverWait(d, timeout).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        # Häufig genutzte Consent-Frameworks
        selectors = [
            (By.CSS_SELECTOR, "button#onetrust-accept-btn-handler"),
            (By.CSS_SELECTOR, "button[aria-label*='Akzeptieren'], button[aria-label*='Zustimmen']"),
            (By.XPATH, "//button[contains(., 'Alle akzeptieren') or contains(., 'Zustimmen') or contains(., 'Akzeptieren')]"),
            # Consentmanager / Usercentrics
            (By.CSS_SELECTOR, "button[data-testid='uc-accept-all-button']"),
            (By.CSS_SELECTOR, "button.cm-btn--accept-all, button[mode='primary']")
        ]
        for how, sel in selectors:
            try:
                btn = d.find_element(how, sel)
                if btn.is_displayed():
                    btn.click(); time.sleep(0.5); break
            except Exception:
                continue
    except Exception:
        pass



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
    page_items = headlines[start:end] if end <= total else (headlines[start:] + headlines[:end - total])
    page_info = f" {page_index + 1}/{num_pages}"
    return html.Div([
        html.Div([
            html.Span(f"Top-Börsennachrichten (finanztreff.de) Seite {page_info}", style={"fontWeight": "bold", "display": "block"}),
            html.Span(f"Stand: {last_str}", style={"color": "#555", "fontSize": "90%", "display": "block"})
        ], style={"marginBottom": "10px"}),
        html.Ul([
            html.Li(
                html.A(title, href=link, target="_blank", style={"textDecoration": "none", "color": "#004c99"}),
                style={"marginBottom": "8px", "listStyleType": "none"}
            )
            for title, link in page_items
        ], style={"paddingLeft": "0", "marginTop": "0"})
    ], style={"position": "absolute","right": "30px","top": "480px","width": "400px","backgroundColor": "#e0e0e0","padding": "12px","borderRadius": "8px","zIndex": "1000"})

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
    return {"Dax":"^GDAXI","S&P 500":"^GSPC","EURO STOXX 50":"^STOXX50E","Dow Jones":"^DJI","Nasdaq":"^NDX"}.get(underlying,None)

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
    "Nasdaq": {
        "long": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-NASDAQ-100?idExerciseRight=2",
        "short": "https://www.onvista.de/derivate/Knock-Outs/Knock-Outs-auf-NASDAQ-100?idExerciseRight=1",
       
    }
}


# --- Top-10 Firmen pro Index (gleichgewichtet) ---
# --- Top-10 Firmen pro Index (gleichgewichtet) ---
TOP10_TICKERS = {
    "Dax": [
        "SAP.DE","SIE.DE","ALV.DE","DTE.DE","IFX.DE",
        "MBG.DE","MUV2.DE","BAS.DE","VOW3.DE","BMW.DE"
    ],
    "EURO STOXX 50": [
        "ASML.AS","NOVN.SW","SAP.DE","MC.PA","OR.PA",
        "LIN",      # Linde plc primär NYSE
        "SIE.DE","TTE.PA","AI.PA","IBE.MC"
    ],
    "S&P 500": ["AAPL","MSFT","NVDA","AMZN","GOOGL","META","TSLA","GOOG","AVGO","BRK-B"],
    "Dow Jones": ["MSFT","AAPL","UNH","JNJ","JPM","V","PG","HD","TRV","GS"],
    "Nasdaq 100": ["AAPL","MSFT","NVDA","AMZN","GOOGL","META","TSLA","GOOG","AVGO","COST"],
}


def _yf_symbol(sym: str) -> str:
    s = sym.strip()
    keep = (".DE",".PA",".L",".MI",".SW",".TO",".HK")
    if any(s.endswith(k) for k in keep): return s
    return s.replace(".", "-")

def _fix_yf_symbol(sym: str) -> str:
    return sym.replace(".", "-") if sym.count(".")==1 and "." in sym else sym

def _get_top10_tickers(underlying: str) -> list[str]:
    alias = {
        "Nasdaq": "Nasdaq 100",
        "EUROSTOXX50": "EURO STOXX 50",
    }
    key = alias.get(underlying, underlying)
    return TOP10_TICKERS.get(key, TOP10_TICKERS.get("Dax", []))


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

refresh_interval = 6  #Abruf Intervall
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

def get_index_data(underlying):
    """
    Prozent-Change ggü. Vortagesschluss + aktueller Lastpreis.
    Intraday mit 1m-Daten, Fallback: Tagesdaten.
    """
    try:
        ticker_map = {"Dax":"^GDAXI","S&P 500":"^GSPC","EURO STOXX 50":"^STOXX50E","Dow Jones":"^DJI","Nasdaq":"^NDX"}
        sym = ticker_map.get(underlying)
        if not sym:
            return None, "-", "gray"

        t = yf.Ticker(sym)

        # Vortagesschluss aus Tagesserie
        daily = t.history(period="5d")
        prev_close = daily["Close"].dropna().iloc[-2] if len(daily.dropna()) >= 2 else None

        # Intraday-Lastpreis
        intra = t.history(period="1d", interval="1m")
        last = intra["Close"].dropna().iloc[-1] if not intra.empty else None

        if last is not None and prev_close:
            change = (last - prev_close) / prev_close * 100.0
            return float(change), f"{float(last):.2f}", "color"

        # Fallback: alte Logik (Tageskerzen)
        data = t.history(period="2d")
        if len(data) >= 2:
            prev = data["Close"].iloc[-2]
            curr = data["Close"].iloc[-1]
            change = (curr - prev) / prev * 100.0
            return float(change), f"{float(curr):.2f}", "color"

        raise ValueError("Keine Daten von Yahoo verfügbar")
    except Exception as e:
        print(f"Fehler bei Yahoo-Finance-Abfrage: {e}")
        return None, "-", "gray"


def get_intraday_change_min_max(underlying: str):
    """Liefert (min_pct, max_pct) des heutigen Tages relativ zum Vortagesschluss in Prozent.
       Quelle: Yahoo Finance 1m-Daten. Kein CSV."""
    ticker_map = {"Dax":"^GDAXI","S&P 500":"^GSPC","EURO STOXX 50":"^STOXX50E","Dow Jones":"^DJI","Nasdaq":"^NDX"}
    sym = ticker_map.get(underlying)
    if not sym:
        return None, None
    try:
        t = yf.Ticker(sym)
        daily = t.history(period="5d")
        prev_close = daily["Close"].dropna().iloc[-2] if len(daily.dropna()) >= 2 else None
        intra = t.history(period="1d", interval="1m")
        if prev_close is None or intra.empty:
            return None, None
        highs = intra["High"].dropna()
        lows  = intra["Low"].dropna()
        if highs.empty or lows.empty:
            return None, None
        max_pct = (highs.max() - prev_close) / prev_close * 100.0
        min_pct = (lows.min()  - prev_close) / prev_close * 100.0
        return float(max_pct), float(min_pct)
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


def get_volatility_change(underlying):
    global _volatility_cache
    now_ts = time.time()
    cache = _volatility_cache.get(underlying, {"value": None, "ts": 0})

    # TTL an refresh_interval koppeln
    ttl = max(1, refresh_interval - 1)
    if (now_ts - cache["ts"] < ttl) and (cache["value"] is not None):
        return cache["value"]

    # nur aktives Underlying aktiv abrufen, sonst nur Cache liefern
    try:
        if underlying != get_selected_underlying():
            return cache.get("value")
    except Exception:
        return cache.get("value")

    # Clamp ±30 %
    CLAMP_MIN, CLAMP_MAX = -30.0, 30.0
    def _clamp(p):
        return max(CLAMP_MIN, min(CLAMP_MAX, float(p)))

    try:
        # Finanztreff-Sperrfenster 09:00–09:40 Europe/Berlin
        _now = datetime.now(TZ_BERLIN)
        _start = _now.replace(hour=9, minute=0, second=0, microsecond=0)
        _end   = _now.replace(hour=9, minute=40, second=0, microsecond=0)
        _block_finanztreff_vola = (_start <= _now < _end) and (underlying in ("Dax", "EURO STOXX 50"))

        val = None

        if underlying == "EURO STOXX 50":
            if _block_finanztreff_vola:
                val = (get_vstoxx_change_stock3()
                       or get_vstoxx_change_onvista()
                       or get_vstoxx_change_yahoo())
            else:
                val = (get_vstoxx_change_stock3()
                       or get_vstoxx_change_onvista()
                       or get_vstoxx_change_yahoo()
                       or get_vstoxx_change_finanztreff())

        elif underlying == "Dax":
            base = get_vdax_change()
            if base is not None:
                v = _clamp(base)
                _volatility_cache["Dax"] = {"value": v, "ts": now_ts}
                return v
            if not _block_finanztreff_vola:
                val = get_vdax_change_finanztreff()

        elif underlying == "S&P 500":
         #  val = (get_vix_change_finanztreff() or get_vix_change_yahoo())
            val = (get_vix_change_yahoo() or get_vix_change_finanztreff())

        elif underlying == "Dow Jones":
            val = (get_vxd_change_yahoo() or get_vxd_change_finanztreff())
           #val = (get_vxd_change_finanztreff() or get_vxd_change_yahoo())

        elif underlying == "Nasdaq":
            val = (get_vxn_change_yahoo() or get_vxn_change_finanztreff())
           #val = (get_vxn_change_finanztreff() or get_vxn_change_yahoo())
        if val is not None:
            v = _clamp(val)
            _volatility_cache[underlying] = {"value": v, "ts": now_ts}
            return v

        # Fallback: letzter Wert
        return cache.get("value")

    except Exception as e:
        print(f"⚠️ get_volatility_change: {e}")
        return cache.get("value")



def get_vstoxx_change_yahoo():
    """Fallback to Yahoo Finance for VSTOXX data"""
    try:
        # Try different Yahoo symbols for VSTOXX
        for symbol in ["^V2TX", "^VSTOXX"]:
            try:
                data = yf.Ticker(symbol).history(period="2d")
                if len(data) >= 2:
                    prev = data["Close"].iloc[-2]
                    curr = data["Close"].iloc[-1]
                    change = ((curr - prev) / prev) * 100
                    return round(change, 2)
            except Exception:
                continue
    except Exception as e:
        print(f"⚠️ Yahoo VSTOXX fallback failed: {e}")
    
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
            close_onvista_popups(d, timeout=6)   
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
            close_onvista_popups(d, timeout=6)  
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
    market_hours = MARKET_TIMES.get("USA", {"start": {"hour": 15, "minute": 30}, "end": {"hour": 22, "minute": 0}})
    return f"{market_comment} (Öffnungszeiten: {market_hours['start']['hour']:02d}:{market_hours['start']['minute']:02d}-{market_hours['end']['hour']:02d}:{market_hours['end']['minute']:02d} Uhr MEZ)"


# --- Finanztreff: generischer Vola-Parser ---
def _ft_accept_cookies_quick(d, timeout=6):
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


def get_vstoxx_change_finanztreff(): return _finanztreff_vola_change("VSTOXX")
def get_vix_change_finanztreff():     return _finanztreff_vola_change("VIX")
def get_vxd_change_finanztreff():     return _finanztreff_vola_change("VXD")
def get_vxn_change_finanztreff():     return _finanztreff_vola_change("VXN")


def _ampel1_status_core(underlying: str):
    # --- Daten holen ---
    idx_change, _, _ = get_index_data(underlying)
    vola_change = get_volatility_change(underlying)

    vola_name = _vola_name(underlying)
    title = get_ampel1_title(underlying) 

    if idx_change is None or vola_change is None:
        missing = []
        if idx_change is None: missing.append(f"{underlying}-Daten")
        if vola_change is None: missing.append(f"{vola_name}-Daten")
        return FARBCODES["gray"], title, f"Keine Daten verfügbar. Min 20 Punkte.Bitte warten. ({', '.join(missing)})."

    th_abs = max(AMP1_MIN_MOVE_FLOOR, 0.001)

    # Farbe
    if abs(idx_change) < th_abs:
        base_color = "gray"
        same_sign = (idx_change * vola_change) > 0
        if same_sign:
        # beide im selben Vorzeichen → Beträge vergleichen
            vola_stronger = abs(vola_change) > abs(idx_change)
        else:
        # gegensätzliche Richtung → orange nur wenn Vola steigt
            vola_stronger = vola_change > 0
        color = "orange" if vola_stronger else "green"


    # Kommentar
    if abs(idx_change) < th_abs:
        if abs(vola_change) <= abs(idx_change):
            comment = f"Seitwärts. {vola_name} unter {underlying} → entspannt."
        else:
            comment = f"Seitwärts. {vola_name} über {underlying} → Nervosität steigt."
    else:
        if idx_change > 0 and vola_change < 0:
            color = "green"
            comment = f"{underlying} (steigt) und {vola_name} (fällt) → Entspannung bestätigt."
        elif idx_change < 0 and vola_change > 0:
            color = "red"
            comment = f"{underlying} (fällt) und {vola_name} (steigt) → Stressphase, Risiko hoch."
        elif idx_change > 0 and vola_change > 0:
            color = "orange"
            comment = f"{underlying} (steigt) und {vola_name} (steigt) → Vorwarnung möglicher Wendepunkt."
        else:
            color = "orange"
            comment = f"{underlying} (fällt) und {vola_name} (fällt) → Beruhigung im Abschwung."

    comment += f" ({underlying}: {idx_change:+.2f} %, {vola_name}: {vola_change:+.2f} %)."
    return FARBCODES[color], title, comment

#Ersetzt die statischen Titel durch einen dynamischen Helper (ampel 1)
def get_ampel1_title(u: str) -> str:
    return f"Ampel 1: Zusammenhang {u} ↔ {_vola_name(u)} (sofort)"

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

    q20 = float(s_vola.quantile(0.20))
    q80 = float(s_vola.quantile(0.80))

    recent = s_vola.tail(4)  # 3 Diffs
    diffs  = recent.diff().tail(3)
    up_cnt   = int((diffs > 0).sum())
    down_cnt = int((diffs < 0).sum())

    up_trend   = (v_now >= q80) and (up_cnt >= 2)
    down_trend = (v_now <= q20) and (down_cnt >= 2)
    return up_trend, down_trend, rel_pos, v_now, i_now



def get_ampel1_status(df, selected_underlying):
    # Grau nur bei fehlenden Daten
    if len(df) < 20 or 'volatility_change' not in df.columns or 'index_change' not in df.columns:
        return FARBCODES["gray"], 0.5, "Keine Daten für Ampel 1. Bitte warten - 20 Datenpunkte erforderlich"

    try:
        df_window = df.iloc[-min(len(df), 654):]

        # Trend-Flags + rel_pos + aktuelle Werte
        up_trend, down_trend, rel_pos, v_now, i_now = _amp1_trend_flags(df_window)

        vola_name = {"Dax":"VDAX","S&P 500":"VIX","EURO STOXX 50":"VSTOXX","Dow Jones":"VXD","Nasdaq":"VXN"}.get(selected_underlying, "Vola")
        tstamp = df_window['timestamp'].iloc[-1]
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

        # Overlay: Orange nur bei deutlicher Vola-Bewegung (alter Ansatz)
        color = base_color
        text  = base_text

        # Zusatz: Index-Richtung kurz prüfen (3 Ticks)
        idx_diffs = df_window["index_change"].dropna().tail(4).diff().tail(3)
        idx_up   = int((idx_diffs > 0).sum()) >= 2
        idx_down = int((idx_diffs < 0).sum()) >= 2

        # Regeln
        if base_color == FARBCODES["green"] and up_trend:
            color = FARBCODES["orange"]
            text  = f"{selected_underlying} ↑, {vola_name} ↑ deutlich → Trendwende möglich."
        elif base_color == FARBCODES["red"] and down_trend:
            color = FARBCODES["orange"]
            text  = f"{selected_underlying} ↓, {vola_name} ↓ deutlich → Entspannung möglich."
        else:
            # Konflikt-Overlays unabhängig von Baseline, wenn stark:
            if idx_up and up_trend:
                color = FARBCODES["orange"]
                text  = f"{selected_underlying} ↑, {vola_name} ↑ deutlich → Trendwende möglich."
            elif idx_down and down_trend:
                color = FARBCODES["orange"]
                text  = f"{selected_underlying} ↓, {vola_name} ↓ deutlich → Entspannung möglich."

        # Min/Max-Info wie zuvor
        vmin = float(df_window['volatility_change'].min())
        vmax = float(df_window['volatility_change'].max())
        text += f" {vola_name}: {v_now:+.2f} %, ( Min {vmin:.2f}%, Max {vmax:.2f}%, seit {tstr} Uhr )."

        # Baseline speichern
        globals()["AMP1_BASELINE_LAST"][selected_underlying] = base_color
        return color, float(rel_pos), text

    except Exception as e:
        return FARBCODES["gray"], 0.5, f"Fehler Ampel 1: {e}"




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


from datetime import datetime

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



# --- VDAX Fallback über finanztreff.de (robust, mit Mini-Cache) ---
# --- VDAX Fallback über finanztreff.de: immer % zurückgeben ---
_FT_VDAX_CACHE = {"ts": 0.0, "val": None}

# --- VDAX Fallback über finanztreff.de: garantiert Prozent, nie Punkte ---

# Garantiert %-Änderung, ohne feste Sleeps
def get_vdax_change_finanztreff(timeout=6) -> float | None:
    d = get_driver("general", KEY_GLOBAL)
    d.get("https://www.finanztreff.de/index/vdax-new")
    _ft_accept_cookies(d)
    WebDriverWait(d, timeout, poll_frequency=POLL).until(
        EC.presence_of_element_located((By.TAG_NAME, "body"))
    )
    # Erst % suchen
    if re.search(r"[+\-]?\d+(?:[.,]\d+)?\s*%", d.page_source or ""):
        m = re.search(r"([+\-]?\d+(?:[.,]\d+)?)\s*%", d.page_source or "")
        return round(float(m.group(1).replace(",", ".")), 2)

    # Sonst Aktuell/Vortag in kleinen Fenstern ziehen
    html = d.page_source or ""
    def _nums_near(label, span=140):
        m = re.search(label, html, flags=re.I)
        if not m: return []
        win = html[max(0, m.start()): m.end() + span]
        return [float(x.replace(".", "").replace(",", ".")) 
                for x in re.findall(r"\d{1,3}(?:\.\d{3})*(?:,\d+)?|\d+(?:,\d+)?", win)]
    cur = _nums_near(r"(Aktuell|Zuletzt|Letzter|Kurs)")
    prev = _nums_near(r"(Vortag|Schluss|Vorh\.\s*Schluss|Vortages|Vortrag)")
    if cur and prev and prev[0] > 0:
        return round(((cur[0] - prev[0]) / prev[0]) * 100.0, 2)
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
    while not stop_event.is_set():
        try:
            u = get_selected_underlying()
            urls = UNDERLYINGS.get(u, {})
            if not urls:
                time.sleep(10); continue

            # 1) schnelle Einzel-Scrapes
            long_vals, short_vals = scrape_onvista_leverage(u)

            # Mittelwerte bilden
            lv = float(np.mean(long_vals)) if long_vals else None
            sv = float(np.mean(short_vals)) if short_vals else None

            # Cache aktualisieren
            now = time.time()
            entry = _LEVER_CACHE.setdefault(u, {"long": None, "short": None, "ts": 0})
            if lv is not None:
                entry["long"] = float(lv); entry["ts"] = now
            if sv is not None:
                entry["short"] = float(sv); entry["ts"] = now

        except Exception as e:
            print(f"⚠️ leverage_loop: {e}")
        time.sleep(10)




def start_leverage_thread():
    global _lever_thread, stop_event
    if 'stop_event' not in globals() or stop_event is None:
        stop_event = threading.Event()
    if _lever_thread and _lever_thread.is_alive():
        return
    _lever_thread = threading.Thread(target=_leverage_loop, name="leverage_loop", daemon=True)
    _lever_thread.start()
###########


# oben einfügen
_last_csv_write = {"ts": 0}

def update_data():
    global last_fetch_time
    global _last_csv_write
    
    while not stop_event.is_set():
        try:
            # aktuelles Underlying
            cu = get_selected_underlying()
            urls = UNDERLYINGS.get(cu, {})
            
            if not urls or "long" not in urls or "short" not in urls:
                print(f"⚠️ Keine URLs für {cu}")
                time.sleep(refresh_interval)
                continue

            # --- Rohwerte Hebel ---
            #long_avg_raw  = scrape_average_leverage(urls["long"])
            #short_avg_raw = scrape_average_leverage(urls["short"])
            # Cache lesen
            cache = _LEVER_CACHE.get(cu, {})
            is_fresh = (time.time() - float(cache.get("ts", 0))) < _LEVER_TTL

            long_cached  = cache.get("long", None) if is_fresh else None
            short_cached = cache.get("short", None) if is_fresh else None

# Fallbacks: wenn Cache leer, nimm letzten Filter-Wert, sonst None
            long_avg_raw  = long_cached  if long_cached  is not None else LEVER_LONG_FILTER.last()
            short_avg_raw = short_cached if short_cached is not None else LEVER_SHORT_FILTER.last()


            # --- Indexänderung (%): Nasdaq zuerst finanztreff (strict/validated), sonst unverändert ---
            index_change_raw, index_display_value = (None, "-")

            if cu == "Nasdaq":
                # Finanztreff zuerst, mit Validierung gegen Yahoo
                try:
                    index_change_raw = (get_nasdaq_change_finanztreff_validated()
                                        or (get_index_data(cu) or (None, "-", None))[0])
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

            # --- Volatilität ---
            vola_change_raw = get_volatility_change(cu)

            # --- Top-10 Ø gleichgewichtet ---
            try:
                top10_now_raw = get_top10_eq_change_pct(cu)
            except Exception:
                top10_now_raw = None

            # --- Filter ---
            long_avg     = LEVER_LONG_FILTER.update(long_avg_raw)
            short_avg    = LEVER_SHORT_FILTER.update(short_avg_raw)
            tmp = INDEX_FILTER.update(index_change_raw)
            index_change = tmp if tmp is not None else INDEX_FILTER.last()
            vola_change  = VOL_FILTER.update(vola_change_raw)
            top10_now    = top10_now_raw

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
                    "top10_avg": top10_now if top10_now is not None else np.nan,
                }

                # Throttle: nur 1x pro Intervall schreiben
                global _last_csv_write
                now = time.time()
                if now - _last_csv_write["ts"] >= refresh_interval:
                    try:
                        if os.path.exists(filename):
                            try:
                                old = pd.read_csv(filename)
                                if not old.empty:
                                    if "top10_avg" not in old.columns:
                                        old["top10_avg"] = np.nan
                                    df = pd.concat([old, pd.DataFrame([row])], ignore_index=True)
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
    return {"Dax":"VDAX (niedrig=gut)","S&P 500":"VIX (niedrig=gut)","EURO STOXX 50":"VSTOXX (niedrig=gut)","Dow Jones":"VXD (niedrig=gut)","Nasdaq":"VXN (niedrig=gut)"}.get(selected_underlying,"Volatilität")

# -----------------------------------------------
# -----------------------------------------------
# Layout
# -----------------------------------------------
# Layout (v78) mit Bild am Ende + pointerEvents
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
        html.Span("v78", style={"fontSize": "16px", "color": "#666", "verticalAlign": "super"}),
        dcc.ConfirmDialog(id="confirm-exit", message="- Leverage Lens - beenden?")
    ], style={"textAlign": "center", "marginBottom": "20px"}),

    html.Div(
        dcc.Dropdown(
            id="underlying-dropdown",
            options=[{"label": ("Nasdaq 100" if k=="Nasdaq" else k), "value": k} for k in UNDERLYINGS.keys()],
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
        html.Button("Abruf Intervall (Sek)", id="set-interval-btn", style={"marginLeft": "7px", "fontSize": "18px"}),
        html.Button("Reset", id="reset-btn", style={"marginLeft": "7px", "fontSize": "18px"})
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
        persistence=False, persistence_type="local",
    ),
    html.Label(
        "Volatilität einblenden",
        style={'display': 'inline-block','fontSize': '16px','fontWeight': 'bold','color':'black'}
    )
], style={'marginBottom': '15px','display':'flex','alignItems':'center',"padding": "10px","marginTop": "10px","marginTop": "10px"}),

html.Div([
    dcc.Checklist(
        id='top10-toggle',
        options=[{'label': '', 'value': 'on'}],
        value=[],
        inline=True,
        style={'display': 'inline-block','marginRight': '10px','transform': 'scale(1.5)'},
        persistence=False, persistence_type="local",
    ),
    html.Label(
        "Top-10 Index-Schwergewichte",
        style={'display': 'inline-block','fontSize': '16px','fontWeight': 'bold','color':'black'}
    )
], style={'marginBottom': '15px','display':'flex','alignItems':'center',"padding": "5px","marginLeft": "5px" }),



   

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
dcc.Graph(id="leverage-graph",
    config={
        "displaylogo": False,
        "modeBarButtonsToRemove": ["zoomIn2d","zoomOut2d"],
        "displayModeBar": True
    },
    style={"height": "90vh"}  # Grafik schon sehr groß
),




    dcc.Interval(id="interval-component", interval=refresh_interval * 1000, n_intervals=0),
    dcc.Interval(id="atr-interval", interval=300000, n_intervals=0),
    html.Audio(id="alarm-audio", src="", autoPlay=True, controls=False, style={"display": "none"}),

    # Bild zuletzt, klick-durchlässig
html.Img(
    src=app.get_asset_url(get_seasonal_image()),
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
    Output('volatility-output', 'children'),
    Input('volatility-toggle', 'value')
)
def update_volatility_label(volatility_toggle):
    if 'on' in volatility_toggle:
        return "Volatilität wird angezeigt."
    return "Volatilität wird nicht angezeigt."
     

def _recommend_leverage_eff(eff_ratio: float, base_leverage: float | None = None) -> float | None:
    if eff_ratio is None or eff_ratio <= 0:
        return None
    if base_leverage is None:
        base_leverage = BASE_LEVERAGE_DEFAULT
    base_leverage = max(LEVER_MIN, base_leverage)  # min 5.0 wenn LEVER_MIN=5.0
    raw = base_leverage / eff_ratio
    clipped = min(LEVER_MAX, raw)
    return round(clipped * 2) / 2.0




#####für Vola + Hebelempfehlung++++++++++++++
# Dann den Callback aktualisieren:
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

    # --- Kennzahl 1: ATR-Status ---
    m = _get_baseline_m(u)         # 30T-Median ATR5% (5m)
    x = _get_current_x(u)          # aktueller ATR5% EMA(3)
    if not m or not x:
        return build_vola_strip("off", base, None), "", "", VOLA_DESCRIPTIONS["off"]

    # --- Cross-Index-Korrektur der Basis ---
    avg_m = _mean_baseline_vola(exclude=None)
    if avg_m and avg_m > 0:
        k = avg_m / m
        base_star = np.clip(round((base * k) * 2) / 2.0, LEVER_MIN, LEVER_MAX)
    else:
        base_star = base

    # --- Kennzahl 2: Live-Bewegung aus Indexlinie ---
    L_pct = _live_movement_pct(u)  # −0.6 .. +1.6 typ. Bereich

    # --- Stufenmapping (±10% = normal) ---
    def _pct_to_level(pct: float) -> int:
        r = 1.0 + float(pct)
        if r < VOLA_THRESH["very_low"]:      return 1
        if r < VOLA_THRESH["low"]:           return 2
        if r <= VOLA_THRESH["high"]:         return 3
        if r <= VOLA_THRESH["very_high"]:    return 4
        return 5

    S_pct  = (x / m) - 1.0
    S_lvl  = _pct_to_level(S_pct)
    L_lvl  = _pct_to_level(L_pct)
    lvl    = int(np.clip(round(0.4 * S_lvl + 0.6 * L_lvl), 1, 5))
    cat    = {1:"very_low",2:"low",3:"normal",4:"elevated",5:"very_high"}[lvl]

    # --- Hebel-Empfehlung (Effizienz) ---
    r_eff = 0.40 * (x / m) + 0.60 * (1.0 + L_pct)
    L_rec = _recommend_leverage_eff(r_eff, base_star)

    # --- Anzeige ---
    strip = build_vola_strip(cat, base_star, L_rec)

    # Standardbeschreibung
    description = VOLA_DESCRIPTIONS.get(cat, VOLA_DESCRIPTIONS["off"])
    desc_children = description  # Default

    # Extra-Text für „Ampel 5:“
    if cat == "very_high" and L_rec is not None and base_star and L_rec <= base_star * AMP5_RED_LEVER_RATIO:
        desc_children = html.Span([
            html.Strong("Ampel 5: "),
            "extreme Volatilität; Handel nur mit äußerster Vorsicht!"
            " News- und Ereignisprüfung zwingend."
    ])


    return strip, "", "", desc_children



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
    Input('interval-component', 'n_intervals'),
    Input('underlying-dropdown', 'value'),
    Input('volatility-toggle', 'value'),
    Input('top10-toggle','value'),     # NEU
    Input('sound-toggle', 'value'),
)
def update_graph(n, selected, volatility_toggle, top10_toggle, sound_value):
    global selected_underlying, last_fetch_time, show_volatility, _last_alarm_state

    # Underlying-Wechsel -> Reset
    if selected != selected_underlying:
        switch_underlying(selected)
     

    # Sound
    sound_on = bool(sound_value) and ("on" in sound_value)
    set_sound_enabled(sound_on)
    alarm_src = ""

    # Schalter
    show_volatility = ('on' in volatility_toggle) if isinstance(volatility_toggle, (list, tuple, set)) else False
    show_top10 = ('on' in top10_toggle) if isinstance(top10_toggle, (list, tuple, set)) else False

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

    # Tages-Min/Max aus Yahoo
    try:
        _ticker_map = {
            "Dax": "^GDAXI",
            "S&P 500": "^GSPC",
            "EURO STOXX 50": "^STOXX50E",
            "Dow Jones": "^DJI",
            "Nasdaq 100": "^NDX",
            "Nasdaq": "^NDX",  # Fallback
        }
        _sym = _ticker_map.get(selected)
        if _sym:
            _t = yf.Ticker(_sym)
            _daily = _t.history(period="5d")
            _prev = _daily["Close"].dropna().iloc[-2] if len(_daily.dropna()) >= 2 else None
            _intra = _t.history(period="1d", interval="1m")
            if _prev is not None and not _intra.empty:
                _max_pct = (_intra["High"].max() - _prev) / _prev * 100.0
                _min_pct = (_intra["Low"].min()  - _prev) / _prev * 100.0
                day_minmax_text = f"Min: {_min_pct:.2f}% · Max: {_max_pct:.2f}%"
    except Exception:
        day_minmax_text = ""

    # Haupt-CSV laden
    csv_file = get_csv_filename(selected_underlying)
    lock = FILE_LOCKS[csv_file]
    with lock:
        if os.path.exists(csv_file):
            try:
                df = pd.read_csv(csv_file, parse_dates=['timestamp'], encoding='utf-8')
            except Exception:
                df = pd.DataFrame(columns=["timestamp","long_avg","short_avg","index_change","volatility_change","top10_avg"])
        else:
            df = pd.DataFrame(columns=["timestamp","long_avg","short_avg","index_change","volatility_change","top10_avg"])

    # Grundsäuberung
    try:
        if not df.empty:
            for col in ['long_avg','short_avg','index_change']:
                if col not in df.columns:
                    df[col] = np.nan
            if 'volatility_change' in df.columns:
                df['volatility_change'] = df['volatility_change'].ffill().bfill()
            if 'top10_avg' in df.columns:
                df['top10_avg'] = df['top10_avg'].ffill().bfill()
            df = df.ffill()
        else:
            # leere Startdatei sicherstellen
            empty = pd.DataFrame(columns=["timestamp","long_avg","short_avg","index_change","volatility_change","top10_avg"])
            atomic_write_csv(empty, csv_file)
    except Exception as e:
        print(f"Fehler beim Aufbereiten der CSV: {e}")
        df = pd.DataFrame(columns=["timestamp","long_avg","short_avg","index_change","volatility_change","top10_avg"])

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
        if show_top10 and 'top10_avg' in df.columns and df['top10_avg'].notna().any():
            fig.add_trace(go.Scatter(
                x=df['timestamp'], y=df['top10_avg'].interpolate(),
                mode='lines',
                name='Top-10 Firmen-Ø (hoch=gut)',
                line=dict(color='rgb(0, 210, 210)', width=2), # <- hier Farbe 
                yaxis='y2',
                hovertemplate="%{x|%H:%M:%S}<br>%{y:.2f}%<extra></extra>",
                connectgaps=True
            ))

        # Y2 Range
        y2_series = df['index_change']
        if show_volatility and 'volatility_change' in df.columns:
            y2_series = pd.concat([y2_series, df['volatility_change']], axis=0)
        if show_top10 and 'top10_avg' in df.columns:
            y2_series = pd.concat([y2_series, df['top10_avg']], axis=0)
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


    
    return (
        fig,
         _last_fetch_el,
        html.Div([
            html.Div([
                html.Span(f"Index aktuell: {index_display_percentage}", style={"color": index_display_color,"fontWeight": "bold","fontSize": "25px","marginRight": "12px"}),
                html.Span(day_minmax_text, style={"color": "#000","fontSize": "18px","marginRight": "12px"}),
             
                html.Span(is_market_open(selected), style={"fontSize": "18px","color": "#444"})
            ], style={"display": "flex","alignItems": "center"}),
            html.Br(),
            news_or_info_block,
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

_CLEANUP_REGISTERED = False

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




if __name__ == "__main__":
    _register_shutdown_hooks()  # einmalig Hooks setzen
    try:
        start_update_thread()
        start_leverage_thread()
        warmup_drivers()
        warmup_requests()
        try:
            import webbrowser
            threading.Timer(0.8, lambda: webbrowser.open("http://127.0.0.1:8050")).start()
        except Exception:
            pass

        # App starten
        app.run(debug=False, host="127.0.0.1", port=8050, use_reloader=False)

    except OSError as e:
        if "Address already in use" in str(e):
            print("Port 8050 belegt. Starte auf 8051 …")
            app.run(debug=False, host="127.0.0.1", port=8051, use_reloader=False)
        else:
            raise
    except KeyboardInterrupt:
        print("\nAbbruch per Tastatur")
    except Exception as e:
        print(f"Unerwarteter Fehler: {e}")
    finally:
        # geordnet stoppen und hart bereinigen
        request_shutdown()
        _cleanup()

