# Hebelwatch Markus Jurina (markus@jurina.biz) 23.08.2025 v61 
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
import os
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
from selenium.webdriver.chrome.service import Service
from webdriver_manager.chrome import ChromeDriverManager
from selenium.webdriver.chrome.options import Options
import tempfile, shutil, atexit
from datetime import timedelta
import gc
import yfinance as yf
from functools import lru_cache
import math
import pytz
from datetime import datetime
import plotly.io as pio
from threading import Lock
import re
import os, sys
# --- Imports (einmalig oben) ---
from selenium.webdriver.common.by import By
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
from datetime import datetime

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
    elif abs(bps) >= 70:
        txt = "Kritisch (Liquiditätsstress): 70–100 bps – Banken leihen zögerlich. Meist Vorbote stärkerer Abverkäufe."
    elif abs(bps) >= 40:
        txt = "Erhöht (Interbankmarkt wird nervös): 40–70 bps – Frühwarnsignal für knapper werdende Liquidität."
    elif abs(bps) >= 10:
        txt = "Normalbereich (kein Stress): 10–40 bps – Typisch in ruhigen Marktphasen."
    else:
        txt = "Unter Normalbereich (<10 bps) – sehr ruhige Interbank-Lage."

    _SOFR_CACHE.update({"ts": now, "bps": bps, "text": txt})
    return bps, txt
##################################################################################################


# --- VSTOXX (stock3) robust ---
_last_vstoxx_change = None

def get_vstoxx_change_stock3(driver, timeout=20, retries=3):
    """
    Liefert die Tagesänderung des VSTOXX in Prozent als float (z.B. 0.85).
    Quelle: stock3 – stabile Detail-URL + klassischer Selektor.
    Fällt auf den letzten gültigen Wert zurück.
    """
    global _last_vstoxx_change
    url = "https://stock3.com/indizes/vstoxx-volatilitaetsindex-17271029/"
    try:
        driver.get(url)
    except Exception as e:
        print(f"⚠️ VSTOXX: Navigation fehlgeschlagen: {e}")
        return _last_vstoxx_change

    # Cookie-Banner versuchen zu schließen
    try:
        accept_cookies_if_present(driver, timeout=8)
    except Exception:
        pass

    for attempt in range(retries):
        try:
            el = WebDriverWait(driver, timeout).until(
                EC.visibility_of_element_located((By.CSS_SELECTOR, "span.instrument-value.changePerc"))
            )
            raw = (el.text or el.get_attribute("data-inst-formatted") or "").strip()
            # "0,85 %" → 0.85
            txt = (raw.replace('%','')
                      .replace('\xa0',' ')
                      .replace(' ','')
                      .replace('−','-')
                      .replace('+','')
                      .replace(',', '.'))
            val = float(txt)
            _last_vstoxx_change = round(val, 2)
            print(f"✔️ VSTOXX Veränderung: {_last_vstoxx_change} % (Quelle: stock3 klassisch)")
            return _last_vstoxx_change
        except (StaleElementReferenceException, TimeoutException):
            try:
                driver.refresh()
            except Exception:
                pass
            continue
        except Exception as e:
            print(f"⚠️ VSTOXX: Unerwarteter Fehler: {e} – nutze Last-Good.")
            break

    return _last_vstoxx_change


_SOUND_ENABLED = True
_SOUND_LOCK = Lock()

def get_driver() -> webdriver.Chrome:
    global _DRIVER
    with _DRIVER_LOCK:
        if _DRIVER is not None:
            try:
                # Lösche alle Cookies für eine frische Session
                _DRIVER.delete_all_cookies()
            except:
                pass
        if _DRIVER is None:
            service = Service(ChromeDriverManager().install())
            _DRIVER = webdriver.Chrome(service=service, options=_make_chrome_options())
        return _DRIVER


def set_sound_enabled(val: bool):
    global _SOUND_ENABLED
    with _SOUND_LOCK:
        _SOUND_ENABLED = bool(val)

def is_sound_enabled() -> bool:
    with _SOUND_LOCK:
        return _SOUND_ENABLED
        
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

# Plotly Template
pio.templates["hebelwatch"] = go.layout.Template(
    layout=dict(
        font=dict(family=FONT_STACK, size=13),
        title=dict(font=dict(family=FONT_STACK, size=16)),
        legend=dict(font=dict(family=FONT_STACK, size=12))
    )
)
pio.templates.default = "hebelwatch+plotly_white"

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

    # Wochenende oder fester Feiertag -> geschlossen
    if now.weekday() >= 5 or (now.month, now.day) in HOLIDAYS_FIXED.get(market, set()):
        return f"❌ Börse geschlossen ({market_hours})"

    return f"✅ Börse geöffnet ({market_hours})" if start_dt <= now <= end_dt else f"❌ Börse geschlossen ({market_hours})"


# ==== WebDriver-Setup ====
_DRIVER = None
_DRIVER_LOCK = threading.Lock()
_TMP_PROFILE_DIR = None

def _make_chrome_options() -> Options:
    global _TMP_PROFILE_DIR
    _TMP_PROFILE_DIR = tempfile.mkdtemp(prefix=f"hebelwatch_profile_{time.time()}_")
    opts = Options()
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
    try:
        # Häufig OneTrust/Consent-Manager
        WebDriverWait(d, timeout).until(
            EC.presence_of_element_located((By.TAG_NAME, "body"))
        )
        # Varianten durchprobieren
        candidates = [
            (By.XPATH, "//button[contains(., 'Akzeptieren')]"),
            (By.XPATH, "//button[contains(., 'Zustimmen')]"),
            (By.CSS_SELECTOR, "button#onetrust-accept-btn-handler"),
            (By.XPATH, "//button[contains(@class,'consent') and (contains(.,'OK') or contains(.,'Akzeptieren'))]"),
        ]
        for how, sel in candidates:
            try:
                btn = d.find_element(how, sel)
                if btn.is_displayed():
                    btn.click()
                    time.sleep(0.8)
                    break
            except NoSuchElementException:
                continue
    except TimeoutException:
        pass
    except WebDriverException:
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
    rss_url = "https://www.finanztreff.de/feed/marktberichte.rss"
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
    ], style={"position": "absolute","right": "30px","top": "485px","width": "400px","backgroundColor": "#e0e0e0","padding": "12px","borderRadius": "8px","zIndex": "1000"})

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
    if rsi_value >= 70:
        return "#ff0000", "RSI-Indikator", f"Risiko: Korrektur innerhalb 8 Tage wahrscheinlich! RSI={rsi_value:.1f}%"
    elif rsi_value >= 62:
        return "#FFA500", "RSI-Indikator", f"Warnung: Markt überhitzt! (RSI {rsi_value:.1f}%) Erhöhtes Crash-Risiko um + 20%"
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
refresh_interval = 7
last_fetch_time = "-"
ALARM_THRESHOLD = 999
stop_event = threading.Event()
update_thread = None

_last_vdax_change = None
_last_EURO_STOXX_50_change = None

def get_vdax_change():
    global _last_vdax_change
    try:
        d = get_driver()
        d.get("https://www.boerse-frankfurt.de/index/vdax")
        element = WebDriverWait(d, 10).until(EC.presence_of_element_located((By.CSS_SELECTOR, "td.widget-table-cell.text-end.change-percent")))
        raw = element.text.strip()
        if not raw:
            return _last_vdax_change
        value = float(raw.replace("%", "").replace(",", "."))
        if value == 0.0 and _last_vdax_change not in (None, 0.0):
            return _last_vdax_change
        _last_vdax_change = value
        print(f"✔️ VDAX Veränderung: {value:.2f} %")
        return value
    except Exception as e:
        print("⚠️ Fehler beim Laden der VDAX-Seite:", e)
        return _last_vdax_change

def get_EURO_STOXX_50_change():
    global _last_EURO_STOXX_50_change
    try:
        d = get_driver()
        d.get("https://www.boerse-frankfurt.de/index/EURO STOXX 50")
        element = WebDriverWait(d, 10).until(EC.presence_of_element_located((By.CSS_SELECTOR, "td.widget-table-cell.text-end.change-percent")))
        raw = element.text.strip()
        if not raw:
            return _last_EURO_STOXX_50_change
        value = float(raw.replace("%", "").replace(",", "."))
        if value == 0.0 and _last_EURO_STOXX_50_change not in (None, 0.0):
            return _last_EURO_STOXX_50_change
        _last_EURO_STOXX_50_change = value
        print(f"✔️ EURO STOXX 50 Veränderung: {value:.2f} %")
        return value
    except Exception as e:
        print("⚠️ Fehler beim Laden der EURO STOXX 50-Seite:", e)
        return _last_EURO_STOXX_50_change

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
    Liefert die prozentuale Tagesänderung des passenden Volatilitätsindex:
    Fallback-Kette:
      - EURO STOXX 50: OnVista -> stoxx.com -> Börse Frankfurt
      - Dax:           Börse Frankfurt -> finanztreff.de
      - S&P 500:       Yahoo (VIX)
      - Dow Jones:     Yahoo (VXD)
      - Nasdaq:        Yahoo (VXN)
    """
    try:
        if underlying == "EURO STOXX 50":
            return get_vstoxx_change_stock3(get_driver())                
           

        elif underlying == "Dax":
            val = get_vdax_change()
            if val is None:
                val = get_vdax_change_finanztreff()
            return val

        elif underlying == "S&P 500":
            return get_vix_change_yahoo()

        elif underlying == "Dow Jones":
            return get_vxd_change_yahoo()

        elif underlying == "Nasdaq":
            return get_vxn_change_yahoo()

    except Exception as e:
        print(f"Fehler in get_volatility_change({underlying}): {e}")

    return None



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

@lru_cache(maxsize=8)
def scrape_average_leverage(url_onvista, url_finanzen=None):
    """Liest durchschnittliche Hebelwerte ausschließlich von OnVista (kein Finanzen-Fallback)."""
    print(f"Versuche Daten von OnVista URL abzurufen: {url_onvista}")
    leverages = []
    try:
        d = get_driver()
        d.get(url_onvista)
        WebDriverWait(d, 15).until(EC.presence_of_element_located((By.CSS_SELECTOR, "table tr")))
        WebDriverWait(d, 5).until(lambda drv: "gearingAsk" in drv.page_source or "Hebel" in drv.page_source)
        soup = BeautifulSoup(d.page_source, "html.parser")
        for row in soup.find_all("tr"):
            for cell in row.find_all("td"):
                text = cell.get_text(strip=True)
                try:
                    value = float(text.replace(',', '.'))
                    if 1 <= value <= 200:
                        leverages.append(value)
                        break
                except ValueError:
                    continue
        if leverages:
            avg = sum(leverages) / len(leverages)
            print(f"Gefundene Hebelwerte von OnVista: {leverages}")
            return avg
    except Exception as e:
        print(f"Fehler bei OnVista-Abfrage: {e}")

    print("Keine Hebelwerte gefunden (nur OnVista aktiv).")
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
        ampel_symbol = "🔴"; base_kommentar = "Alarm: Long-Hebel über Short-Hebel - Banken erwarten fallenden Markt,deswegen bieten Sie kleinere Short an"
    elif long_now < short_now:
        ampel_symbol = "🟢"; base_kommentar = "Positiv: Short-Hebel über Long-Hebel - Banken erwarten steigenden Markt,deswegen bieten Sie kleinere Long an"
    else:
        ampel_symbol = "🟡"; base_kommentar = "Neutral: Long- und Short-Hebel gleich"
    thresholds = get_dynamic_thresholds(df_history if df_history is not None else pd.DataFrame())
    rel_delta_long = (long_now - long_prev) / long_prev * 100 * thresholds['leverage_volatility_factor'] if long_prev != 0 else 0
    rel_delta_short = (short_now - short_prev) / short_prev * 100 * thresholds['leverage_volatility_factor'] if short_prev != 0 else 0
    if rel_delta_short <= thresholds['short_crash']:
        ampel_symbol = "🔴"; base_kommentar = f"Crash-Alarm: Shorts ↓{abs(rel_delta_short):.1f}% (Volatilität: {thresholds['leverage_volatility_factor']:.1f}x)"
    elif rel_delta_short <= thresholds['short_warning']:
        ampel_symbol = "🟠"; base_kommentar = f"Frühwarnung: Shorts ↓{abs(rel_delta_short):.1f}% (Schwelle: {thresholds['short_warning']}%)"
    elif rel_delta_long >= thresholds['long_warn']:
        ampel_symbol = "🟠"; base_kommentar = f" Long-Push: {rel_delta_long:.1f}% (Schwelle: {thresholds['long_warn']}%)"
    kommentar = base_kommentar
    if (long_now < long_prev) and (short_now < short_prev):
        kommentar += " | Achtung: Beide Hebel sinken – Banken könnten sich zurückziehen oder hohe Volatilität erwarten"; persistenter_kommentar = kommentar; persistenz_counter = 10
    verhältnis_neu = short_now - long_now
    if verhältnis_vorher * verhältnis_neu < 0:
        kommentar += " | 🔁 Hebel-Kreuzung erkannt – Bankenstruktur hat sich gedreht"; persistenter_kommentar = kommentar; persistenz_counter = 36
    verhältnis_vorher = verhältnis_neu
    try:
        rel_diff = abs(short_now - long_now) / ((abs(short_now) + abs(long_now)) / 2) * 100
        if rel_diff < 9: kommentar += " | Banken unsicher – geringer Unterschied zwischen Long- und Short-Hebel"
    except ZeroDivisionError:
        pass
    if timestamp:
        log_ampel_event(timestamp, rel_delta_long, rel_delta_short, ampel_symbol, kommentar)
        if index_change is not None: log_index_event(timestamp, index_change)
    return kommentar

def determine_ampel_signal(df):
    if len(df) < 1:
        return 0.5, "-", "Warte auf Daten", "-", "-", "-"
    hebel_signal = "Warte auf Daten"
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

def get_ampel1_status(df, selected_underlying):
    if len(df) < 20 or 'volatility_change' not in df.columns:
        return FARBCODES["gray"], 0.5, "Nicht genug Daten. 50 sec warten."
    try:
        df_window = df.iloc[-min(len(df), 654):]
        v_now = df_window['volatility_change'].iloc[-1]
        i_now = df_window['index_change'].iloc[-1]
        timestamp = df_window['timestamp'].iloc[-1]
        schnittzeit = timestamp.strftime("%H:%M")
        vola_min, vola_max = df_window['volatility_change'].min(), df_window['volatility_change'].max()
        rel_pos = (v_now - vola_min) / (vola_max - vola_min) if vola_max != vola_min else 0.5
        minmax_text = f"Min: {vola_min:.2f} %, Max: {vola_max:.2f} %"
        vola_wert = f"{v_now:.2f} %"
        kommentar_vorab = {"Dax":"VDAX","S&P 500":"VIX","EURO STOXX 50":"VSTOXX","Dow Jones":"VXD"}.get(selected_underlying,"VXN")
        if v_now < i_now and rel_pos < 0.6:
            return FARBCODES["green"], rel_pos, f"{kommentar_vorab} – Vola unter Index – Entspannt.(Veränderung: {vola_wert}, {minmax_text})"
        elif v_now < i_now and rel_pos >= 0.75:
            return FARBCODES["orange"], rel_pos, f"{kommentar_vorab} – Vola unter Index (gut), aber steigender Trend.(Veränderung: {vola_wert}, {minmax_text})"
        elif v_now > i_now and rel_pos < 0.45:
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

def _scrape_finanztreff_header(names):
    """
    Liefert dict {Name: %-Change} aus der Header-Tickerleiste.
    names: Iterable von Label-Strings z.B. ("DAX","S&P 500","NASDAQ 100","Dow 30")
    """
    d = get_driver()
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
    """Nur EURO STOXX 50 ('E. Stoxx 50') aus der großen Märkte-Tabelle."""
    d = get_driver()
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



def _ft_accept_cookies_quick(d, timeout=8):
    try:
        WebDriverWait(d, timeout).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        for how, sel in [
            (By.CSS_SELECTOR, "button#onetrust-accept-btn-handler"),
            (By.XPATH, "//button[contains(., 'Akzeptieren') or contains(., 'Zustimmen')]"),
        ]:
            try:
                btn = d.find_element(how, sel)
                if btn.is_displayed(): btn.click(); time.sleep(0.4); break
            except Exception:
                pass
    except Exception:
        pass

def get_vdax_change_finanztreff():
    """
    Fallback für VDAX aus der großen 'Märkte'-Tabelle auf finanztreff.de
    Sucht die Zeile mit 'VDAX' und extrahiert den %-Wert in derselben Zeile.
    """
    try:
        d = get_driver()
        d.get("https://www.finanztreff.de/")
        _ft_accept_cookies_quick(d)
        WebDriverWait(d, 15).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        time.sleep(1.2)  # dynamische Nachladung

        soup = BeautifulSoup(d.page_source, "html.parser")
        target = None
        for t in soup.find_all(string=re.compile(r"\bVDAX\b", re.I)):
            node = t.parent
            for _ in range(5):
                if node and node.name in ("div", "tr"):
                    target = node; break
                node = node.parent
            if target: break
        if not target:
            return None

        row_text = target.get_text(" ", strip=True)
        m = re.search(r"([+-]?\d+[.,]\d+)\s*%", row_text)
        if m:
            val = float(m.group(1).replace(",", "."))
            print(f"✔️ VDAX (finanztreff) Veränderung: {val:.2f} %")
            return val
    except Exception as e:
        print(f"⚠️ VDAX finanztreff Fallback fehlgeschlagen: {e}")
    return None

import html as _html

_last_vstoxx_change_cache = None  # globaler Puffer

def get_vstoxx_change_stoxx_requests(timeout=10):
    """
    VSTOXX von stoxx.com (ohne Selenium).
    Sucht mehrere Muster, inkl. data-daily-change-percent und Text-Fallbacks.
    """
    try:
        headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "de-DE,de;q=0.9,en-US;q=0.8,en;q=0.7",
            "Cache-Control": "no-cache",
        }
        r = requests.get("https://www.stoxx.com/index/v2tx/", headers=headers, timeout=timeout)
        r.raise_for_status()
        html = r.text

        # 1) präzise: <span class="data-daily-change-percent">(+0.77%)</span>
        m = re.search(r'data-daily-change-percent[^>]*>\s*\(([^()%]+)%\)\s*<', html, re.I)
        if m:
            val = float(m.group(1).replace(",", ".").replace("+", "").strip())
            print(f"✔️ VSTOXX (stoxx.com) %: {val:.2f}")
            return val

        # 2) alternative Container-Klassen, z.B. data-current-price-status block
        m = re.search(r'(?:data-current-price-status|data-daily-change-row)[\s\S]{0,500}?\(([^()%]+)%\)', html, re.I)
        if m:
            val = float(m.group(1).replace(",", ".").replace("+", "").strip())
            print(f"✔️ VSTOXX (stoxx.com/alt) %: {val:.2f}")
            return val

        # 3) Text-Fallback: komplette Seite ent-HTMLen und im Umfeld von "Change"/"Last Value" suchen
        text = BeautifulSoup(html, "html.parser").get_text(" ", strip=True)
        text = _html.unescape(text)
        m = re.search(r"(?:Change|Last Value)[^()]{0,150}\(([+-]?\d+[.,]\d+)\s*%\)", text, re.I)
        if m:
            val = float(m.group(1).replace(",", "."))
            print(f"✔️ VSTOXX (stoxx.com/Text) %: {val:.2f}")
            return val

        print("ℹ️ stoxx.com gefunden, aber kein %-Muster erkannt.")
    except Exception as e:
        print(f"⚠️ VSTOXX stoxx.com (requests) fehlgeschlagen: {e}")
    return None



def update_data():
    global last_fetch_time, refresh_interval, selected_underlying
    while not stop_event.is_set():
        current_underlying = selected_underlying
        urls = UNDERLYINGS[current_underlying]
        long_avg = scrape_average_leverage(urls["long"])
        short_avg = scrape_average_leverage(urls["short"])
        index_data = get_index_data(current_underlying)
        index_change, index_display_value = (None, "-")
        if index_data and len(index_data) == 3:
            index_change, index_display_value, _ = index_data

        if index_change is None:
               
            ft_change = get_index_change_from_finanztreff(current_underlying)
            if ft_change is not None:
                index_change = ft_change

        vola_change = get_volatility_change(current_underlying)
        print(f"Volatility change for {current_underlying}: {vola_change}")
        if None not in (long_avg, short_avg, index_change) and abs(index_change) < 10:
            csv_file = get_csv_filename(current_underlying)
            new_data = pd.DataFrame([[
                datetime.now(TZ_BERLIN), long_avg, short_avg, index_change,
                (short_avg/long_avg-1)*100 if (long_avg + short_avg) > 0 else None,
                vola_change
            ]], columns=["timestamp","long_avg","short_avg","index_change","short_vs_long_diff_prozent","volatility_change"])
            if os.path.exists(csv_file):
                df = pd.read_csv(csv_file, parse_dates=['timestamp'], encoding='utf-8')
                if len(df) > 1000: df = df.iloc[-1000:]
                df = pd.concat([df, new_data], ignore_index=True)
            else:
                df = new_data
            df.to_csv(csv_file, index=False, encoding='utf-8', lineterminator='\n')
            last_fetch_time = datetime.now(TZ_BERLIN).strftime("%H:%M:%S")
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
# -----------------------------------------------
# Layout
# -----------------------------------------------
app.layout = html.Div([
    html.Div([
        html.H1("Leverage Lens", id="exit-title", style={
            "fontSize": "56px", "fontWeight": "bold", "textAlign": "center",
            "background": "linear-gradient(90deg, red, orange, yellow, green, blue, violet)",
            "WebkitBackgroundClip": "text", "WebkitTextFillColor": "transparent",
            "cursor": "pointer", "display": "inline-block", "marginRight": "10px"
        }),
        html.Span("v61", style={
            "fontSize": "16px",
            "color": "#666",
            "verticalAlign": "super",
            "fontWeight": "normal"
        })
    ], style={"textAlign": "center", "marginBottom": "20px"}),

    html.Div(
        dcc.Dropdown(
            id='underlying-dropdown',
            options=[{'label': k, 'value': k} for k in UNDERLYINGS.keys()],
            value=selected_underlying,
            style={"width": "300px","fontWeight": "bold","fontSize": "22px"}
        ),
        style={"display": "flex","justifyContent": "center","margin": "19px 0"}
    ),

    html.Div(
        id="index-info",
        children=[
            html.Div(id="last-fetch-time", style={"fontSize": "16px", "color": "#555", "margin": "80px 0 4px 0"}),
            html.Div(id="index-display", style={"fontWeight": "bold"})
        ],
        style={"display": "flex","flexDirection": "column","rowGap": "4px","margin": "10px 0"}
    ),

    html.Img(src=app.get_asset_url("meinbild2.jpg"),
             style={'position': 'absolute','top': '30px','right': '30px','width': 'auto','height': '285px','zIndex': '10'}),

    html.Div([
        dcc.Input(id='interval-input', type='number', value=refresh_interval, min=5, step=1,
                  style={'width': '40px', "fontSize": "18px", "fontWeight": "bold","textAlign": "center"}),
        html.Button("Intervall ändern (Sek)", id="set-interval-btn", style={'marginLeft': '7px', "fontSize": "18px"}),
        html.Button("Alle CSV löschen", id="reset-btn", style={'marginLeft': '7px', "fontSize": "18px"})
    ], style={'margin': '20px 0'}),
    
    # ---- Ton-Schalter (bereinigt) ----
    html.Div([
        dcc.Checklist(
            id="sound-toggle",
            options=[{"label": "🔔", "value": "on"}],
            value=["on"],
            inline=True,
            persistence=True,
            persistence_type="local",
            style={"fontSize": "18px"}
        ),
    ], style={'marginTop': '10px'}),

    # Volatilitäts-Schalter
    html.Div(
        dcc.RadioItems(
            id='volatility-toggle',
            options=[],
            value='off',
            labelStyle={'display': 'block'},
            style={'fontSize': '20px','padding': '6px 10px'},
            inputStyle={"transform": "scale(1.4)", "marginRight": "8px"}
        )
    ),

    dcc.Graph(id='leverage-graph'),
    dcc.Interval(id='interval-component', interval=refresh_interval * 1000, n_intervals=0),
    html.Audio(id="alarm-audio", src="", autoPlay=True, controls=False, style={"display": "none"})
])  # Closing the main html.Div

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

    # Sound-Schalter übernehmen
    sound_on = bool(sound_value) and ("on" in sound_value)
    set_sound_enabled(sound_on)
    alarm_src = ""                      # default: kein Sound

    # Volatilitäts-Schalter übernehmen
    show_volatility = (volatility_toggle == 'on')

    # Bei Wechsel des Underlyings: Thread neu starten
    if selected != selected_underlying:
        selected_underlying = selected
        start_update_thread()

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
            df = pd.DataFrame(columns=["timestamp", "long_avg", "short_avg", "index_change"])
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
        min_val = float(y2_series.min()); max_val = float(y2_series.max())
        span = max_val - min_val; min_range = 1.0; padding = 0.1
        if span < min_range:
            center = (min_val + max_val) / 2.0
            y2_range = [center - min_range / 2.0 - padding, center + min_range / 2.0 + padding]
        else:
            y2_range = [min_val - padding, max_val + padding]
        fig.update_layout(
            title={'text': f"Ø Hebel von Long/Short Turbos ({selected_underlying})",'y': 0.95,'x': 0.5,'xanchor': 'center','yanchor': 'top'},
            xaxis=dict(title='Zeit'),
            yaxis=dict(title='Durchschnittlicher Hebel', side='left', showgrid=True),
            yaxis2=dict(title="Index Veränderung (%)", overlaying='y', side='right', showgrid=False, range=y2_range),
            legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="right", x=1),
            margin=dict(l=50, r=50, b=50, t=80, pad=4), height=500, plot_bgcolor='rgba(240,240,240,0.8)'
        )
    else:
        now = datetime.now(TZ_BERLIN)
        placeholder_text = "Warte auf ausreichende Daten..." if len(df) == 1 else "Warte auf erste Daten..."
        fig.add_annotation(text=placeholder_text, xref="paper", yref="paper", x=0.5, y=0.5, showarrow=False, font=dict(size=16, color="gray"))
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
      
        sofr_bps, _ = get_sofr_proxy_comment()  
        
        if sofr_bps is None:
            sofr_bps = 0
            sofr_text = "SOFR-Proxy: keine Daten."
            
        else:
            if abs(sofr_bps) > 100:
                sofr_text = "Extrem (Systemkrise): >100 bps – Historisch nur in Krisen (2007–2008 bis 465 bps, Corona 2020 ca. 140 bps). Signal: akute Banken-/Fundingkrise."
            elif abs(sofr_bps) >= 70:
                sofr_text = "Kritisch (Liquiditätsstress): 70–100 bps – Banken leihen zögerlich. Meist Vorbote stärkerer Abverkäufe."
            elif abs(sofr_bps) >= 40:
                sofr_text = "Erhöht (Markt wird nervös): 40–70 bps – Leichte Spannungen im Interbankmarkt. Frühwarnsignal für knapper werdende Liquidität."
            elif abs(sofr_bps) >= 10:
                sofr_text = "Normalbereich (kein Stress): 10–40 bps – Typisch in ruhigen Marktphasen."
            else:
                sofr_text = "Unter Normalbereich (<10 bps) – sehr ruhige Interbank-Lage."    
        
            
            
            
            #
# Miniampel/Farbe bestimmen
        if abs(sofr_bps) >= 70:
            sofr_mini_color = FARBCODES["red"]
            sofr_mini_emoji = "🔴"
        elif abs(sofr_bps) >= 40:
            sofr_mini_color = FARBCODES["orange"]
            sofr_mini_emoji = "🟠"
        else:
            sofr_mini_color = FARBCODES["green"]
            sofr_mini_emoji = "🟢"
# Ampel 2 hart überschreiben, wenn Stress hoch        
        if abs(sofr_bps) >= 70:
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

    # RSI / Ampel 4
    rsi_ticker = get_rsi_for_underlying(selected)
    if rsi_ticker:
        rsi_value = get_rsi(rsi_ticker)
    else:
        rsi_value = None
    if rsi_value is not None:
        rsi_status, rsi_title, rsi_kommentar = bewerte_rsi_ampel(rsi_value)
    else:
        rsi_status, rsi_title, rsi_kommentar = FARBCODES["gray"], "RSI nicht verfügbar", "Keine ausreichenden Daten für RSI"

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
                    html.Div(f"Kommentar: {kommentar}", style={"marginLeft": "40px","fontSize": "90%","color": "#333","fontStyle": "normal"}),
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
                html.Div(style={"width": "35px","height": "35px","borderRadius": "50%","backgroundColor": rsi_status,"display": "inline-block","marginRight": "15px","marginTop": "4px","boxShadow": "0 0 8px 2px rgba(255, 255, 255, 0.5)","border": "2px solid #666","boxSizing": "border-box"}),
                html.Div([
                    html.Div(f"Ampel 4: {rsi_title} (8 Tage)", style={"fontSize": "100%","fontWeight": "bold"}),
                    html.Div("Erkennt: Überkaufte (RSI ≥70 %) oder überverkaufte (RSI ≤30 %) Märkte", style={"marginLeft": "20px","fontSize": "90%","color": "#333"}),
                    html.Div(f"Kommentar: {rsi_kommentar}", style={"marginLeft": "40px","fontSize": "90%","color": "#333"}),
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
        pd.DataFrame(columns=["timestamp", "long_avg", "short_avg", "index_change"]).to_csv(file, index=False, encoding='utf-8', lineterminator='\n')
    for fname in ["log_ampel.csv", "log_index.csv"]:
        path = os.path.join(CSV_FOLDER, fname)
        if os.path.exists(path):
            os.remove(path)
    return 0

def cleanup():
    global _DRIVER, _TMP_PROFILE_DIR
    if _DRIVER is not None:
        try:
            _DRIVER.quit()
        except:
            pass
        _DRIVER = None
    if _TMP_PROFILE_DIR and os.path.exists(_TMP_PROFILE_DIR):
        try:
            shutil.rmtree(_TMP_PROFILE_DIR)
        except:
            pass

atexit.register(cleanup)

import webbrowser, threading

@app.callback(
    Output("exit-title", "children"),
    Input("exit-title", "n_clicks"),
    prevent_initial_call=True
)
def close_app(n_clicks):
    os._exit(0)   # beendet das Programm sofort


if __name__ == "__main__":
    start_update_thread()
    threading.Timer(0.8, lambda: webbrowser.open("http://127.0.0.1:8050")).start()
    try:
        app.run(debug=False, host="127.0.0.1", port=8050, use_reloader=False)
    except OSError as e:
        if "Address already in use" in str(e):
            print(f"Port 8050 is already in use. Trying port 8051...")
            app.run(debug=False, host="127.0.0.1", port=8051, use_reloader=False)
        else:
            raise e
