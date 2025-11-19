import json
import urllib.request
import platform
import hashlib
import threading
import time
import tkinter as tk
from tkinter import messagebox
from pathlib import Path
import shutil
import sys
import os

# Wird von LeverageLens gesetzt:
# CURRENT_VERSION
# VERSION_URL
# BUILD_FLAVOR (1=DAX, 0=FULL)


###############################
# SHA256 Prüffunktion
###############################
def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


###############################
# JSON laden
###############################
def fetch_latest_info() -> dict | None:
    try:
        with urllib.request.urlopen(VERSION_URL, timeout=5) as r:
            text = r.read().decode("utf-8")
        return json.loads(text)
    except Exception as e:
        print(f"[Update] Fehler beim Laden von VERSION_URL: {e}")
        return None


###############################
# Download-URL je nach OS wählen
###############################
def get_platform_download_url(info: dict) -> str | None:
    system = platform.system().lower()
    if "windows" in system:
        return info.get("windows_url")
    if "linux" in system:
        return info.get("linux_url")
    print(f"[Update] Plattform nicht unterstützt: {system}")
    return None


###############################
# Update prüfen
###############################
def check_for_update() -> dict | None:
    info = fetch_latest_info()
    if not info:
        return None

    remote_ver = str(info.get("version", "")).strip()
    if not remote_ver:
        print("[Update] JSON enthält keine Version.")
        return None

    if remote_ver == CURRENT_VERSION:
        return None

    print(f"[Update] Neue Version gefunden: {remote_ver}")
    return info


###############################
# Download + SHA256 prüfen
###############################
def download_update(info: dict) -> Path | None:
    url = get_platform_download_url(info)
    if not url:
        return None

    exe_path = Path(sys.argv[0]).resolve()
    out_dir = exe_path.parent
    remote_ver = str(info.get("version", "")).strip()

    system = platform.system().lower()
    if "windows" in system:
        suffix = ".exe"
    else:
        suffix = "_linux"

    out_name = f"{exe_path.stem}_{remote_ver}{suffix}"
    out_path = out_dir / out_name

    print(f"[Update] Lade herunter: {url} → {out_path}")

    try:
        with urllib.request.urlopen(url, timeout=30) as r, open(out_path, "wb") as f:
            shutil.copyfileobj(r, f)
    except Exception as e:
        print(f"[Update] Download fehlgeschlagen: {e}")
        return None

    # -------------------------------------------------
    # SHA256-Prüfung (plattformabhängig: Windows / Linux)
    # -------------------------------------------------
    expected_sha = None
    if "windows" in system:
        expected_sha = info.get("sha256_windows")
    elif "linux" in system:
        expected_sha = info.get("sha256_linux")

    if expected_sha:
        try:
            local_sha = sha256_file(out_path)
        except Exception as e:
            print(f"[Update] SHA256-Berechnung fehlgeschlagen: {e}")
            out_path.unlink(missing_ok=True)
            return None

        if local_sha.lower() != expected_sha.lower():
            print("[Update] SHA256-Prüfung fehlgeschlagen – Datei wird gelöscht.")
            out_path.unlink(missing_ok=True)
            return None

        print("[Update] SHA256 OK.")

    # Linux: ausführbar machen
    if "linux" in system:
        try:
            out_path.chmod(out_path.stat().st_mode | 0o111)
        except Exception as e:
            print(f"[Update] chmod +x fehlgeschlagen: {e}")

    print(f"[Update] Update gespeichert: {out_path}")
    return out_path



###############################
# GUI: Dialog anzeigen
###############################
def show_update_dialog(info: dict):
    """
    Zeigt den Update-Dialog:
    - 'Nein'  -> Dialog schließt, keine Aktion
    - 'Ja'    -> Download, Hinweis, Programmende
    """
    # WICHTIG: Tk-Root pro Dialog anlegen und sicher wieder zerstören
    root = tk.Tk()
    root.withdraw()  # kein Hauptfenster

    remote_ver = info.get("version", "???")
    answer = messagebox.askyesno(
        "Update verfügbar",
        (
            f"Eine neue Version ({remote_ver}) ist verfügbar.\n\n"
            "Möchten Sie diese jetzt herunterladen?"
        ),
        parent=root
    )

    if not answer:
        # Benutzer hat auf „Nein“ geklickt -> einfach schließen
        root.destroy()
        return

    # Benutzer hat „Ja“ gewählt -> Download starten
    file = download_update(info)
    if not file:
        messagebox.showerror(
            "Update",
            "Update fehlgeschlagen.\nBitte versuchen Sie es später erneut.",
            parent=root
        )
        root.destroy()
        return

    # Erfolgreich geladen – Hinweis + programmatisches Beenden
    messagebox.showinfo(
        "Update",
        (
            "Update wurde erfolgreich heruntergeladen.\n\n"
            f"Datei:\n{file}\n\n"
            "Das Programm kann jetzt beendet werden.\n"
            "Bitte starten Sie anschließend die neue Datei manuell."
        ),
        parent=root
    )

    root.destroy()
    sys.exit(0)



###############################
# Delayed Update-Check
###############################
def check_update_later(delay_sec=20):
    """
    Startet die Updateprüfung zeitverzögert in einem Thread.
    Verhindert Freeze beim Start.
    """
    def _worker():
        time.sleep(delay_sec)
        info = check_for_update()
        if info:
            show_update_dialog(info)

    threading.Thread(target=_worker, daemon=True).start()
