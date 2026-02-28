#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# ===============================================
# 
# Version V44.2.21 - Extraction robuste du lien captcha
# ===============================================

import os
import json
import asyncio
import time
import random
import re
import requests
import unicodedata
import subprocess
import base64
import platform
import threading
import hashlib
import tempfile
from datetime import datetime, date
from colorama import Fore, Style, init
from telethon import TelegramClient
from telethon.errors import MessageIdInvalidError, FloodWaitError
from json.decoder import JSONDecodeError

# Imports pour cloudscraper (optionnel, non utilisé ici)
try:
    import cloudscraper
    CLOUDSCRAPER_AVAILABLE = True
except ImportError:
    CLOUDSCRAPER_AVAILABLE = False

# uiautomator2
try:
    import uiautomator2 as u2
    from uiautomator2.exceptions import UiObjectNotFoundError, ConnectError
except ImportError:
    print(Fore.RED + Style.BRIGHT + "[❌] uiautomator2 manquant. Installez-le avec 'pip install uiautomator2'." + Style.NORMAL)
    exit(1)

# OpenCV optionnel
try:
    import cv2
    import numpy as np
    OPENCV_AVAILABLE = True
except ImportError:
    OPENCV_AVAILABLE = False
    print("ℹ️ OpenCV non installé, prétraitement désactivé.")


class Colors:
    # Couleurs de texte
    PURPLE = '\033[1;35m'
    RED = '\033[1;91m'
    GREEN = '\033[1;92m'
    BLACK = '\033[1;30m'
    YELLOW = '\033[1;33m'
    CYAN = '\033[1;96m'
    WHITE = '\033[1;97m'
    BLUE = '\033[1;34m'
    ORANGE = '\x1b[38;5;214m'  # Orange
    ORANGE2 = '\033[38;5;208m'
    
    # Styles
    RESET = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'
    
    # Arrière-plans
    CYAN_BG = '\033[7;96m'
    RED_BG = '\033[7;91m'
    GREEN_BG = '\033[7;92m'
    RED_BG_BRIGHT = '\033[1;41m'
    CYAN_BG_BRIGHT = '\033[1;46m'

# Variables globales pour la compatibilité
vi = Colors.PURPLE
R = Colors.RED
V = Colors.GREEN
black = Colors.BLACK
J = Colors.YELLOW
C = Colors.CYAN
B = Colors.WHITE
Bl = Colors.BLUE
o = Colors.ORANGE
O = Colors.ORANGE2
S = Colors.RESET
c = Colors.CYAN_BG
r = Colors.RED_BG
v = Colors.GREEN_BG
ro = Colors.RED_BG_BRIGHT
co = Colors.CYAN_BG_BRIGHT

# Gestion des jours restants
DAYS_LEFT = None  # Doit être défini avant la fonction

# Mode de délais: False = nouveaux délais (lents), True = anciens délais (rapides)
DELAY_MODE = False
USE_OLD_DELAYS = False  # Pour wait_after_task: True = 1s, sinon 1s aussi (pause entre tâches)

def get_days_left_str():
    """Retourne une chaîne formatée indiquant le temps restant avant l'expiration."""
    global DAYS_LEFT
    if DAYS_LEFT is not None:
        if DAYS_LEFT < 0:
            return f"{Colors.RED}[EXPIRE]{Colors.RESET}"
        return f"{Colors.YELLOW}{DAYS_LEFT} jour(s) restant(s){Colors.RESET}"
    return f"{Colors.GREEN}Abonnement actif{Colors.RESET}"

logo=f"""
{o}═════════════════════════════════════════
{vi}┌────────────────────────────────┐
│   _     _     _     _     _    │
│  / \\   / \\   / \\   / \\   / \\   │
│ ( F ) ( A ) ( R ) ( E ) ( S )  │
│  \\/   \\/   \\/   \\/   \\_/   │
│                                │
│                                │
│                                │
│                                │
└────────────────────────────────┘{V}2025
{o}═════════════════════════════════════════
{B}[{V}•{B}]{o}Développeur    {B}==  {vi}Alex le développeur
{B}[{V}•{B}]{o}Version       {B}==  {vi}Payant 
{B}[{V}•{B}]{o}FARES         {B}==  {vi}ALEX
{B}[{V}•{B}]{o}Nant Fare     {B}==  {vi}SmmKingdomTask {V}BEST{J} 
{o}═════════════════════════════════════════
\033[1;96m[Licence]\033[0m {get_days_left_str()}
"""

clien=[]
var1=[]
var2=[]
var=[]
compte=[]
comptes=[]
accounts_with_no_tasks = []
rq=requests.session()
session = "sessions"
BASE_DIR = os.path.join(os.path.dirname(__file__), "SmmKingdomTask")
if not os.path.exists(BASE_DIR):
    os.makedirs(BASE_DIR)
ON_HOLD_FILE = os.path.join(BASE_DIR, "on_hold_accounts.txt")
LOGIN_REQUIRED_FILE = os.path.join(BASE_DIR, "login_required.txt")

# Initialize IG session directory early
IG_SESSION_DIR = os.path.join(BASE_DIR, "ig_sessions")
os.makedirs(IG_SESSION_DIR, exist_ok=True)

# SUPPRESSION DES LIMITES D'ACTIONS - Plus de restrictions
# Le bot peut maintenant effectuer un nombre illimité d'actions
# sans être bloqué par des limites horaires ou journalières
ACTION_TYPES = ['follow', 'like', 'comment', 'story', 'video']
ON_HOLD_ACTION_FILE = os.path.join(BASE_DIR, 'on_hold_action.json')

# Ajout d'un fichier pour stocker les comptes temporairement bloqués (10 min)
TEMP_BLOCK_FILE = os.path.join(BASE_DIR, 'temp_block.json')

# --- Gestion de la clé de licence et vérification d'accès ---
SERVER_URL = "http://botfares3.pythonanywhere.com"  # Assure-toi que l'URL commence par http(s)
API_KEY_FILE = "api_key.json"
SESSION_FILE = "session_id.txt"

# Variable globale pour stocker le nombre de jours restants
EXPIRES_AT = None

# Fichier audio d'alerte Security check
ALERT_SOUND_FILE = "alerte.wav"

# Génère une empreinte unique pour la machine (ou l'utilisateur)
def get_machine_fingerprint():
    base = platform.node() + platform.system() + platform.processor()
    return hashlib.sha256(base.encode()).hexdigest()

def get_or_create_session_id():
    if os.path.exists(SESSION_FILE):
        with open(SESSION_FILE, "r") as f:
            return f.read().strip()
    else:
        session_id = get_machine_fingerprint()
        with open(SESSION_FILE, "w") as f:
            f.write(session_id)
        return session_id


# --- ALARME PUSH NTFY ---
def send_push_alarm_ntfy(topic, title, message):
    url = f"https://ntfy.sh/{topic}"
    headers = {"Title": title, "Priority": "5", "Tags": "rotating_light"}
    try:
        response = requests.post(url, data=message.encode('utf-8'), headers=headers)
        if response.status_code == 200:
            print("📱 Alarme push envoyée avec succès.")
        else:
            print(f"❌ Erreur notification push: {response.status_code} {response.text}")
    except Exception as ex:
        print(f"❌ Erreur lors de l'envoi de l'alarme push: {ex}")


# --- Ajout de la gestion de période d'essai et notification expiration ---
def get_or_create_api_key():
    if os.path.exists(API_KEY_FILE):
        try:
            with open(API_KEY_FILE, "r") as f:
                data = json.load(f)
        except Exception:
            data = {}

        api_key = data.get("api_key")
        username = data.get("username")
        if api_key:
            return api_key

        if username:
            session_id = get_or_create_session_id()
            try:
                resp = requests.post(SERVER_URL + "/register", json={"session_id": session_id, "test_days": 0.02, "username": username})
                if resp.status_code == 200:
                    data = resp.json()
                    api_key = data.get("api_key")
                    if api_key:
                        with open(API_KEY_FILE, "w") as f:
                            json.dump({"api_key": api_key, "username": username}, f)
                        print("✅ Clé API générée et enregistrée :", api_key)
                        return api_key
                else:
                    print("Erreur lors de la génération de la clé API :", resp.text)
            except Exception as e:
                print("Erreur de connexion au serveur (tentative d'enregistrement) :", e)
            return None

    # No api key file found: prompt user and try to register
    username = input("Entrez votre nom d'utilisateur Telegram : ").strip()
    session_id = get_or_create_session_id()
    try:
        resp = requests.post(SERVER_URL + "/register", json={"session_id": session_id, "test_days": 0.02, "username": username})
        if resp.status_code == 200:
            data = resp.json()
            api_key = data.get("api_key")
            if api_key:
                with open(API_KEY_FILE, "w") as f:
                    json.dump({"api_key": api_key, "username": username}, f)
                print("✅ Clé API générée et enregistrée :", api_key)
                return api_key
        else:
            print("Erreur lors de la génération de la clé API :", resp.text)
    except Exception as e:
        print("Erreur de connexion au serveur :", e)

    # Fallback: save username only
    try:
        with open(API_KEY_FILE, "w") as f:
            json.dump({"username": username}, f)
        print("⚠ Enregistrement seulement du nom d'utilisateur ; pas de clé API générée.")
    except Exception as e:
        print("⚠ Impossible d'enregistrer le nom d'utilisateur localement :", e)

    return None

def initialize_api_key():
    """Appelle get_or_create_api_key() pour assurer qu'un api_key existe ou que l'utilisateur soit invité."""
    api_key = get_or_create_api_key()
    if api_key:
        print("API key présente ou générée avec succès.")
    else:
        print("Pas de clé API disponible pour le moment. Vous pouvez la générer via l'option manuelle.")

def check_access():
    global DAYS_LEFT, EXPIRES_AT
    api_key = get_or_create_api_key()
    session_id = get_or_create_session_id()
    try:
        response = requests.post(SERVER_URL + "/verify", json={
            "api_key": api_key,
            "session_id": session_id
        })
        data = response.json()

        # --- Notification push un jour avant expiration ---
        expires_at = data.get("expires_at")
        username = data.get("username", "user")
        if expires_at:
            try:
                exp_dt = datetime.fromisoformat(expires_at)
                now = datetime.utcnow()
                days_left = (exp_dt - now).days
                DAYS_LEFT = days_left
                EXPIRES_AT = exp_dt
                if 0 < days_left <= 1:
                    send_push_alarm_ntfy(
                        topic="botpayant-licence",
                        title="Alerte expiration licence",
                        message=f"La licence du bot pour {username} expire dans moins de 24h !"
                    )
            except Exception:
                pass

        if data.get("access") is True:
            if DAYS_LEFT is not None:
                if DAYS_LEFT < 1:
                    # Convert to minutes for display
                    if EXPIRES_AT is not None:
                        hours_left = (EXPIRES_AT - datetime.utcnow()).total_seconds() / 3600
                        if hours_left < 1:
                            minutes_left = int((EXPIRES_AT - datetime.utcnow()).total_seconds() / 60)
                            print(f"\033[1;92m[Licence] Minutes restantes sur l'essai : {minutes_left} minute(s)\033[0m")
                        else:
                            print(f"\033[1;92m[Licence] Heures restantes sur l'essai : {int(hours_left)} heure(s)\033[0m")
                else:
                    print(f"\033[1;92m[Licence] Jours restants sur l'abonnement : {DAYS_LEFT} jour(s)\033[0m")
            else:
                print(f"\033[1;92m[Licence] Abonnement actif\033[0m")
            return True

        # Cas bloquants
        reason = data.get("reason", "unknown")
        if reason == "expired":
            print("⛔ Abonnement expiré.")
        elif reason == "disabled":
            print("⛔ Clé désactivée.")
        elif reason == "already_running":
            print("⛔ Cette clé est déjà utilisée sur un autre appareil.")
        else:
            print("⛔ Accès refusé :", reason)
        return False

    except Exception as e:
        print("❌ Erreur de connexion :", e)
        return False

# À placer tout en haut du script principal
if not check_access():
    exit()


init(autoreset=True)

# ==================================
# CONFIGURATION LICENCE
# ==================================

# --- CONFIGURATION GROQ ---
GROQ_CONFIG_FILE = "groq_config.json"
DEFAULT_GROQ_MODEL = "meta-llama/llama-4-maverick-17b-128e-instruct"
groq_api_key = ""
groq_model = DEFAULT_GROQ_MODEL

# --- IDENTIFIANTS TELEGRAM ---
API_ID_DEFAULT = 30425664
API_HASH_DEFAULT = "790c5b2fd259fdcda140abc1a44c19d3"
BOT_USERNAME = "SmmKingdomTasksBot"
SESSION_NAME = "SmmKingdomTasksBot"

TELEGRAM_API_ID = API_ID_DEFAULT
TELEGRAM_API_HASH = API_HASH_DEFAULT
TELEGRAM_PHONE_NUMBER = ""

# --- VARIABLES GLOBALES ---
client = None
client_status_user = "Déconnecté"
DEVICE_IP = None
ACCOUNTS_FILE = "accounts.json"
CONFIG_FILE = "config.json"
DEFAULT_DEVICE_IP = "127.0.0.1:7912"
APK_PACKAGE_HOST = "com.waxmoon.ma.gp"
TERMUX_PACKAGE = "com.termux"
LICENSE_FILE = "license.json"
STOP_TASK_FLAG = False
BASE_DIR = os.path.join(os.path.dirname(__file__), "SmmKingdomTask")
os.makedirs(BASE_DIR, exist_ok=True)

# Filtres d'actions (Like / Commentaire)
DISABLE_LIKE = False
DISABLE_COMMENT = False

# Fichier pour sauvegarder le HTML de vérification (optionnel)
VERIFICATION_HTML_FILE = os.path.join(BASE_DIR, "code.txt")
# Fichier pour enregistrer le dernier captcha réussi (emoji + answer)
SECURITY_LAST_PASSED_FILE = os.path.join(BASE_DIR, "security_last_passed.json")

# Multibot: api.multibot.in (key=apikey, method=turnstile, in.php / res.php)
CAPSOLVER_CONFIG_FILE = "capsolver_config.json"
CAPSOLVER_API_KEY = "qYS90qZQPo4K4TOzcQRKgyOQ5ecDfC9M"  # Clé Multibot par défaut
CAPSOLVER_SITEKEY = "0x4AAAAAABlpNiu45fH48l-Z"  # websiteKey/sitekey Turnstile
MULTIBOT_API_HOST = "https://api.multibot.in"

# --- DÉLAIS CONFIGURABLES (inchangés) ---
DEFAULT_TERMUX_BRING_TO_FRONT_DELAY = 1.5
DEFAULT_PRE_ACTION_STABILITY_TIME = 3
DEFAULT_HOST_APP_OPEN_DELAY = 5.0
DEFAULT_URL_OPEN_TO_CLONE_SELECT_DELAY = 3.0
DEFAULT_CLONE_OPEN_DELAY = 10
DEFAULT_SWIPE_ACTUALISATION_DELAY = 1.0
DEFAULT_POPUP_CLOSE_DELAY = 3.0
DEFAULT_MENU_CLOSE_BACK_DELAY = 2.0
DEFAULT_POST_ACTION_DELAY = 3.0
DEFAULT_COMMENT_PANEL_OPEN_DELAY = 3.0
DEFAULT_COMMENT_PANEL_BACK_DELAY = 0.5
DEFAULT_COMMENT_INPUT_ACTIVATE_DELAY = 1.0
DEFAULT_COMMENT_SEND_KEYS_DELAY = 2.0
DEFAULT_TERMUX_RE_ACQUIRE_FOCUS_DELAY = 5.0
DEFAULT_COMMENT_AFTER_BUBBLE_DELAY = 0.5
DEFAULT_COMMENT_KEYBOARD_OPEN_DELAY = 0.5
DEFAULT_COMMENT_PASTE_MENU_DELAY = 0.5
DEFAULT_COMMENT_PASTE_DELAY = 0.1
DEFAULT_CAPTCHA_OUVRIR_DELAY = 2.0
DEFAULT_CAPTCHA_WAIT_DELAY = 15.0
DEFAULT_CAPTCHA_VERIFY_DELAY = 3.0

TERMUX_BRING_TO_FRONT_DELAY = DEFAULT_TERMUX_BRING_TO_FRONT_DELAY
PRE_ACTION_STABILITY_TIME = DEFAULT_PRE_ACTION_STABILITY_TIME
HOST_APP_OPEN_DELAY = DEFAULT_HOST_APP_OPEN_DELAY
URL_OPEN_TO_CLONE_SELECT_DELAY = DEFAULT_URL_OPEN_TO_CLONE_SELECT_DELAY
CLONE_OPEN_DELAY = DEFAULT_CLONE_OPEN_DELAY
SWIPE_ACTUALISATION_DELAY = DEFAULT_SWIPE_ACTUALISATION_DELAY
POPUP_CLOSE_DELAY = DEFAULT_POPUP_CLOSE_DELAY
MENU_CLOSE_BACK_DELAY = DEFAULT_MENU_CLOSE_BACK_DELAY
POST_ACTION_DELAY = DEFAULT_POST_ACTION_DELAY
COMMENT_PANEL_OPEN_DELAY = DEFAULT_COMMENT_PANEL_OPEN_DELAY
COMMENT_PANEL_BACK_DELAY = DEFAULT_COMMENT_PANEL_BACK_DELAY
COMMENT_INPUT_ACTIVATE_DELAY = DEFAULT_COMMENT_INPUT_ACTIVATE_DELAY
COMMENT_SEND_KEYS_DELAY = DEFAULT_COMMENT_SEND_KEYS_DELAY
TERMUX_RE_ACQUIRE_FOCUS_DELAY = DEFAULT_TERMUX_RE_ACQUIRE_FOCUS_DELAY
COMMENT_AFTER_BUBBLE_DELAY = DEFAULT_COMMENT_AFTER_BUBBLE_DELAY
COMMENT_KEYBOARD_OPEN_DELAY = DEFAULT_COMMENT_KEYBOARD_OPEN_DELAY
COMMENT_PASTE_MENU_DELAY = DEFAULT_COMMENT_PASTE_MENU_DELAY
COMMENT_PASTE_DELAY = DEFAULT_COMMENT_PASTE_DELAY
CAPTCHA_OUVRIR_DELAY = DEFAULT_CAPTCHA_OUVRIR_DELAY
CAPTCHA_WAIT_DELAY = DEFAULT_CAPTCHA_WAIT_DELAY
CAPTCHA_VERIFY_DELAY = DEFAULT_CAPTCHA_VERIFY_DELAY

# ======================================================================
# FONCTIONS DE CONFIGURATION GROQ
# ======================================================================
def load_groq_config():
    global groq_api_key, groq_model
    if os.path.exists(GROQ_CONFIG_FILE):
        try:
            with open(GROQ_CONFIG_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            groq_api_key = data.get("api_key", "")
            groq_model = data.get("model", DEFAULT_GROQ_MODEL)
        except:
            pass

def save_groq_config():
    data = {"api_key": groq_api_key, "model": groq_model}
    with open(GROQ_CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
    print(Fore.GREEN + "✅ Configuration Groq sauvegardée." + Style.NORMAL)

load_groq_config()

# ======================================================================
# FONCTIONS DE PRÉTRAITEMENT D'IMAGE
# ======================================================================
def preprocess_image(image_path, output_path="temp_processed.png"):
    if not OPENCV_AVAILABLE:
        return image_path
    try:
        img = cv2.imread(image_path, cv2.IMREAD_GRAYSCALE)
        if img is None:
            return image_path
        img = cv2.resize(img, None, fx=2, fy=2, interpolation=cv2.INTER_CUBIC)
        img = cv2.equalizeHist(img)
        _, img = cv2.threshold(img, 120, 255, cv2.THRESH_BINARY)
        cv2.imwrite(output_path, img)
        return output_path
    except Exception as e:
        print(f"⚠️ Erreur prétraitement : {e}")
        return image_path

# ======================================================================
# FONCTION D'EXTRACTION DU SYMBOLE CIBLE
# ======================================================================
def extract_emoji_and_math_from_message(message_text):
    print(Fore.CYAN + f"[🔍] Extraction du cible après 'by link'..." + Style.NORMAL)
    target_emoji = None
    print(Fore.YELLOW + f"[📝] Message analysé:\n{message_text[:300]}..." + Style.NORMAL)
    pattern = r'by link\s*([^\s\n])'
    match = re.search(pattern, message_text, re.IGNORECASE)
    if match:
        target_emoji = match.group(1).strip()
    else:
        pattern2 = r'by link\s*([^\s\n,\.!?]+)'
        match2 = re.search(pattern2, message_text, re.IGNORECASE)
        if match2:
            target_emoji = match2.group(1).strip()
    if target_emoji:
        target_emoji = target_emoji.strip('.,!?;:')
    if not target_emoji:
        print(Fore.YELLOW + "[🔄] Recherche ligne par ligne..." + Style.NORMAL)
        lines = message_text.split('\n')
        for i, line in enumerate(lines):
            if 'by link' in line.lower():
                print(Fore.CYAN + f"[🔍] Ligne {i+1} contient 'by link': {line}" + Style.NORMAL)
                parts = line.lower().split('by link')
                if len(parts) > 1:
                    after_by_link = parts[1].strip()
                    if after_by_link:
                        first_part = after_by_link.split()[0] if after_by_link.split() else after_by_link
                        target_emoji = first_part.strip('.,!?;:')
                        print(Fore.GREEN + f"[✅] Cible extrait de la ligne: '{target_emoji}'" + Style.NORMAL)
                        break
    if not target_emoji:
        common_targets = ['●', '○', '■', '□', '▲', '△', '★', '☆', '🔥', '⭐', '❤️', '✨', '🌟', '⚠']
        for symbol in common_targets:
            if symbol in message_text:
                target_emoji = symbol
                print(Fore.YELLOW + f"[⚠️] Cible déduit (symbole trouvé): '{target_emoji}'" + Style.NORMAL)
                break
        if not target_emoji:
            print(Fore.RED + "[❌] Impossible d'extraire le symbole cible. Abandon." + Style.NORMAL)
            return None, None
    try:
        uname = unicodedata.name(target_emoji)
        print(Fore.GREEN + f"[🎯] Cible détectée : {target_emoji} ({uname})" + Style.NORMAL)
    except:
        print(Fore.GREEN + f"[🎯] Cible détectée : {target_emoji}" + Style.NORMAL)
    # Indice d'opération : le cible est un EMOJI de vérification, pas le signe de calcul
    operation_hint = None
    msg_lower = message_text.lower()
    if any(w in msg_lower for w in ("difference", "subtract", "soustraire", "soustraction", "minus", "moins")):
        operation_hint = "subtraction"
        print(Fore.CYAN + "[🧮] Indice message : opération = soustraction (difference)." + Style.NORMAL)
    elif any(w in msg_lower for w in ("sum", "addition", "add", "additionner", "plus")):
        operation_hint = "addition"
        print(Fore.CYAN + "[🧮] Indice message : opération = addition (sum)." + Style.NORMAL)
    elif any(w in msg_lower for w in ("product", "multiply", "multiplication", "multiplier")):
        operation_hint = "multiplication"
        print(Fore.CYAN + "[🧮] Indice message : opération = multiplication." + Style.NORMAL)
    elif any(w in msg_lower for w in ("division", "divide", "diviser")):
        operation_hint = "division"
        print(Fore.CYAN + "[🧮] Indice message : opération = division." + Style.NORMAL)
    print(Fore.CYAN + "[🧮] Le cible sert UNIQUEMENT à sélectionner l'image ; ce n'est PAS le signe de calcul." + Style.NORMAL)
    return target_emoji, operation_hint

# ======================================================================
# FONCTION GROQ MULTI-IMAGES (CORRIGÉE)
# ======================================================================
def solve_multiple_images_groq(image_paths, target_symbol, operation_hint=None):
    """
    Envoie les trois images en une seule requête et retourne (image_num, result).
    target_symbol = emoji/symbole de VÉRIFICATION pour sélectionner l'image (PAS l'opérateur mathématique).
    operation_hint = indication du message (subtraction, addition, etc.) pour éviter de confondre le cible avec ×.
    """
    if not groq_api_key:
        print(Fore.RED + "[❌] Clé API Groq non configurée." + Style.NORMAL)
        return None, None

    # Prétraiter chaque image
    b64_images = []
    temp_files = []
    for path in image_paths:
        processed = preprocess_image(path)
        temp_files.append(processed if processed != path else None)
        try:
            with open(processed, "rb") as f:
                b64 = base64.b64encode(f.read()).decode("utf-8")
                b64_images.append(b64)
        except Exception as e:
            print(Fore.RED + f"[❌] Erreur lecture image {path}: {e}" + Style.NORMAL)
            for tf in temp_files:
                if tf and os.path.exists(tf):
                    os.remove(tf)
            return None, None

    for tf in temp_files:
        if tf and os.path.exists(tf):
            os.remove(tf)

    try:
        target_name = unicodedata.name(target_symbol).lower()
    except:
        target_name = "symbole"

    hint_line = ""
    if operation_hint == "subtraction":
        hint_line = (
            "IMPORTANT: Le message indique que l'opération est une SOUSTRACTION (difference). "
            "Les deux nombres doivent être soustraits (premier - second). Le symbole cible peut ressembler à × mais c'est l'emoji de vérification, pas le signe multiplier.\n"
        )
    elif operation_hint == "addition":
        hint_line = "IMPORTANT: Le message indique que l'opération est une ADDITION (sum). Utilise + entre les deux nombres.\n"
    elif operation_hint == "multiplication":
        hint_line = "IMPORTANT: Le message indique que l'opération est une MULTIPLICATION.\n"
    elif operation_hint == "division":
        hint_line = "IMPORTANT: Le message indique que l'opération est une DIVISION.\n"

    prompt = (
        f"Voici trois images (image1, image2, image3). Chacune contient une expression mathématique et un symbole.\n"
        f"Le symbole CIBLE (emoji de vérification) est {target_symbol} (un {target_name}). Il sert UNIQUEMENT à identifier quelle image contient le défi.\n\n"
        "DISTINCTION OBLIGATOIRE — ne pas confondre :\n"
        "- X ou × (lettre x / croix) = EMOJI DE VÉRIFICATION (le cible). Il sert uniquement à sélectionner l'image. Ce n'est JAMAIS l'opérateur du calcul.\n"
        "- * (astérisque) = OPÉRATEUR de multiplication dans l'expression. Pour écrire une multiplication, utilise *.\n"
        "Donc : dans l'image, le X ou × est l'emoji à trouver ; pour le calcul, l'opérateur multiplier est * (pas le X). Si tu vois seulement un X/× entre deux nombres, c'est le cible, pas l'opérateur — cherche le vrai opérateur (souvent - pour la différence) ou applique l'indice du message.\n\n"
        + hint_line +
        "Trouve l'image qui contient le symbole cible. Dans cette image, repère les NOMBRES et le VRAI signe d'opération.\n"
        "Règles opérateurs (pour l'expression et le résultat) :\n"
        "- MOINS : trait horizontal (-) → soustraction.\n"
        "- PLUS : croix avec barre verticale et horizontale (+) → addition.\n"
        "- MULTIPLICATION : opérateur * (astérisque). Le X/× visible est l'emoji cible, pas *.\n"
        "- DIVISION : / ou ÷.\n"
        "Réponds UNIQUEMENT au format JSON suivant, sans aucun autre texte :\n"
        "{\"image\": numero (1, 2 ou 3), \"expression\": \"l'expression\", \"result\": nombre}\n"
        "Si aucune image ne contient le symbole, réponds {\"image\": null, \"expression\": null, \"result\": null}."
    )

    content = [{"type": "text", "text": prompt}]
    for b64 in b64_images:
        content.append({
            "type": "image_url",
            "image_url": {"url": f"data:image/png;base64,{b64}"}
        })

    payload = {
        "model": groq_model,
        "messages": [{"role": "user", "content": content}],
        "temperature": 0,
        "max_completion_tokens": 150,
    }

    try:
        response = requests.post(
            "https://api.groq.com/openai/v1/chat/completions",
            headers={"Authorization": f"Bearer {groq_api_key}", "Content-Type": "application/json"},
            json=payload,
            timeout=60
        )
    except Exception as e:
        print(Fore.RED + f"[❌] Erreur requête Groq : {e}" + Style.NORMAL)
        return None, None

    if response.status_code != 200:
        print(Fore.RED + f"[❌] API Groq a retourné {response.status_code} : {response.text[:200]}" + Style.NORMAL)
        return None, None

    data = response.json()
    try:
        content = data["choices"][0]["message"]["content"].strip()
    except (KeyError, IndexError):
        print(Fore.RED + "[❌] Réponse Groq mal formée :", data + Style.NORMAL)
        return None, None

    # Debug (optionnel)
    # print(Fore.CYAN + f"[🔍] Réponse brute : {content}" + Style.NORMAL)

    try:
        json_match = re.search(r'\{.*\}', content, re.DOTALL)
        if json_match:
            result_data = json.loads(json_match.group())
        else:
            result_data = json.loads(content)
    except json.JSONDecodeError:
        print(Fore.YELLOW + "[⚠️] La réponse n'est pas un JSON valide." + Style.NORMAL)
        return None, None

    image_num = result_data.get("image")
    result = result_data.get("result")
    if result is not None:
        result = str(result)
    return image_num, result

# ======================================================================
# NOUVELLES FONCTIONS DE TÉLÉCHARGEMENT
# ======================================================================
async def get_previous_security_images(reference_msg, max_photos=3):
    """
    Récupère jusqu'à max_photos messages images (photos) avant le message de référence.
    Utilise le client Telethon déjà connecté.
    """
    photos = []
    async for m in client.iter_messages(BOT_USERNAME, offset_id=reference_msg.id, reverse=False, limit=20):
        if m.id >= reference_msg.id:
            continue
        if getattr(m, "photo", None) or (getattr(m, "media", None) and getattr(m.media, "photo", None)):
            photos.append(m)
            if len(photos) >= max_photos:
                break
    return photos

async def download_security_images(msg):
    """
    Télécharge les images captcha précédant le message de vérification.
    - msg : le message Telegram contenant le Security check.
    - Les images sont sauvegardées dans BASE_DIR (SmmKingdomTask/).
    Retourne la liste des chemins locaux des images téléchargées.
    """
    security_images = await get_previous_security_images(msg, max_photos=3)
    downloaded_paths = []
    for imsg in security_images:
        try:
            save_path = os.path.join(BASE_DIR, f"security_img_{imsg.id}.jpg")
            path = await client.download_media(imsg, file=save_path)
            print(Fore.GREEN + f"[📥] Image téléchargée : {path}" + Style.NORMAL)
            downloaded_paths.append(path)
        except Exception as e:
            print(Fore.RED + f"[⚠️] Erreur téléchargement image {imsg.id}: {e}" + Style.NORMAL)
    return downloaded_paths

# ======================================================================
# FONCTION D'EXTRACTION ROBUSTE DU LIEN DE VÉRIFICATION
# ======================================================================
def extract_verification_link(message_obj):
    """Extrait le lien de vérification caché dans le bouton Start verification (version ultra robuste)"""
    if not message_obj:
        print(Fore.RED + "[❌] Message vide" + Style.NORMAL)
        return None

    print(Fore.CYAN + f"[🔍] Extraction du lien depuis le message #{message_obj.id}..." + Style.NORMAL)

    # --- 1. Vérifier les boutons (url directe) ---
    if hasattr(message_obj, 'buttons') and message_obj.buttons:
        print(Fore.CYAN + f"[🔘] Analyse de {len(message_obj.buttons)} ligne(s) de boutons..." + Style.NORMAL)
        for row_idx, row in enumerate(message_obj.buttons):
            for btn_idx, button in enumerate(row):
                # Vérifier l'attribut url
                if hasattr(button, 'url') and button.url:
                    print(Fore.GREEN + f"[✅] URL trouvée dans button.url: {button.url}" + Style.NORMAL)
                    return button.url
                # Vérifier callback_data (parfois contient l'URL encodée)
                if hasattr(button, 'callback_data') and button.callback_data:
                    data = button.callback_data
                    if isinstance(data, bytes):
                        data = data.decode('utf-8', errors='ignore')
                    print(Fore.YELLOW + f"[🔎] Callback data: {data[:200]}..." + Style.NORMAL)
                    # Chercher une URL dans callback_data
                    urls = re.findall(r'https?://[^\s]+', data)
                    if urls:
                        print(Fore.GREEN + f"[✅] URL extraite de callback_data: {urls[0]}" + Style.NORMAL)
                        return urls[0]
                # Vérifier le texte du bouton (parfois c'est un lien)
                if hasattr(button, 'text') and button.text:
                    text_urls = re.findall(r'https?://[^\s]+', button.text)
                    if text_urls:
                        print(Fore.GREEN + f"[✅] URL trouvée dans le texte du bouton: {text_urls[0]}" + Style.NORMAL)
                        return text_urls[0]

    # --- 2. Vérifier les entités (MessageEntityTextUrl ou MessageEntityUrl) ---
    if hasattr(message_obj, 'entities') and message_obj.entities:
        print(Fore.CYAN + f"[🔍] Analyse de {len(message_obj.entities)} entité(s)..." + Style.NORMAL)
        for entity in message_obj.entities:
            if hasattr(entity, 'url') and entity.url:
                print(Fore.GREEN + f"[✅] URL trouvée dans entity.url: {entity.url}" + Style.NORMAL)
                return entity.url
            # Entité de type URL (lien dans le texte)
            if hasattr(entity, 'type') and entity.type == 'url' and hasattr(message_obj, 'message'):
                start = entity.offset
                end = entity.offset + entity.length
                if end <= len(message_obj.message):
                    link = message_obj.message[start:end]
                    print(Fore.GREEN + f"[✅] URL trouvée dans entité texte: {link}" + Style.NORMAL)
                    return link

    # --- 3. Chercher dans le texte brut du message ---
    if hasattr(message_obj, 'message') and message_obj.message:
        print(Fore.CYAN + "[🔍] Recherche dans le texte brut..." + Style.NORMAL)
        # URLs http(s)
        urls = re.findall(r'https?://[^\s]+', message_obj.message)
        if urls:
            print(Fore.GREEN + f"[✅] URL trouvée dans le texte: {urls[0]}" + Style.NORMAL)
            return urls[0]
        # Liens t.me ou telegram.me
        tg_urls = re.findall(r't\.me/[^\s]+|telegram\.me/[^\s]+', message_obj.message)
        if tg_urls:
            link = tg_urls[0]
            if not link.startswith('http'):
                link = 'https://' + link
            print(Fore.GREEN + f"[✅] Lien Telegram trouvé: {link}" + Style.NORMAL)
            return link

    # --- 4. Dernier recours : examiner la représentation du message (parfois l'info est cachée) ---
    print(Fore.YELLOW + "[⚠️] Aucun lien trouvé, tentative d'extraction via str(message)..." + Style.NORMAL)
    msg_str = str(message_obj)
    urls = re.findall(r'https?://[^\s]+', msg_str)
    if urls:
        print(Fore.GREEN + f"[✅] URL extraite de la représentation: {urls[0]}" + Style.NORMAL)
        return urls[0]

    print(Fore.RED + "[❌] Aucun lien de vérification trouvé après toutes les tentatives." + Style.NORMAL)
    return None


# ======================================================================
# RÉSOLUTION TURNSTILE VIA MULTIBOT (API requests, pas Chrome)
# ======================================================================
def _solve_turnstile_with_multibot(sitekey: str, pageurl: str) -> str:
    """Résout Cloudflare Turnstile avec l'API Multibot (api.multibot.in).
    Envoi: POST in.php multipart (key, method=turnstile, sitekey, pageurl, json=1)
    Récupération: GET res.php?key=KEY&id=ID&json=1

    Returns:
        Token Turnstile ou None en cas d'échec.
    """
    if not CAPSOLVER_API_KEY:
        print(Fore.RED + "[❌] Clé API Turnstile non configurée." + Style.NORMAL)
        return None

    host = MULTIBOT_API_HOST.rstrip("/")
    try:
        print(Fore.CYAN + "[🔄] Création de la tâche Turnstile via Multibot..." + Style.NORMAL)
        files = {
            "key": (None, CAPSOLVER_API_KEY),
            "method": (None, "turnstile"),
            "sitekey": (None, sitekey),
            "pageurl": (None, pageurl),
            "json": (None, "1"),
        }
        r = requests.post(f"{host}/in.php", files=files, timeout=30)
        resp_data = r.json()
        if not resp_data.get("status"):
            err = resp_data.get("request", str(resp_data))
            print(Fore.RED + f"[❌] Création tâche Turnstile échouée: {err}" + Style.NORMAL)
            return None

        captcha_id = resp_data.get("request", "")
        if not captcha_id:
            print(Fore.RED + "[❌] Pas d'ID de tâche retourné par Multibot." + Style.NORMAL)
            return None

        print(Fore.CYAN + f"[⏳] Attente résolution Turnstile (id: {str(captcha_id)[:12]}...)..." + Style.NORMAL)
        for attempt in range(40):
            time.sleep(3)
            res = requests.get(
                f"{host}/res.php",
                params={"key": CAPSOLVER_API_KEY, "id": captcha_id, "json": "1"},
                timeout=30,
            )
            j = res.json()
            if j.get("status"):
                token = j.get("request", "")
                if token and "CAPCHA_NOT_READY" not in str(token).upper() and "ERROR" not in str(token).upper():
                    print(Fore.GREEN + f"[✅] Token Turnstile obtenu (tentative {attempt+1})!" + Style.NORMAL)
                    return str(token).strip()
            req = j.get("request", "")
            if req and "ERROR" in str(req).upper() and "NOT_READY" not in str(req).upper():
                print(Fore.RED + f"[❌] Turnstile échoué: {req}" + Style.NORMAL)
                return None
        print(Fore.RED + "[❌] Timeout résolution Turnstile (>2 min)." + Style.NORMAL)
        return None
    except Exception as ex:
        print(Fore.RED + f"[❌] Erreur Turnstile Multibot: {ex.__class__.__name__} - {ex}" + Style.NORMAL)
        return None


def _solve_turnstile_with_capsolver(sitekey: str, pageurl: str) -> str:
    """Résout Turnstile via Multibot (alias pour compatibilité)."""
    return _solve_turnstile_with_multibot(sitekey, pageurl)


# ======================================================================
# FONCTION DE RÉSOLUTION DU CAPTCHA VIA MULTIBOT + REQUESTS (pas Chrome)
# ======================================================================
async def handle_telegram_captcha_direct_link_with_math(security_message_obj, math_result):
    """
    Gère la résolution du captcha après avoir obtenu le résultat mathématique.
    Résolution Turnstile via Multibot API, soumission via requests/cloudscraper (pas Chrome/ADB).
    - security_message_obj : le message Telegram contenant le bouton de vérification
    - math_result : le résultat du calcul (string)
    """
    print(Fore.YELLOW + "[🔗] Résolution du captcha avec résultat: " + str(math_result) + Style.NORMAL)

    # 1) Extraire le lien de vérification
    verification_url = extract_verification_link(security_message_obj)
    if not verification_url:
        print(Fore.RED + "[❌] Aucun lien de vérification trouvé." + Style.NORMAL)
        return False
    print(Fore.GREEN + f"[🔗] Lien trouvé: {verification_url}" + Style.NORMAL)

    result_value = str(math_result).strip()
    message_text = security_message_obj.message or ""
    target_emoji, _ = extract_emoji_and_math_from_message(message_text)

    # 2) Résoudre Turnstile avec Multibot (attendre que le captcha soit résolu)
    turnstile_token = None
    if CAPSOLVER_API_KEY:
        turnstile_token = await asyncio.to_thread(
            _solve_turnstile_with_capsolver, CAPSOLVER_SITEKEY, verification_url
        )
    else:
        print(Fore.YELLOW + "[⚠️] Multibot non configuré. Soumission sans token Turnstile." + Style.NORMAL)

    # 3) Appeler le site via cloudscraper, sauvegarder HTML, soumettre answer + token
    if not CLOUDSCRAPER_AVAILABLE:
        print(Fore.RED + "[❌] cloudscraper requis pour la soumission. Installez: pip install cloudscraper" + Style.NORMAL)
        return False

    try:
        scraper = cloudscraper.create_scraper()
        print(Fore.CYAN + "[🌐] Requête GET initiale sur l'URL de vérification (cloudscraper)..." + Style.NORMAL)
        resp = scraper.get(verification_url, timeout=60)
        html = resp.text

        try:
            os.makedirs(os.path.dirname(VERIFICATION_HTML_FILE), exist_ok=True)
            with open(VERIFICATION_HTML_FILE, "w", encoding="utf-8") as f:
                f.write(html)
            print(Fore.GREEN + f"[📝] HTML de vérification sauvegardé dans '{VERIFICATION_HTML_FILE}'." + Style.NORMAL)
        except Exception as e:
            print(Fore.RED + f"[⚠️] Impossible de sauvegarder le HTML: {e.__class__.__name__} - {e}" + Style.NORMAL)

        # Soumission: answer + cf-turnstile-response (Submit)
        data = {"answer": result_value}
        if turnstile_token:
            data["cf-turnstile-response"] = turnstile_token

        success_any = False
        submit_resp = None
        for method in ["post", "get"]:
            try:
                if method == "post":
                    submit_resp = scraper.post(verification_url, data=data, timeout=60)
                else:
                    submit_resp = scraper.get(verification_url, params=data, timeout=60)
                text_lower = (submit_resp.text or "").lower()
                # Chercher des indicateurs réels de succès/échec
                success_keywords = ["verification passed", "success", "completed", "correct"]
                fail_keywords = ["wrong", "incorrect", "failed", "invalid", "error"]
                if any(k in text_lower for k in success_keywords):
                    success_any = True
                    print(Fore.GREEN + "[✅] Vérification RÉUSSIE confirmée!" + Style.NORMAL)
                elif any(k in text_lower for k in fail_keywords):
                    print(Fore.RED + f"[❌] Réponse incorrecte: {submit_resp.text[:200]}" + Style.NORMAL)
                    success_any = False
                    continue
                if submit_resp.status_code in (200, 302) or "success" in text_lower:
                    success_any = True
                    # Quand "Verification passed" / "Captcha was completed successfully" : stocker l'emoji + réponse
                    if "verification passed" in text_lower or "captcha was completed successfully" in text_lower:
                        try:
                            passed_data = {
                                "emoji": target_emoji if target_emoji else None,
                                "answer": result_value,
                                "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
                            }
                            with open(SECURITY_LAST_PASSED_FILE, "w", encoding="utf-8") as f:
                                json.dump(passed_data, f, ensure_ascii=False, indent=2)
                            print(Fore.GREEN + f"[💾] Emoji et réponse enregistrés ({SECURITY_LAST_PASSED_FILE})." + Style.NORMAL)
                        except Exception as e:
                            print(Fore.YELLOW + f"[⚠️] Impossible d'enregistrer security_last_passed: {e}" + Style.NORMAL)
                    print(Fore.GREEN + f"[✅] Challenge soumis avec succès (answer={result_value}, méthode={method})." + Style.NORMAL)
                    break
            except Exception as e:
                print(Fore.YELLOW + f"[⚠️] Soumission {method} échouée: {e}" + Style.NORMAL)
                continue

        if success_any:
            return True
        print(Fore.RED + "[❌] Aucune soumission réussie (POST/GET)." + Style.NORMAL)
        return False
    except Exception as e:
        print(Fore.RED + f"[❌] Erreur soumission captcha: {e.__class__.__name__} - {e}" + Style.NORMAL)
        return False

def _play_alert_sound():
    """Joue le fichier audio d'alerte via termux-media-player."""
    if not os.path.exists(ALERT_SOUND_FILE):
        print(Fore.YELLOW + f"[⚠️] Fichier audio '{ALERT_SOUND_FILE}' introuvable. Alerte audio ignorée." + Style.NORMAL)
        return

    def play_sound():
        try:
            path = os.path.abspath(ALERT_SOUND_FILE)
            subprocess.Popen(
                ["termux-media-player", "play", path],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                start_new_session=True
            )
        except FileNotFoundError:
            print(Fore.YELLOW + "[⚠️] termux-media-player non disponible. Installez: pkg install termux-api" + Style.NORMAL)
        except Exception as e:
            print(Fore.RED + f"[⚠️] Erreur lecture audio: {e.__class__.__name__} - {e}" + Style.NORMAL)

    threading.Thread(target=play_sound, daemon=True).start()


# ======================================================================
# TRAITEMENT DU MESSAGE DE SÉCURITÉ (VERSION FINALE ROBUSTE)
# ======================================================================
async def process_security_check_message(security_message_obj):
    print(Fore.YELLOW + "[🛡️] TRAITEMENT MESSAGE DE SÉCURITÉ COMPLET" + Style.NORMAL)
    _play_alert_sound()
    try:
        # Vérification connexion Telegram
        if not client or not client.is_connected():
            print(Fore.RED + "[❌] Client Telegram déconnecté." + Style.NORMAL)
            return False

        # Extraction du symbole cible
        message_text = security_message_obj.message or ""
        target_emoji, operation_hint = extract_emoji_and_math_from_message(message_text)
        if not target_emoji:
            print(Fore.RED + "[❌] Symbole cible non trouvé. Abandon du security check." + Style.NORMAL)
            return False

        print(Fore.GREEN + f"[🎯] Cible identifié: '{target_emoji}'" + Style.NORMAL)

        
        
        # Téléchargement des 3 images avec timeout global de 30s
        image_paths = []
        try:
            # On utilise asyncio.wait_for pour limiter le temps total
            image_paths = await asyncio.wait_for(
                download_security_images(security_message_obj),
                timeout=30.0
            )
        except asyncio.TimeoutError:
            print(Fore.RED + "[❌] Timeout global de 30s dépassé pour le téléchargement des 3 images." + Style.NORMAL)
            return False
        except Exception as e:
            print(Fore.RED + f"[❌] Erreur lors du téléchargement : {e}" + Style.NORMAL)
            return False

        # Vérifier que les 3 images ont bien été téléchargées
        if len(image_paths) < 3:
            print(Fore.RED + f"[❌] Seulement {len(image_paths)} image(s) téléchargée(s) sur 3." + Style.NORMAL)
            # Nettoyer les fichiers partiels
            for p in image_paths:
                try: os.remove(p)
                except: pass
            return False

        print(Fore.GREEN + f"[✅] 3 images téléchargées avec succès." + Style.NORMAL)

        # Analyse Groq
        print(Fore.CYAN + "[🔍] Analyse comparative des 3 images avec Groq..." + Style.NORMAL)
        image_num, math_result = await asyncio.to_thread(solve_multiple_images_groq, image_paths, target_emoji, operation_hint)

        # Nettoyage des fichiers temporaires
        for p in image_paths:
            try: os.remove(p)
            except: pass

        if image_num is None or math_result is None:
            print(Fore.RED + "[❌] Groq n'a pas pu extraire le résultat." + Style.NORMAL)
            return False

        print(Fore.GREEN + f"[✅] Image {image_num} sélectionnée, résultat: {math_result}" + Style.NORMAL)

        # Résolution du captcha via Multibot + requests (pas Chrome/ADB)
        success = await handle_telegram_captcha_direct_link_with_math(
            security_message_obj,
            math_result,
        )

        if success:
            print(Fore.GREEN + "[✅] Captcha résolu avec succès!" + Style.NORMAL)
            return True
        else:
            print(Fore.RED + "[❌] Échec du captcha" + Style.NORMAL)
            return False
            
    except Exception as e:
        print(Fore.RED + f"[❌] Erreur critique: {e}" + Style.NORMAL)
        import traceback
        traceback.print_exc()
        return False

# ======================================================================
# FONCTIONS ADB (inchangées, mais on inclut stable_adb_connect)
# ======================================================================
def check_adb_port():
    global DEVICE_IP
    if DEVICE_IP == "127.0.0.1:7912":
        print(Fore.YELLOW + "[⚠️] Port ADB non-standard détecté: 7912" + Style.NORMAL)
        try:
            subprocess.run(["adb", "kill-server"], capture_output=True, timeout=2)
            subprocess.run(["adb", "start-server"], capture_output=True, timeout=2)
            subprocess.run(["adb", "connect", "127.0.0.1:5555"], capture_output=True, timeout=2)
            result = subprocess.run(["adb", "devices"], capture_output=True, text=True, timeout=5)
            if "127.0.0.1:5555" in result.stdout and "device" in result.stdout:
                DEVICE_IP = "127.0.0.1:5555"
                print(Fore.GREEN + f"[✔] Changé vers port standard: {DEVICE_IP}" + Style.NORMAL)
                config = load_config()
                if 'device_ips' in config and config['device_ips']:
                    config['device_ips'][0] = DEVICE_IP
                    save_config(config)
        except Exception as e:
            print(Fore.YELLOW + f"[ℹ] Utilisation du port actuel: {DEVICE_IP}" + Style.NORMAL)

async def stable_adb_connect(max_retries=3):
    for attempt in range(max_retries):
        try:
            print(Fore.YELLOW + f"[🔌] Tentative de connexion ADB {attempt+1}/{max_retries}..." + Style.NORMAL)
            if attempt > 0:
                try:
                    subprocess.run(["adb", "reconnect", DEVICE_IP.split(':')[0]], capture_output=True, timeout=2)
                    await asyncio.sleep(0.1)
                except:
                    pass
            d = await asyncio.to_thread(u2.connect, DEVICE_IP)
            info = await asyncio.to_thread(lambda: d.info)
            print(Fore.GREEN + f"[✔] ADB connecté: {info.get('model', 'N/A')}" + Style.NORMAL)
            return d
        except (ConnectError, ConnectionRefusedError, ConnectionAbortedError) as e:
            print(Fore.RED + f"[❌] Échec connexion ADB: {e.__class__.__name__}" + Style.NORMAL)
            if attempt < max_retries - 1:
                print(Fore.YELLOW + f"[🔄] Reconnexion dans 1s..." + Style.NORMAL)
                await asyncio.sleep(1)
            else:
                raise Exception(f"Échec connexion ADB après {max_retries} tentatives")
    return None

async def adb_watchdog():
    while True:
        try:
            result = subprocess.run(["adb", "devices"], capture_output=True, text=True, timeout=3)
            if DEVICE_IP not in result.stdout or "offline" in result.stdout:
                print(Fore.RED + "[⚠️] ADB offline détecté, reconnexion..." + Style.NORMAL)
                subprocess.run(["adb", "reconnect", DEVICE_IP.split(':')[0]], capture_output=True)
                await asyncio.sleep(0.5)
            await asyncio.sleep(0.3)
        except Exception as e:
            await asyncio.sleep(0.5)

def adb_copy_text_simple(text):
    try:
        escaped_text = text.replace('"', '\\"').replace('$', '\\$').replace('`', '\\`')
        cmd = f'termux-clipboard-set "{escaped_text}"'
        result = subprocess.run(cmd, shell=True, capture_output=True, timeout=3)
        if result.returncode == 0:
            print(Fore.GREEN + f"[📋] Texte copié via Termux:API ({len(text)} caractères)" + Style.NORMAL)
            return True
        else:
            print(Fore.YELLOW + f"[⚠️] Termux:API copy échoué, code: {result.returncode}" + Style.NORMAL)
            return False
    except Exception as e:
        print(Fore.YELLOW + f"[⚠️] Erreur Termux:API copy: {e}" + Style.NORMAL)
        return False

def backup_copy_method(text):
    try:
        escaped_text = text.replace('"', '\\"').replace('$', '\\$').replace('`', '\\`')
        cmd = f'am broadcast -a com.termux.api.ClipboardSet -e text "{escaped_text}"'
        result = subprocess.run(cmd, shell=True, capture_output=True, timeout=3)
        return result.returncode == 0
    except Exception as e:
        print(Fore.YELLOW + f"[⚠️] Backup copy échoué: {e}" + Style.NORMAL)
        return False


async def kill_multi_app(d=None):
    """Tue le processus Multi App (com.waxmoon.ma.gp) après chaque tâche."""
    try:
        # Via uiautomator2
        if d:
            await asyncio.to_thread(d.app_stop, APK_PACKAGE_HOST)
            print(Fore.YELLOW + f"[🔪] Multi App ({APK_PACKAGE_HOST}) tué via u2." + Style.NORMAL)
        else:
            # Via ADB shell directement
            subprocess.run(
                ["adb", "-s", DEVICE_IP, "shell", "am", "force-stop", APK_PACKAGE_HOST],
                capture_output=True, timeout=5
            )
            print(Fore.YELLOW + f"[🔪] Multi App ({APK_PACKAGE_HOST}) tué via ADB shell." + Style.NORMAL)
    except Exception as e:
        print(Fore.YELLOW + f"[⚠️] Erreur kill Multi App: {e}" + Style.NORMAL)
# ======================================================================
# FONCTIONS DE GESTION DE LICENCE (inchangées)
# ======================================================================


# ======================================================================
# FONCTIONS DE GESTION DE CONFIGURATION ET D'IP (inchangées)
# ======================================================================
def load_config():
    global DEVICE_IP, TELEGRAM_API_ID, TELEGRAM_API_HASH, TELEGRAM_PHONE_NUMBER
    global TERMUX_BRING_TO_FRONT_DELAY, PRE_ACTION_STABILITY_TIME, HOST_APP_OPEN_DELAY, URL_OPEN_TO_CLONE_SELECT_DELAY, CLONE_OPEN_DELAY, SWIPE_ACTUALISATION_DELAY, POPUP_CLOSE_DELAY, MENU_CLOSE_BACK_DELAY, POST_ACTION_DELAY, COMMENT_PANEL_OPEN_DELAY, COMMENT_PANEL_BACK_DELAY, COMMENT_INPUT_ACTIVATE_DELAY, COMMENT_SEND_KEYS_DELAY, TERMUX_RE_ACQUIRE_FOCUS_DELAY
    global COMMENT_AFTER_BUBBLE_DELAY, COMMENT_KEYBOARD_OPEN_DELAY, COMMENT_PASTE_MENU_DELAY, COMMENT_PASTE_DELAY
    global CAPTCHA_OUVRIR_DELAY, CAPTCHA_WAIT_DELAY, CAPTCHA_VERIFY_DELAY
    global DISABLE_LIKE, DISABLE_COMMENT

    config = {}
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, 'r') as f:
                config = json.load(f)
        except (json.JSONDecodeError, FileNotFoundError):
            pass

    TELEGRAM_API_ID = config.get('telegram_api_id', API_ID_DEFAULT)
    TELEGRAM_API_HASH = config.get('telegram_api_hash', API_HASH_DEFAULT)
    TELEGRAM_PHONE_NUMBER = config.get('telegram_phone_number', "")

    TERMUX_BRING_TO_FRONT_DELAY = config.get('delay_termux_front', DEFAULT_TERMUX_BRING_TO_FRONT_DELAY)
    PRE_ACTION_STABILITY_TIME = config.get('delay_pre_action_stability', DEFAULT_PRE_ACTION_STABILITY_TIME)
    HOST_APP_OPEN_DELAY = config.get('delay_host_app_open', DEFAULT_HOST_APP_OPEN_DELAY)
    URL_OPEN_TO_CLONE_SELECT_DELAY = config.get('delay_url_clone_select', DEFAULT_URL_OPEN_TO_CLONE_SELECT_DELAY)
    CLONE_OPEN_DELAY = config.get('delay_clone_open', DEFAULT_CLONE_OPEN_DELAY)
    SWIPE_ACTUALISATION_DELAY = config.get('delay_swipe_actualisation', DEFAULT_SWIPE_ACTUALISATION_DELAY)
    POPUP_CLOSE_DELAY = config.get('delay_popup_close', DEFAULT_POPUP_CLOSE_DELAY)
    MENU_CLOSE_BACK_DELAY = config.get('delay_menu_close_back', DEFAULT_MENU_CLOSE_BACK_DELAY)
    POST_ACTION_DELAY = config.get('delay_post_action', DEFAULT_POST_ACTION_DELAY)
    COMMENT_PANEL_OPEN_DELAY = config.get('delay_comment_panel_open', DEFAULT_COMMENT_PANEL_OPEN_DELAY)
    COMMENT_PANEL_BACK_DELAY = config.get('delay_comment_panel_back', DEFAULT_COMMENT_PANEL_BACK_DELAY)
    COMMENT_INPUT_ACTIVATE_DELAY = config.get('delay_comment_input_activate', DEFAULT_COMMENT_INPUT_ACTIVATE_DELAY)
    COMMENT_SEND_KEYS_DELAY = config.get('delay_comment_send_keys', DEFAULT_COMMENT_SEND_KEYS_DELAY)
    TERMUX_RE_ACQUIRE_FOCUS_DELAY = config.get('delay_termux_refocus', DEFAULT_TERMUX_RE_ACQUIRE_FOCUS_DELAY)
    COMMENT_AFTER_BUBBLE_DELAY = config.get('delay_comment_after_bubble', DEFAULT_COMMENT_AFTER_BUBBLE_DELAY)
    COMMENT_KEYBOARD_OPEN_DELAY = config.get('delay_comment_keyboard_open', DEFAULT_COMMENT_KEYBOARD_OPEN_DELAY)
    COMMENT_PASTE_MENU_DELAY = config.get('delay_comment_paste_menu', DEFAULT_COMMENT_PASTE_MENU_DELAY)
    COMMENT_PASTE_DELAY = config.get('delay_comment_paste', DEFAULT_COMMENT_PASTE_DELAY)
    DISABLE_LIKE = config.get('disable_like', False)
    DISABLE_COMMENT = config.get('disable_comment', False)
    CAPTCHA_OUVRIR_DELAY = config.get('delay_captcha_ouvrir', DEFAULT_CAPTCHA_OUVRIR_DELAY)
    CAPTCHA_WAIT_DELAY = config.get('delay_captcha_wait', DEFAULT_CAPTCHA_WAIT_DELAY)
    CAPTCHA_VERIFY_DELAY = config.get('delay_captcha_verify', DEFAULT_CAPTCHA_VERIFY_DELAY)

    if 'device_ips' not in config or not isinstance(config['device_ips'], list):
        config['device_ips'] = [DEFAULT_DEVICE_IP]

    DEVICE_IP = config['device_ips'][0] if config['device_ips'] else DEFAULT_DEVICE_IP
    return config

def save_config(config_data):
    global TELEGRAM_API_ID, TELEGRAM_API_HASH, TELEGRAM_PHONE_NUMBER
    global TERMUX_BRING_TO_FRONT_DELAY, PRE_ACTION_STABILITY_TIME, HOST_APP_OPEN_DELAY, URL_OPEN_TO_CLONE_SELECT_DELAY, CLONE_OPEN_DELAY, SWIPE_ACTUALISATION_DELAY, POPUP_CLOSE_DELAY, MENU_CLOSE_BACK_DELAY, POST_ACTION_DELAY, COMMENT_PANEL_OPEN_DELAY, COMMENT_PANEL_BACK_DELAY, COMMENT_INPUT_ACTIVATE_DELAY, COMMENT_SEND_KEYS_DELAY, TERMUX_RE_ACQUIRE_FOCUS_DELAY
    global COMMENT_AFTER_BUBBLE_DELAY, COMMENT_KEYBOARD_OPEN_DELAY, COMMENT_PASTE_MENU_DELAY, COMMENT_PASTE_DELAY
    global CAPTCHA_OUVRIR_DELAY, CAPTCHA_WAIT_DELAY, CAPTCHA_VERIFY_DELAY
    global DISABLE_LIKE, DISABLE_COMMENT

    config_data['telegram_api_id'] = TELEGRAM_API_ID
    config_data['telegram_api_hash'] = TELEGRAM_API_HASH
    config_data['telegram_phone_number'] = TELEGRAM_PHONE_NUMBER

    config_data['delay_termux_front'] = TERMUX_BRING_TO_FRONT_DELAY
    config_data['delay_pre_action_stability'] = PRE_ACTION_STABILITY_TIME
    config_data['delay_host_app_open'] = HOST_APP_OPEN_DELAY
    config_data['delay_url_clone_select'] = URL_OPEN_TO_CLONE_SELECT_DELAY
    config_data['delay_clone_open'] = CLONE_OPEN_DELAY
    config_data['delay_swipe_actualisation'] = SWIPE_ACTUALISATION_DELAY
    config_data['delay_popup_close'] = POPUP_CLOSE_DELAY
    config_data['delay_menu_close_back'] = MENU_CLOSE_BACK_DELAY
    config_data['delay_post_action'] = POST_ACTION_DELAY
    config_data['delay_comment_panel_open'] = COMMENT_PANEL_OPEN_DELAY
    config_data['delay_comment_panel_back'] = COMMENT_PANEL_BACK_DELAY
    config_data['delay_comment_input_activate'] = COMMENT_INPUT_ACTIVATE_DELAY
    config_data['delay_comment_send_keys'] = COMMENT_SEND_KEYS_DELAY
    config_data['delay_termux_refocus'] = TERMUX_RE_ACQUIRE_FOCUS_DELAY
    config_data['delay_comment_after_bubble'] = COMMENT_AFTER_BUBBLE_DELAY
    config_data['delay_comment_keyboard_open'] = COMMENT_KEYBOARD_OPEN_DELAY
    config_data['delay_comment_paste_menu'] = COMMENT_PASTE_MENU_DELAY
    config_data['delay_comment_paste'] = COMMENT_PASTE_DELAY
    config_data['delay_captcha_ouvrir'] = CAPTCHA_OUVRIR_DELAY
    config_data['delay_captcha_wait'] = CAPTCHA_WAIT_DELAY
    config_data['delay_captcha_verify'] = CAPTCHA_VERIFY_DELAY
    config_data['disable_like'] = DISABLE_LIKE
    config_data['disable_comment'] = DISABLE_COMMENT

    with open(CONFIG_FILE, "w") as f:
        json.dump(config_data, f, indent=2)

def load_json(file):
    if not os.path.exists(file): return []
    try:
        with open(file, 'r') as f: return json.load(f)
    except (json.JSONDecodeError, FileNotFoundError): return []

def save_json(file, data):
    with open(file, "w") as f:
        json.dump(data, f, indent=2)

load_config()

# ======================================================================
# UTILITAIRE : SLEEP AVEC VÉRIFICATION D'ARRÊT
# ======================================================================
async def sleep_with_check(duration):
    global STOP_TASK_FLAG
    sleep_step = 0.1
    steps = int(duration / sleep_step)
    for _ in range(steps):
        if STOP_TASK_FLAG:
            return True
        await asyncio.sleep(sleep_step)
    if STOP_TASK_FLAG:
        return True
    return False

async def get_user_input(prompt):
    global STOP_TASK_FLAG
    try:
        user_input = await asyncio.to_thread(input, prompt)
        if user_input.strip().upper() == 'S':
            STOP_TASK_FLAG = True
            print(Fore.RED + Style.BRIGHT + "\n[🛑 SIGNAL D'ARRÊT REÇU] Arrêt du cycle en cours..." + Style.NORMAL)
        return user_input
    except EOFError:
        return ""
    except KeyboardInterrupt:
        STOP_TASK_FLAG = True
        print(Fore.RED + Style.BRIGHT + "\n[🛑 SIGNAL D'ARRÊT REÇU] Arrêt du cycle en cours..." + Style.NORMAL)
        return "S"

# ======================================================================
# FONCTIONS DE DÉTECTION DE MESSAGES (inchangées)
# ======================================================================
def is_message_to_ignore(text):
    if not text:
        return False
    cleaned_text = '\n'.join([line.strip() for line in text.split('\n') if line.strip()])
    if cleaned_text == "🔴 Account" or cleaned_text.lower() == "🔴 account":
        print(Fore.YELLOW + "[❌ IGNORÉ] Message 1: '🔴 Account'" + Style.NORMAL)
        return True
    if cleaned_text == "🟡 Account" or cleaned_text.lower() == "🟡 account":
        print(Fore.YELLOW + "[❌ IGNORÉ] Message 2: '🟡 Account'" + Style.NORMAL)
        return True
    if "============" in cleaned_text and ("❗️ Account" in cleaned_text or "❗️ account" in cleaned_text.lower()):
        print(Fore.YELLOW + "[❌ IGNORÉ] Message 3: '============\\n❗️ Account'" + Style.NORMAL)
        return True
    if cleaned_text.lower() == "thank you for completing the task:" or cleaned_text.lower().startswith("thank you for completing the task:"):
        print(Fore.YELLOW + "[❌ IGNORÉ] Message 4: 'Thank you for completing the task:'" + Style.NORMAL)
        return True
    return False

def is_social_network_choice_message(text):
    if not text:
        return False
    if is_message_to_ignore(text):
        return False
    text_lower = text.lower()
    if "instagram :" in text_lower and "tiktok :" in text_lower and "choose social network :" in text_lower:
        return True
    if "------------------------" in text and ("instagram :" in text_lower or "tiktok :" in text_lower):
        return True
    return False

def is_security_check_message(text):
    if not text:
        return False
    security_patterns = [
        "Security check",
        "To continue, please complete the verification",
        "You have 60 sec",
        "👉 Start verification",
        "Start verification",
        "Verification failed",
        "🛡 Security check",
        "choose the image with emoji",
        "solve the example",
        "Choose the image with emoji"
    ]
    for pattern in security_patterns:
        if pattern.lower() in text.lower():
            return True
    return False

def is_comment_text(message):
    if not message:
        return False
    text = message.strip()
    if is_message_to_ignore(text):
        return False
    if is_social_network_choice_message(text):
        return False
    if is_security_check_message(text):
        return False
    url_patterns = [
        r'https?://[^\s<>"\'()]+',
        r'www\.[^\s<>"\'()]+\.[^\s<>"\'()]+',
        r'tiktok\.com/[^\s<>"\'()]+',
        r'vm\.tiktok\.com/[^\s<>"\'()]+',
        r'vt\.tiktok\.com/[^\s<>"\'()]+',
        r'instagram\.com/[^\s<>"\'()]+',
        r'youtube\.com/[^\s<>"\'()]+',
        r'youtu\.be/[^\s<>"\'()]+',
        r'facebook\.com/[^\s<>"\'()]+',
        r'twitter\.com/[^\s<>"\'()]+',
        r'x\.com/[^\s<>"\'()]+'
    ]
    for pattern in url_patterns:
        if re.search(pattern, text, re.IGNORECASE):
            print(Fore.YELLOW + f"[🔗] Message avec lien détecté (IGNORÉ): '{text[:50]}...'" + Style.NORMAL)
            return False
    if text.startswith('/'):
        return False
    if not text or text.isspace():
        return False
    print(Fore.CYAN + f"[💬] Texte de commentaire accepté: '{text[:50]}{'...' if len(text) > 50 else ''}'" + Style.NORMAL)
    return True

def extract_task_from_message(message_obj):
    if not message_obj or not message_obj.message:
        return None
    text = message_obj.message
    if is_message_to_ignore(text):
        print(Fore.YELLOW + "[⚠️] Message à ignorer détecté (Pas une tâche)" + Style.NORMAL)
        return None
    if is_social_network_choice_message(text):
        print(Fore.YELLOW + "[⚠️] Message choix réseau social détecté (Pas une tâche)" + Style.NORMAL)
        return None
    if is_security_check_message(text):
        print(Fore.YELLOW + "[🛡️] Message sécurité détecté (Pas une tâche)" + Style.NORMAL)
        return None
    print(Fore.CYAN + f"[🔍] Analyse du message: {text[:100]}..." + Style.NORMAL)
    url, action, content = None, None, "Nice!"
    if hasattr(message_obj, 'entities') and message_obj.entities:
        for entity in message_obj.entities:
            if hasattr(entity, 'url') and entity.url:
                if 'tiktok.com' in entity.url:
                    url = entity.url
                    print(Fore.GREEN + f"[✔] Lien COMPLET extrait des entités du message: {url}" + Style.NORMAL)
                    break
            elif hasattr(entity, 'type') and hasattr(entity, 'url'):
                try:
                    url_text = text[entity.offset:entity.offset + entity.length]
                    if 'tiktok.com' in url_text:
                        url_match = re.search(r'https?://[^\s<>"\'()]+', url_text)
                        if url_match:
                            url = url_match.group(0)
                            print(Fore.GREEN + f"[✔] Lien TikTok extrait des entités text_url: {url}" + Style.NORMAL)
                            break
                except:
                    pass
    if not url:
        url_patterns = [
            r'https?://(?:www\.|vm\.|vt\.)?tiktok\.com/[^\s<>"\'()]+',
            r'tiktok\.com/[^\s<>"\'()]+',
            r'vm\.tiktok\.com/[^\s<>"\'()]+',
            r'vt\.tiktok\.com/[^\s<>"\'()]+'
        ]
        for pattern in url_patterns:
            url_match = re.search(pattern, text)
            if url_match:
                url = url_match.group(0)
                if not url.startswith('http'):
                    if url.startswith('//'):
                        url = 'https:' + url
                    elif url.startswith('tiktok.com'):
                        url = 'https://' + url
                    elif url.startswith('www.tiktok.com'):
                        url = 'https://' + url
                    elif url.startswith('vm.tiktok.com'):
                        url = 'https://' + url
                    elif url.startswith('vt.tiktok.com'):
                        url = 'https://' + url
                print(Fore.GREEN + f"[✔] Lien TikTok extrait du texte (corrigé): {url}" + Style.NORMAL)
                break
    text_lower = text.lower()
    if 'leave the comment' in text_lower or ('comment' in text_lower and ('task' in text_lower or 'reward' in text_lower)):
        action = "C"
        print(Fore.MAGENTA + "[💬] TÂCHE DE COMMENTAIRE DÉTECTÉE" + Style.NORMAL)
    elif 'like the post below' in text_lower or ('like' in text_lower and 'post below' in text_lower):
        action = "L"
        print(Fore.GREEN + "[👍] TÂCHE DE LIKE DÉTECTÉE !" + Style.NORMAL)
    elif 'follow' in text_lower and 'profile' in text_lower:
        action = "F"
        print(Fore.BLUE + "[👤] TÂCHE DE FOLLOW DÉTECTÉE !" + Style.NORMAL)
    elif 'watch' in text_lower or 'view' in text_lower:
        action = "V"
        print(Fore.CYAN + "[👁️] TÂCHE DE VISUALISATION DÉTECTÉE !" + Style.NORMAL)
    elif url and not action:
        action = "V"
        print(Fore.CYAN + "[👁️] Action par défaut: Visualisation (V)" + Style.NORMAL)
    if action == "C":
        print(Fore.YELLOW + "[📝] Recherche du texte de commentaire..." + Style.NORMAL)
        if url and text.lower().find(url.lower()) != -1:
            url_index = text.lower().find(url.lower())
            possible_comment = text[url_index + len(url):].strip()
            if possible_comment and len(possible_comment.strip()) > 0:
                excluded = ['action:', 'reward:', 'cashcoins:', 'leave the comment', 'do not duplicate']
                if not any(excl in possible_comment.lower() for excl in excluded):
                    if is_comment_text(possible_comment):
                        content = possible_comment.strip()
                        print(Fore.GREEN + f"[💬] Texte de commentaire trouvé dans le même message: '{content[:50]}...'" + Style.NORMAL)
                    else:
                        print(Fore.YELLOW + f"[⚠️] Texte après URL non valide comme commentaire" + Style.NORMAL)
    if action and url:
        print(Fore.GREEN + f"[✅] Tâche extraite: Action={action}, URL={url[:50]}..." + Style.NORMAL)
        return {"url": url, "action": action, "content": content}
    elif action == "C" and not url:
        print(Fore.YELLOW + f"[⚠️] Tâche de commentaire détectée mais pas d'URL trouvée (peut arriver dans message séparé)" + Style.NORMAL)
        return {"url": None, "action": action, "content": content}
    print(Fore.YELLOW + f"[⚠️] Impossible d'extraire une tâche valide du message" + Style.NORMAL)
    return None

# ======================================================================
# FONCTIONS POUR GÉRER LE CAPTCHA TELEGRAM
# ======================================================================
def debug_message_structure(message_obj):
    print(Fore.MAGENTA + "[🔬 DEBUG STRUCTURE MESSAGE]" + Style.NORMAL)
    if not message_obj:
        print(Fore.RED + "Message vide" + Style.NORMAL)
        return
    print(Fore.CYAN + f"ID: {message_obj.id}" + Style.NORMAL)
    print(Fore.CYAN + f"Texte: {message_obj.message[:200] if message_obj.message else 'Aucun'}" + Style.NORMAL)
    if hasattr(message_obj, 'buttons') and message_obj.buttons:
        print(Fore.YELLOW + f"Nombre de boutons: {len(message_obj.buttons)}" + Style.NORMAL)
        for i, row in enumerate(message_obj.buttons):
            print(Fore.CYAN + f"  Ligne {i+1}:" + Style.NORMAL)
            for j, button in enumerate(row):
                print(Fore.CYAN + f"    Bouton [{i},{j}]:" + Style.NORMAL)
                print(Fore.GREEN + f"      Text: {button.text if hasattr(button, 'text') else 'N/A'}" + Style.NORMAL)
                if hasattr(button, 'url'):
                    print(Fore.BLUE + f"      URL: {button.url}" + Style.NORMAL)
                if hasattr(button, 'data'):
                    try:
                        if isinstance(button.data, bytes):
                            decoded = button.data.decode('utf-8', errors='ignore')
                            if 'http' in decoded:
                                print(Fore.MAGENTA + f"      Data (lien): {decoded[:100]}" + Style.NORMAL)
                    except:
                        pass
    else:
        print(Fore.YELLOW + "Pas de boutons" + Style.NORMAL)
    if hasattr(message_obj, 'entities') and message_obj.entities:
        print(Fore.CYAN + f"Nombre d'entités: {len(message_obj.entities)}" + Style.NORMAL)
        for i, entity in enumerate(message_obj.entities):
            print(Fore.CYAN + f"  Entité {i+1}:" + Style.NORMAL)
            if hasattr(entity, 'url'):
                print(Fore.GREEN + f"    URL: {entity.url}" + Style.NORMAL)

async def wait_for_bot_response(last_sent_message_id=None, max_attempts=10):
    print(Fore.CYAN + f"[🔍] Attente réponse du bot après message ID {last_sent_message_id} (max {max_attempts} tentatives)..." + Style.NORMAL)
    task_data_cache = None
    for attempt in range(max_attempts):
        try:
            await asyncio.sleep(2)
            messages = await client.get_messages(BOT_USERNAME, limit=20)
            if not messages:
                print(Fore.YELLOW + f"[{attempt+1}/{max_attempts}] Aucun message" + Style.NORMAL)
                continue
            new_messages = []
            for msg in messages:
                if msg.out:
                    continue
                if last_sent_message_id and msg.id <= last_sent_message_id:
                    continue
                new_messages.append(msg)
            if not new_messages:
                print(Fore.YELLOW + f"[{attempt+1}/{max_attempts}] Aucun NOUVEAU message du bot" + Style.NORMAL)
                continue
            new_messages.sort(key=lambda x: x.id)
            print(Fore.CYAN + f"[{attempt+1}/{max_attempts}] {len(new_messages)} nouveau(x) message(s) du bot détecté(s)" + Style.NORMAL)
            for msg in new_messages:
                if not msg.message:
                    continue
                message_text = msg.message
                print(Fore.CYAN + f"[📨] Message #{msg.id} du bot: {message_text[:80]}..." + Style.NORMAL)
                if message_text.lower().startswith(("sorry", "⭕️ sorry", "désolé", "aucune tâche")):
                    print(Fore.RED + "[❌] Détection: Message 'Sorry...' - Pas de tâches disponibles" + Style.NORMAL)
                    return "sorry", None
                if is_social_network_choice_message(message_text):
                    print(Fore.YELLOW + f"[🌐] Message #{msg.id} de CHOIX RÉSEAU SOCIAL détecté - IGNORÉ et clic sur TikTok" + Style.NORMAL)
                    return "choose_social", msg
                if is_message_to_ignore(message_text):
                    print(Fore.YELLOW + f"[⚠️] Message #{msg.id} à ignorer détecté - IGNORÉ" + Style.NORMAL)
                    continue
                if is_security_check_message(message_text):
                    print(Fore.YELLOW + f"[🛡️] Message #{msg.id} de SÉCURITÉ détecté" + Style.NORMAL)
                    return "security_check", msg
                task_keywords = [
                    "▪️ link :", "link :", "lien :", "▪️ lien :",
                    "leave the comment", "like the post", "follow the profile", "watch the video",
                    "action:", "reward:", "cashcoins:", "comment text:"
                ]
                is_task_message = any(keyword in message_text.lower() for keyword in task_keywords)
                has_entities = hasattr(msg, 'entities') and msg.entities
                if is_task_message or has_entities:
                    print(Fore.MAGENTA + f"[🎯] Message #{msg.id} de tâche potentiel détecté - Extraction..." + Style.NORMAL)
                    extracted_task = extract_task_from_message(msg)
                    if extracted_task:
                        print(Fore.GREEN + f"[✅] Structure de tâche extraite: Action={extracted_task['action']}" + Style.NORMAL)
                        if extracted_task['action'] == "C":
                            task_data_cache = extracted_task
                            print(Fore.YELLOW + "[💬] Tâche de commentaire identifiée." + Style.NORMAL)
                            if task_data_cache.get('url'):
                                print(Fore.GREEN + f"[🌐] Lien COMPLET extrait: {task_data_cache['url'][:60]}..." + Style.NORMAL)
                                if task_data_cache.get('content') and task_data_cache['content'] != "Nice!":
                                    print(Fore.GREEN + f"[💬] Texte trouvé dans le même message: '{task_data_cache['content'][:50]}...'" + Style.NORMAL)
                                    return "task", task_data_cache
                                print(Fore.YELLOW + "[⏳] Recherche du texte du commentaire dans les prochains messages..." + Style.NORMAL)
                                for next_msg in new_messages:
                                    if next_msg.id <= msg.id:
                                        continue
                                    if is_comment_text(next_msg.message):
                                        print(Fore.GREEN + f"[💬] Texte du commentaire trouvé dans message #{next_msg.id}: '{next_msg.message[:50]}...'" + Style.NORMAL)
                                        task_data_cache['content'] = next_msg.message.strip()
                                        return "task", task_data_cache
                                print(Fore.YELLOW + "[⚠️] Texte de commentaire non trouvé, utilisation du texte par défaut 'Nice!'" + Style.NORMAL)
                                return "task", task_data_cache
                            else:
                                print(Fore.YELLOW + "[⚠️] URL non trouvée dans ce message." + Style.NORMAL)
                                continue
                        else:
                            return "task", extracted_task
                if is_comment_text(message_text):
                    print(Fore.YELLOW + f"[💬] Message #{msg.id} semble être un texte de commentaire" + Style.NORMAL)
                    if task_data_cache and task_data_cache['action'] == "C" and task_data_cache.get('content') == "Nice!":
                        print(Fore.GREEN + f"[💬] Attribution du texte à la tâche de commentaire existante" + Style.NORMAL)
                        task_data_cache['content'] = message_text.strip()
                        return "task", task_data_cache
                    for prev_msg in new_messages:
                        if prev_msg.id >= msg.id:
                            continue
                        prev_has_entities = hasattr(prev_msg, 'entities') and prev_msg.entities
                        prev_is_task = any(keyword in prev_msg.message.lower() for keyword in task_keywords) if prev_msg.message else False
                        if prev_is_task or prev_has_entities:
                            extracted_task = extract_task_from_message(prev_msg)
                            if extracted_task and extracted_task.get('action') == "C":
                                print(Fore.GREEN + f"[🌐] Tâche de commentaire associée trouvée dans message #{prev_msg.id}!" + Style.NORMAL)
                                extracted_task['content'] = message_text.strip()
                                return "task", extracted_task
                    print(Fore.YELLOW + f"[⏭️] Message #{msg.id} ignoré (pas de tâche de commentaire associée trouvée)" + Style.NORMAL)
        except Exception as e:
            print(Fore.RED + f"[❌] Erreur lors de l'analyse: {e}" + Style.NORMAL)
            import traceback
            traceback.print_exc()
    print(Fore.YELLOW + "[⏰] Timeout: Aucune réponse valide du bot dans les nouveaux messages" + Style.NORMAL)
    return "timeout", None

async def get_last_sent_message_id():
    try:
        messages = await client.get_messages(BOT_USERNAME, limit=10)
        for msg in messages:
            if msg.out:
                return msg.id
        return None
    except Exception as e:
        print(Fore.RED + f"[❌] Erreur get_last_sent_message_id: {e}" + Style.NORMAL)
        return None

# ======================================================================
# FONCTIONS UI-AUTOMATOR ET LOGIQUE TÉLÉGRAM (inchangées)
# ======================================================================
async def perform_ui_task(apk_id, url, action, comment):
    global STOP_TASK_FLAG, TERMUX_BRING_TO_FRONT_DELAY, PRE_ACTION_STABILITY_TIME, HOST_APP_OPEN_DELAY, URL_OPEN_TO_CLONE_SELECT_DELAY, CLONE_OPEN_DELAY, SWIPE_ACTUALISATION_DELAY, POPUP_CLOSE_DELAY, MENU_CLOSE_BACK_DELAY, POST_ACTION_DELAY, COMMENT_PANEL_OPEN_DELAY, COMMENT_PANEL_BACK_DELAY, COMMENT_INPUT_ACTIVATE_DELAY, COMMENT_SEND_KEYS_DELAY, TERMUX_RE_ACQUIRE_FOCUS_DELAY
    global COMMENT_AFTER_BUBBLE_DELAY, COMMENT_KEYBOARD_OPEN_DELAY, COMMENT_PASTE_MENU_DELAY, COMMENT_PASTE_DELAY

    clone_match = re.search(r'\d+', str(apk_id))
    clone_number = clone_match.group(0) if clone_match else '1'
    package_name = APK_PACKAGE_HOST
    d = None
    success = False
    
    c_coords = load_config()
    LIKE_BTN_X = c_coords.get('lx', 1000); LIKE_BTN_Y = c_coords.get('ly', 1385)
    COMMENT_BTN_X = c_coords.get('cx', 1000); COMMENT_BTN_Y = c_coords.get('cy', 1522)
    INPUT_FIELD_X = c_coords.get('tx', 468); INPUT_FIELD_Y = c_coords.get('ty', 2138)
    SEND_BUTTON_X = c_coords.get('sx', 958); SEND_BUTTON_Y = c_coords.get('sy', 2046)
    LONG_CLICK_X = c_coords.get('long_x', 468); LONG_CLICK_Y = c_coords.get('long_y', 2138)
    PASTE_BTN_X = c_coords.get('paste_x', 500); PASTE_BTN_Y = c_coords.get('paste_y', 1800)
    FOLLOW_BTN_X = c_coords.get('follow_x', 1000); FOLLOW_BTN_Y = c_coords.get('follow_y', 500)

    max_retries = 2
    retries = 0
    task_done = False 

    while retries <= max_retries and not task_done:
        if retries > 0:
            print(Fore.RED + Style.BRIGHT + f"\n[🚨 TENTATIVE DE RÉ-EXÉCUTION n°{retries}/{max_retries}]" + Style.NORMAL)
            if await sleep_with_check(0.5):
                success = False
                task_done = True
                break

        try:
            print(Fore.CYAN + f"[🔌] ÉTABLISSEMENT CONNEXION ADB..." + Style.NORMAL)
            try:
                d = await stable_adb_connect(max_retries=1)
                if not d:
                    raise ConnectError("Échec connexion ADB")
            except Exception as e:
                if retries < max_retries:
                    print(Fore.RED + f"[🔄] Reconnexion ADB (tentative {retries+1}/{max_retries})..." + Style.NORMAL)
                    retries += 1
                    continue
                else:
                    raise

            print(Fore.BLUE + "[🏠] Ramener Termux au premier plan..." + Style.NORMAL)
            try:
                await asyncio.to_thread(d.app_start, TERMUX_PACKAGE, stop=False)
            except Exception as e:
                print(Fore.YELLOW + f"[⚠] Erreur démarrage Termux: {e}" + Style.NORMAL)
            if await sleep_with_check(TERMUX_BRING_TO_FRONT_DELAY):
                success = False
                task_done = True
                break

            await asyncio.to_thread(d.app_start, package_name, stop=False) 
            print(Fore.CYAN + f"[➡️] Lancement de l'hôte Multi App pour le clone n°{clone_number}..." + Style.NORMAL)
            if await sleep_with_check(HOST_APP_OPEN_DELAY):
                success = False
                task_done = True
                break

            if url:
                print(Fore.CYAN + f"[🌐] Ouverture du lien: {url}" + Style.NORMAL)
                await asyncio.to_thread(d.open_url, url)
                if await sleep_with_check(URL_OPEN_TO_CLONE_SELECT_DELAY):
                    success = False
                    task_done = True
                    break
                print(Fore.YELLOW + "[🔍] Recherche de l'icône du clone TikTok..." + Style.NORMAL)
                clicked = False
                tiktok_icons = d(text="TikTok")
                try:
                    target_index = int(clone_number) - 1
                except ValueError:
                    target_index = 0
                if not await asyncio.to_thread(tiktok_icons.wait, timeout=3):
                    print(Fore.RED + Style.BRIGHT + "[❌] ÉCHEC : Fenêtre de sélection de clone 'TikTok' non apparue." + Style.NORMAL)
                    success = False
                    task_done = True
                    break
                if tiktok_icons.count > target_index:
                    try:
                        await asyncio.to_thread(tiktok_icons[target_index].click)
                        clicked = True
                        print(Fore.GREEN + f"[✔] Sélection du clone n°{clone_number} réussie." + Style.NORMAL)
                        if await sleep_with_check(CLONE_OPEN_DELAY):
                            success = False
                            task_done = True
                            break
                        print(Fore.YELLOW + "[⚡] Pas d'attente de stabilité - Action immédiate." + Style.NORMAL)
                        print(Fore.YELLOW + "[ℹ] Swipe désactivé pour toutes les actions." + Style.NORMAL)
                        if action in ["L", "C"]:
                            print(Fore.YELLOW + "[🔍] Recherche rapide du pop-up 'TikTok Lite'..." + Style.NORMAL)
                            try:
                                pas_maintenant_btn = d(textMatches=r"(?i)Pas maintenant|Not now")
                                if await asyncio.to_thread(pas_maintenant_btn.exists, timeout=1):
                                    await asyncio.to_thread(pas_maintenant_btn.click)
                                    print(Fore.GREEN + "[✔] Pop-up 'TikTok Lite' fermé." + Style.NORMAL)
                                else:
                                    close_btn = d(resourceIdMatches=".*close_button|.*close_icon|.*tiktok_close")
                                    if await asyncio.to_thread(close_btn.exists, timeout=0.5):
                                        await asyncio.to_thread(close_btn.click)
                                        print(Fore.GREEN + "[✔] Pop-up fermé via 'X'." + Style.NORMAL)
                                    else:
                                        print(Fore.YELLOW + "[ℹ] Pas de pop-up détecté." + Style.NORMAL)
                                if await sleep_with_check(POPUP_CLOSE_DELAY):
                                    success = False
                                    task_done = True
                                    break
                            except Exception as e:
                                print(Fore.RED + f"[❌] Erreur pop-up : {e.__class__.__name__}" + Style.NORMAL)
                    except Exception as e:
                        print(Fore.RED + f"[❌] Échec clic clone: {e}" + Style.NORMAL)
                        clicked = False
                if not clicked:
                    print(Fore.RED + Style.BRIGHT + "[❌] Clone non trouvé ou cliqué." + Style.NORMAL)
                    success = False
                    task_done = True
                    break

            if action == "L":
                menu_present = await asyncio.to_thread(d(textMatches=r"(?i)Télécharger|Vitesse|Pas intéressé\(e\)").exists, timeout=0.5)
                if menu_present:
                    print(Fore.MAGENTA + "[⚠️ MENU DÉTECTÉ] Fermeture rapide avec 'back'." + Style.NORMAL)
                    await asyncio.to_thread(d.press, "back")
                    if await sleep_with_check(MENU_CLOSE_BACK_DELAY):
                        success = False
                        task_done = True
                        break
                else:
                    print(Fore.YELLOW + "[ℹ️ MENU NON DÉTECTÉ] Action immédiate." + Style.NORMAL)
                print(Fore.CYAN + "[⚡] Clic Like immédiat aux coordonnées..." + Style.NORMAL)
                like_icon = d(resourceId="com.zhiliaoapp.musically:id/ak7")
                if await asyncio.to_thread(like_icon.exists, timeout=1.0):
                    print(Fore.GREEN + "[✅] Icône Like détectée. Clic." + Style.NORMAL)
                    await asyncio.to_thread(like_icon.click)
                    success = True
                else:
                    print(Fore.YELLOW + "[⚠️] Icône Like non détectée. Clic FORCÉ." + Style.NORMAL)
                    await asyncio.to_thread(d.click, LIKE_BTN_X, LIKE_BTN_Y)
                    success = True
                if await sleep_with_check(POST_ACTION_DELAY):
                    success = False
                    task_done = True
                    break
                print(Fore.MAGENTA + "---[ Like réussi ]---" + Style.NORMAL)
                await kill_multi_app(d)
                await asyncio.to_thread(d.app_start, TERMUX_PACKAGE, stop=False)
                task_done = True
                break

            elif action == "F":
                print(Fore.GREEN + "[👤] FOLLOW IMMÉDIAT" + Style.NORMAL)
                if await sleep_with_check(1):
                    success = False
                    task_done = True
                    break
                element_clicked = False
                print(Fore.CYAN + "[🔍] Recherche rapide du bouton Follow..." + Style.NORMAL)
                follow_texts = ["Suivre", "Follow", "S'abonner"]
                for text in follow_texts:
                    try:
                        follow_btn = d(text=text)
                        if await asyncio.to_thread(follow_btn.exists, timeout=1):
                            print(Fore.GREEN + f"[✔] Bouton '{text}' détecté!" + Style.NORMAL)
                            await asyncio.to_thread(follow_btn.click)
                            element_clicked = True
                            success = True
                            print(Fore.GREEN + f"[✔] Follow via texte." + Style.NORMAL)
                            break
                    except:
                        continue
                if not element_clicked:
                    print(Fore.YELLOW + "[⚠️] Utilisation des coordonnées fixes..." + Style.NORMAL)
                    print(Fore.CYAN + f"[📍] Clic: X={FOLLOW_BTN_X}, Y={FOLLOW_BTN_Y}" + Style.NORMAL)
                    try:
                        await asyncio.to_thread(d.click, FOLLOW_BTN_X, FOLLOW_BTN_Y)
                        element_clicked = True
                        success = True
                        print(Fore.GREEN + "[✔] Follow via coordonnées." + Style.NORMAL)
                    except Exception as e:
                        print(Fore.RED + f"[❌] Erreur clic: {e}" + Style.NORMAL)
                        success = False
                if await sleep_with_check(POST_ACTION_DELAY):
                    success = False
                    task_done = True
                    break

                await kill_multi_app(d)
                await asyncio.to_thread(d.app_start, TERMUX_PACKAGE, stop=False)
                task_done = True
                break

            elif action == "C":
                print(Fore.RED + Style.BRIGHT + f"[💬] EXÉCUTION DE COMMENTAIRE AVEC COPIER-COLLER DIRECT" + Style.NORMAL)
                print(Fore.CYAN + f"[📝] Texte à commenter: '{comment[:50]}{'...' if len(comment) > 50 else ''}'" + Style.NORMAL)
                print(Fore.CYAN + f"[📏] Longueur: {len(comment)} caractères" + Style.NORMAL)
                print(Fore.GREEN + f"[📋] STRATÉGIE: Copie immédiate → Appui long → Coller → Envoyer" + Style.NORMAL)
                success = False
                menu_present = await asyncio.to_thread(d(textMatches=r"(?i)Télécharger|Vitesse|Pas intéressé\(e\)").exists, timeout=1)
                if menu_present:
                    print(Fore.MAGENTA + "[⚠️ MENU DÉTECTÉ] Fermeture du menu 'Télécharger/Vitesse' avec 'back'." + Style.NORMAL)
                    await asyncio.to_thread(d.press, "back")
                    if await sleep_with_check(MENU_CLOSE_BACK_DELAY):
                        success = False
                        task_done = True
                        break
                else:
                    print(Fore.YELLOW + "[ℹ️ MENU NON DÉTECTÉ] Exécution immédiate." + Style.NORMAL)
                print(Fore.GREEN + f"[📋 ÉTAPE 1/6] Copie directe du texte du commentaire..." + Style.NORMAL)
                if adb_copy_text_simple(comment):
                    print(Fore.GREEN + "[✔] Texte copié dans le presse-papier via Termux:API" + Style.NORMAL)
                else:
                    print(Fore.YELLOW + "[🔄] Tentative méthode de secours..." + Style.NORMAL)
                    if backup_copy_method(comment):
                        print(Fore.GREEN + "[✔] Texte copié via méthode de secours" + Style.NORMAL)
                    else:
                        print(Fore.RED + "[❌] Échec de la copie, tentative avec texte par défaut" + Style.NORMAL)
                        if not (adb_copy_text_simple("Nice!") or backup_copy_method("Nice!")):
                            print(Fore.RED + "[❌] Impossible de copier même le texte par défaut" + Style.NORMAL)
                            success = False
                            task_done = True
                            break
                await asyncio.sleep(0.5)
                print(Fore.GREEN + f"[💬 ÉTAPE 2/6] Clic sur bulle commentaire..." + Style.NORMAL)
                await asyncio.to_thread(d.click, COMMENT_BTN_X, COMMENT_BTN_Y)
                if await sleep_with_check(COMMENT_AFTER_BUBBLE_DELAY):
                    success = False
                    task_done = True
                    break
                print(Fore.GREEN + f"[🖱️ ÉTAPE 3/6] Clic sur champ de texte..." + Style.NORMAL)
                await asyncio.to_thread(d.click, INPUT_FIELD_X, INPUT_FIELD_Y)
                if await sleep_with_check(COMMENT_KEYBOARD_OPEN_DELAY):
                    success = False
                    task_done = True
                    break
                print(Fore.GREEN + f"[⏱️ ÉTAPE 4/6] Appui long de 1 seconde sur le champ de texte..." + Style.NORMAL)
                await asyncio.to_thread(d.long_click, LONG_CLICK_X, LONG_CLICK_Y, 1.0)
                await asyncio.sleep(1.5)
                print(Fore.GREEN + f"[📋 ÉTAPE 5/6] Clic sur bouton 'Coller'..." + Style.NORMAL)
                await asyncio.to_thread(d.click, PASTE_BTN_X, PASTE_BTN_Y)
                await asyncio.sleep(1.0)
                print(Fore.GREEN + f"[📤 ÉTAPE 6/6] Clic sur bouton 'Envoyer'..." + Style.NORMAL)
                await asyncio.to_thread(d.click, SEND_BUTTON_X, SEND_BUTTON_Y)
                print(Fore.GREEN + f"[👁️] Vérification de l'envoi..." + Style.NORMAL)
                if await sleep_with_check(POST_ACTION_DELAY):
                    success = False
                    task_done = True
                    break
                try:
                    error_msg = d(textMatches=r"(?i)try again|error|failed|échoué|réessayer")
                    if await asyncio.to_thread(error_msg.exists, timeout=2):
                        print(Fore.RED + "[❌] Erreur détectée après envoi" + Style.NORMAL)
                        success = False
                    else:
                        success = True
                        print(Fore.GREEN + Style.BRIGHT + f"[✔ SUCCÈS] Commentaire ENVOYÉ via copier-coller ({len(comment)} caractères)." + Style.NORMAL)
                except:
                    success = True
                    print(Fore.GREEN + Style.BRIGHT + f"[✔ SUCCÈS] Commentaire ENVOYÉ via copier-coller ({len(comment)} caractères)." + Style.NORMAL)
                task_done = True
                break
            
            elif action == "V":
                print(Fore.MAGENTA + "[👁️] VISUALISATION RAPIDE" + Style.NORMAL)
                if await sleep_with_check(POST_ACTION_DELAY):
                    success = False
                    task_done = True
                    break
                success = True
                print(Fore.GREEN + Style.BRIGHT + "[✔ SUCCÈS V] Visualisation." + Style.NORMAL)
                await asyncio.to_thread(d.app_start, TERMUX_PACKAGE, stop=False)
                task_done = True
                break

            else:
                print(Fore.RED + f"[❌] Action '{action}' non supportée." + Style.NORMAL);
                success = False
                task_done = True
                break

        except UiObjectNotFoundError:
            print(Fore.RED + Style.BRIGHT + f"[❌] Élément manquant." + Style.NORMAL)
            success = False
            task_done = True
        except Exception as e:
            print(Fore.RED + Style.BRIGHT + f"[❌] Erreur: {e.__class__.__name__}" + Style.NORMAL)
            success = False
            task_done = True                                                                       
        finally:
            if d:
                try:
                    # ← AJOUT : Tuer Multi App
                    await kill_multi_app(d)
                    await asyncio.sleep(0.5)
            # Nettoyage cache existant
                    await asyncio.to_thread(d.shell, "pm clear-cache com.waxmoon.ma.gp")
                    try:
                        await asyncio.to_thread(d.app_start, TERMUX_PACKAGE, stop=False)
                    except:
                        pass
                except:
                    pass
        return success

# ======================================================================
# FONCTIONS POUR LE BOUTON TIKTOK
# ======================================================================
async def click_tiktok_button(message=None):
    try:
        if message and message.buttons:
            print(Fore.CYAN + f"[🔍] Recherche du bouton TikTok dans le message #{message.id}..." + Style.NORMAL)
            for row in message.buttons:
                for button in row:
                    if hasattr(button, "text") and "TikTok" in button.text:
                        print(Fore.GREEN + f"[✔] Bouton 'TikTok' trouvé dans le message #{message.id}" + Style.NORMAL)
                        try:
                            await button.click()
                            print(Fore.GREEN + f"[✔] Clic sur 'TikTok' effectué" + Style.NORMAL)
                            return True
                        except MessageIdInvalidError:
                            print(Fore.RED + "[❌] Message trop ancien." + Style.NORMAL)
                        except Exception as e:
                            print(Fore.RED + f"[❌] Erreur clic: {e}" + Style.NORMAL)
        messages = await client.get_messages(BOT_USERNAME, limit=10)
        if not messages:
            print(Fore.YELLOW + "[⚠️] Aucun message trouvé." + Style.NORMAL)
            return False
        for msg in messages:
            if not msg.buttons:
                continue
            for row in msg.buttons:
                for button in row:
                    if hasattr(button, "text") and "TikTok" in button.text:
                        print(Fore.GREEN + f"[✔] Bouton 'TikTok' trouvé dans le message #{msg.id}" + Style.NORMAL)
                        try:
                            await button.click()
                            print(Fore.GREEN + f"[✔] Clic sur 'TikTok' effectué" + Style.NORMAL)
                            return True
                        except MessageIdInvalidError:
                            print(Fore.RED + "[❌] Message trop ancien." + Style.NORMAL)
                            continue
                        except Exception as e:
                            print(Fore.RED + f"[❌] Erreur clic: {e}" + Style.NORMAL)
                            continue
        print(Fore.YELLOW + "[⚠️] Bouton 'TikTok' introuvable." + Style.NORMAL)
        return False
    except Exception as e:
        print(Fore.RED + f"[❌] Erreur click_tiktok_button: {e}" + Style.NORMAL)
        return False

# ======================================================================
# LOGIQUE PRINCIPALE SIMPLIFIÉE
# ======================================================================
async def task_loop():
    global STOP_TASK_FLAG
    if not client or not client.is_connected():
        print(Fore.RED + Style.BRIGHT + "[⚠ Connectez Telegram (Option 8)] : Le client n'est pas prêt ou déconnecté." + Style.NORMAL); return
    
    try:
        if not await client.is_user_authorized():
            print(Fore.RED + Style.BRIGHT + "[⚠ Connectez Telegram (Option 8)] : L'utilisateur n'est pas autorisé." + Style.NORMAL); return
    except Exception:
        print(Fore.RED + Style.BRIGHT + "[⚠ Connectez Telegram (Option 8)] : Erreur de vérification d'autorisation. Le client est-il prêt ?" + Style.NORMAL); return
    
    accounts = await asyncio.to_thread(load_json, ACCOUNTS_FILE)
    if not accounts: 
        print(Fore.RED + Style.BRIGHT + "[⚠ Ajoutez un compte (Option 2)]" + Style.NORMAL); return
    
    STOP_TASK_FLAG = False 
    print(Fore.MAGENTA + "[💡 ÉCOUTE ACTIVE] Tapez 'S' et Entrée à tout moment pour revenir au menu." + Style.NORMAL)
    
    #watchdog_task = asyncio.create_task(adb_watchdog())
    listener_task = asyncio.create_task(get_user_input(Fore.BLUE + Style.BRIGHT + "\n > Saisissez 'S' pour stopper : " + Style.NORMAL))

    try:
        print(Fore.MAGENTA + "[⚙️ Démarrage du Bot]" + Style.NORMAL)
        print(Fore.YELLOW + "[📋] Logique CORRIGÉE: Analyse UNIQUEMENT des messages APRÈS notre envoi" + Style.NORMAL)
        print(Fore.GREEN + "[⚡] MODE RAPIDE ACTIVÉ - Pas d'attente inutile" + Style.NORMAL)
        print(Fore.CYAN + "[📋] MÉTHODE: Copie directe du message → Appui long → Coller → Envoyer" + Style.NORMAL)
        
        while not STOP_TASK_FLAG: 
            accounts = await asyncio.to_thread(load_json, ACCOUNTS_FILE)
            if not accounts:
                print(Fore.RED + "[⛔] Aucune compte TikTok configuré. Arrêt de la boucle." + Style.NORMAL)
                break
            
            for acc in accounts:
                if STOP_TASK_FLAG: break 
                
                apk_id = acc.get('apk_id', '1')
                username = acc['username']
                clean_username = username.strip().lstrip('@')
                
                print(Fore.CYAN + f"\n" + "="*50 + Style.NORMAL)
                print(Fore.CYAN + f"[👤] Compte: {clean_username} (Clone n°{apk_id})" + Style.NORMAL)
                print(Fore.CYAN + "="*50 + Style.NORMAL)
                
                has_more_tasks = True
                task_count = 0
                is_first_request = True
                social_network_choice_detected = False

                while has_more_tasks and not STOP_TASK_FLAG:
                    task_count += 1
                    
                    try:
                        if is_first_request:
                            print(Fore.YELLOW + f"[1️⃣] Première tâche pour {clean_username}" + Style.NORMAL)
                            print(Fore.CYAN + "[🔍] Recherche du bouton TikTok..." + Style.NORMAL)
                            found_tiktok_button = await click_tiktok_button()
                            if found_tiktok_button:
                                print(Fore.GREEN + "[✔] Bouton TikTok cliqué." + Style.NORMAL)
                                await asyncio.sleep(1)
                            else:
                                print(Fore.YELLOW + "[ℹ] Bouton TikTok non trouvé, envoi direct." + Style.NORMAL)
                            print(Fore.YELLOW + f"[➡️] Envoi username: {clean_username}" + Style.NORMAL)
                            await client.send_message(BOT_USERNAME, clean_username)
                            is_first_request = False
                            last_sent_msg_id = await get_last_sent_message_id()
                            print(Fore.CYAN + f"[📌] Message envoyé ID: {last_sent_msg_id}" + Style.NORMAL)
                        else:
                            print(Fore.YELLOW + f"[🔄] Tâche chaînée n°{task_count}" + Style.NORMAL)
                        
                        response_type, response_data = await wait_for_bot_response(last_sent_msg_id)
                        
                        if response_type == "sorry":
                            print(Fore.RED + "[❌] Bot: 'Sorry, no tasks'. Passage au compte suivant." + Style.NORMAL)
                            has_more_tasks = False
                            continue
                        
                        elif response_type == "choose_social":
                            print(Fore.YELLOW + "[🌐] Détection: Message de choix de réseau social" + Style.NORMAL)
                            if social_network_choice_detected:
                                print(Fore.RED + "[❌] Déjà traité. Passage au compte suivant." + Style.NORMAL)
                                has_more_tasks = False
                                continue
                            social_network_choice_detected = True
                            print(Fore.CYAN + "[🖱️] Clic sur TikTok..." + Style.NORMAL)
                            await click_tiktok_button(response_data)
                            print(Fore.YELLOW + "[⏳] Attente réponse bot..." + Style.NORMAL)
                            await asyncio.sleep(1)
                            last_sent_msg_id = response_data.id
                            print(Fore.CYAN + f"[📌] Nouveau ID: {last_sent_msg_id}" + Style.NORMAL)
                            continue
                        
                        elif response_type == "security_check":
                            print(Fore.YELLOW + "[🛡️] MESSAGE DE SÉCURITÉ DÉTECTÉ - TRAITEMENT DIRECT" + Style.NORMAL)
                            success = await process_security_check_message(response_data)
                            if success:
                                print(Fore.GREEN + "[✅] Envoi 'Completed' pour continuer..." + Style.NORMAL)
                                await client.send_message(BOT_USERNAME, "✅Completed", link_preview=False)
                                last_sent_msg_id = await get_last_sent_message_id()
                                print(Fore.CYAN + f"[📌] 'Completed' envoyé ID: {last_sent_msg_id}" + Style.NORMAL)
                                print(Fore.MAGENTA + "[🚀] Continuation de la boucle après captcha..." + Style.NORMAL)
                            else:
                                print(Fore.RED + "[❌] Échec captcha, passage au compte suivant." + Style.NORMAL)
                                has_more_tasks = False
                        
                        elif response_type == "task" and response_data:
                            print(Fore.GREEN + f"[✅] Tâche reçue: Action={response_data['action']}" + Style.NORMAL)
                            if response_data.get('url'):
                                print(Fore.CYAN + f"[🌐] URL: {response_data['url']}" + Style.NORMAL)
                            else:
                                print(Fore.YELLOW + f"[⚠️] Pas d'URL" + Style.NORMAL)
                            print(Fore.CYAN + f"[💬] Texte: '{response_data.get('content', 'Nice!')[:50]}{'...' if len(response_data.get('content', 'Nice!')) > 50 else ''}'" + Style.NORMAL)
                            
                            action_code = response_data['action']

                            # Gestion du filtre Like/Commentaire (désactivation sélective)
                            if action_code == "L" and DISABLE_LIKE:
                                print(Fore.YELLOW + "[⏭] Tâche LIKE désactivée – envoi direct de 'Completed'." + Style.NORMAL)
                                await client.send_message(BOT_USERNAME, "✅Completed", link_preview=False)
                                last_sent_msg_id = await get_last_sent_message_id()
                                print(Fore.CYAN + f"[📌] 'Completed' envoyé ID: {last_sent_msg_id}" + Style.NORMAL)
                                print(Fore.MAGENTA + "[🚀] Chaînage: Attente prochaine tâche..." + Style.NORMAL)
                                await asyncio.sleep(0.5)
                                continue

                            if action_code == "C" and DISABLE_COMMENT:
                                print(Fore.YELLOW + "[⏭] Tâche COMMENTAIRE désactivée – envoi direct de 'Completed'." + Style.NORMAL)
                                await client.send_message(BOT_USERNAME, "✅Completed", link_preview=False)
                                last_sent_msg_id = await get_last_sent_message_id()
                                print(Fore.CYAN + f"[📌] 'Completed' envoyé ID: {last_sent_msg_id}" + Style.NORMAL)
                                print(Fore.MAGENTA + "[🚀] Chaînage: Attente prochaine tâche..." + Style.NORMAL)
                                await asyncio.sleep(0.5)
                                continue

                            if action_code == "C":
                                print(Fore.GREEN + f"[📋] Copie immédiate du texte du commentaire dans le presse-papier..." + Style.NORMAL)
                                comment_text = response_data.get('content', 'Nice!')
                                if adb_copy_text_simple(comment_text):
                                    print(Fore.GREEN + f"[✔] Texte copié ({len(comment_text)} caractères) - Prêt pour collage" + Style.NORMAL)
                                else:
                                    if backup_copy_method(comment_text):
                                        print(Fore.GREEN + f"[✔] Texte copié via méthode de secours" + Style.NORMAL)
                                    else:
                                        print(Fore.YELLOW + f"[⚠️] Échec de la copie, sera réessayé pendant l'action" + Style.NORMAL)
                            
                            if not response_data.get('url'):
                                print(Fore.RED + "[❌] ÉCHEC: Pas d'URL" + Style.NORMAL)
                                has_more_tasks = False
                                continue
                            
                            res = await perform_ui_task(
                                apk_id,
                                response_data['url'],
                                action_code,
                                response_data.get('content', 'Nice!')
                            )
                            
                            print(Fore.YELLOW + "[✅] Envoi 'Completed'..." + Style.NORMAL)
                            await client.send_message(BOT_USERNAME, "✅Completed", link_preview=False)
                            last_sent_msg_id = await get_last_sent_message_id()
                            print(Fore.CYAN + f"[📌] 'Completed' envoyé ID: {last_sent_msg_id}" + Style.NORMAL)
                            
                            if res:
                                print(Fore.GREEN + Style.BRIGHT + "[✅] Tâche validée!" + Style.NORMAL)
                            else:
                                print(Fore.RED + "[⚠️] Tâche échouée, mais 'Completed' envoyé." + Style.NORMAL)
                            
                            print(Fore.MAGENTA + "[🚀] Chaînage: Attente prochaine tâche..." + Style.NORMAL)
                            await asyncio.sleep(0.5)
                        
                        elif response_type == "timeout":
                            print(Fore.YELLOW + "[⏰] Timeout: Passage au compte suivant." + Style.NORMAL)
                            has_more_tasks = False
                    
                    except FloodWaitError as e:
                        print(Fore.RED + Style.BRIGHT + f"[❌ FloodWait] Pause de {e.seconds}s" + Style.NORMAL)
                        await asyncio.sleep(e.seconds)
                        has_more_tasks = False
                    
                    except Exception as e:
                        print(Fore.RED + Style.BRIGHT + f"[❌] Erreur: {e.__class__.__name__}: {e}" + Style.NORMAL)
                        import traceback
                        traceback.print_exc()
                        try:
                            await client.send_message(BOT_USERNAME, "✅Completed", link_preview=False)
                            last_sent_msg_id = await get_last_sent_message_id()
                            print(Fore.YELLOW + "[⚠️] 'Completed' envoyé malgré erreur." + Style.NORMAL)
                        except:
                            pass
                        has_more_tasks = False
                
                if not STOP_TASK_FLAG and has_more_tasks == False:
                    print(Fore.YELLOW + f"[⏸️] Pause avant prochain compte..." + Style.NORMAL)
                    await asyncio.sleep(0.5)
            
            if not STOP_TASK_FLAG:
                print(Fore.CYAN + "\n" + "="*50 + Style.NORMAL)
                print(Fore.CYAN + "[🔄] Cycle terminé. Pause de 3s..." + Style.NORMAL)
                print(Fore.CYAN + "="*50 + Style.NORMAL)
                if await sleep_with_check(3): 
                    break
    
    except Exception as e:
        print(Fore.RED + Style.BRIGHT + f"[☠] Crash fatal: {e}" + Style.NORMAL)
        import traceback
        traceback.print_exc()
    
    finally:
        #watchdog_task.cancel()
        if listener_task and not listener_task.done():
            listener_task.cancel()
            try: 
                await listener_task 
            except asyncio.CancelledError: 
                pass
        if STOP_TASK_FLAG:
            print(Fore.RED + Style.BRIGHT + "\n[🛑 ARRÊT] Retour au menu." + Style.NORMAL)
        print(Fore.MAGENTA + "[🛑] Session terminée." + Style.NORMAL)

# ======================================================================
# FONCTIONS MENU (inchangées)
# ======================================================================
async def get_last_message():
    try:
        msg = await client.get_messages(BOT_USERNAME, limit=1)
        return msg[0] if msg else None
    except Exception as e:
        print(Fore.RED + f"[❌] Erreur get_last_message: {e}" + Style.NORMAL)
        return None

async def click_completed_button():
    msg = await get_last_message()
    if not msg or not msg.buttons:
        await client.send_message(BOT_USERNAME, "✅Completed", link_preview=False)
        print(Fore.YELLOW + "[⚠️] Envoi texte '✅Completed'" + Style.NORMAL)
        return True
    for row in msg.buttons:
        for button in row:
            if hasattr(button, "text") and ("Completed" in button.text or "✅" in button.text):
                try:
                    await button.click()
                    print(Fore.GREEN + "[✔] Bouton 'Completed' cliqué." + Style.NORMAL)
                    return True
                except Exception as e:
                    print(Fore.RED + f"[❌] Erreur clic: {e}" + Style.NORMAL)
                    await client.send_message(BOT_USERNAME, "✅Completed", link_preview=False)
                    return True
    await client.send_message(BOT_USERNAME, "✅Completed", link_preview=False)
    print(Fore.YELLOW + "[⚠️] Envoi texte '✅Completed'" + Style.NORMAL)
    return True

def manage_device_ips_menu():
    global DEVICE_IP
    while True:
        config = load_config()
        current_ips = config.get('device_ips', [DEFAULT_DEVICE_IP])
        print(Fore.BLUE + Style.BRIGHT + "\n--- [ GESTION DES IPS D'APPAREIL ] ---" + Style.NORMAL)
        print(Fore.YELLOW + f"IP ACTIVE (pour les tâches) : {DEVICE_IP}\n")
        print(Fore.MAGENTA + f"IP par défaut (Termux Local) : {DEFAULT_DEVICE_IP}\n")
        if not current_ips:
            print(Fore.RED + Style.BRIGHT + "[⚠] Aucune IP enregistrée. Ajoutons la première." + Style.NORMAL)
            action = '1'
        else:
            print(Fore.CYAN + "Liste des IPs enregistrées:")
            for i, ip in enumerate(current_ips):
                status = "(ACTIVE)" if ip == DEVICE_IP else ""
                print(f" {i+1}) {ip} {Fore.GREEN}{status}{Style.NORMAL}")
            print("\nChoix :")
            print(" 1) Ajouter une nouvelle IP (Devient active)")
            print(" 2) Supprimer une IP existante")
            print(" R) Retour au menu principal")
            action = input("Action (1/2/R) : ").upper()
        if action == 'R':
            load_config()
            return
        elif action == '1':
            new_ip = input("Entrez la NOUVELLE IP ou IP:PORT (Ex: 192.168.1.100:5555) : ").strip()
            if not new_ip:
                print(Fore.RED + "[❌] Aucune IP saisie. Annulation." + Style.NORMAL)
                continue
            if new_ip in current_ips:
                print(Fore.YELLOW + f"[ℹ] Cette IP ({new_ip}) est déjà dans la liste." + Style.NORMAL)
                continue
            current_ips.insert(0, new_ip)
            config['device_ips'] = current_ips
            save_config(config)
            DEVICE_IP = new_ip
            print(Fore.GREEN + Style.BRIGHT + f"[✔ SUCCÈS] IP ajoutée et rendue ACTIVE : {DEVICE_IP}" + Style.NORMAL)
        elif action == '2':
            if len(current_ips) == 0:
                print(Fore.YELLOW + "[ℹ] La liste est vide." + Style.NORMAL)
                continue
            try:
                n = int(input("Numéro de l'IP à supprimer (1, 2, ...) : "))
                if 1 <= n <= len(current_ips):
                    deleted_ip = current_ips.pop(n-1)
                    config['device_ips'] = current_ips
                    save_config(config)
                    print(Fore.GREEN + f"[✔ SUCCÈS] IP supprimée : {deleted_ip}" + Style.NORMAL)
                    if deleted_ip == DEVICE_IP:
                        DEVICE_IP = current_ips[0] if current_ips else DEFAULT_DEVICE_IP
                        print(Fore.YELLOW + f"[ℹ] L'IP active a changé pour : {DEVICE_IP}" + Style.NORMAL)
                else:
                    print(Fore.RED + Style.BRIGHT + "[❌ Numéro invalide]" + Style.NORMAL)
            except ValueError:
                print(Fore.RED + Style.BRIGHT + "[❌ Entrée invalide]" + Style.NORMAL)
        else:
            print(Fore.RED + "[⚠ Choix invalide]" + Style.NORMAL)

def input_float(prompt, current_value, default_value):
    while True:
        try:
            value = input(Fore.YELLOW + f"{prompt} (Actuel: {current_value}s | Défaut: {default_value}s) : " + Style.NORMAL).strip()
            if not value:
                return current_value
            new_val = float(value)
            return max(0.0, new_val)
        except ValueError:
            print(Fore.RED + "[❌] Entrée invalide. Veuillez saisir un nombre." + Style.NORMAL)

def manage_delays_menu():
    global TERMUX_BRING_TO_FRONT_DELAY, PRE_ACTION_STABILITY_TIME, HOST_APP_OPEN_DELAY, URL_OPEN_TO_CLONE_SELECT_DELAY, CLONE_OPEN_DELAY, SWIPE_ACTUALISATION_DELAY, POPUP_CLOSE_DELAY, MENU_CLOSE_BACK_DELAY, POST_ACTION_DELAY, COMMENT_PANEL_OPEN_DELAY, COMMENT_PANEL_BACK_DELAY, COMMENT_INPUT_ACTIVATE_DELAY, COMMENT_SEND_KEYS_DELAY, TERMUX_RE_ACQUIRE_FOCUS_DELAY
    global COMMENT_AFTER_BUBBLE_DELAY, COMMENT_KEYBOARD_OPEN_DELAY, COMMENT_PASTE_MENU_DELAY, COMMENT_PASTE_DELAY
    global CAPTCHA_OUVRIR_DELAY, CAPTCHA_WAIT_DELAY, CAPTCHA_VERIFY_DELAY
    
    config = load_config()
    print(Fore.BLUE + Style.BRIGHT + "\n--- [ MODIFICATION DES DÉLAIS DE TEMPS (SECONDES) ] ---" + Style.NORMAL)
    print(Fore.CYAN + "Laissez vide pour conserver la valeur actuelle." + Style.NORMAL)

    TERMUX_BRING_TO_FRONT_DELAY = input_float("Délai 1. Retour Termux (Début tâche)", TERMUX_BRING_TO_FRONT_DELAY, DEFAULT_TERMUX_BRING_TO_FRONT_DELAY)
    PRE_ACTION_STABILITY_TIME = input_float("Délai 2. Stabilité Pré-Action", PRE_ACTION_STABILITY_TIME, DEFAULT_PRE_ACTION_STABILITY_TIME)
    HOST_APP_OPEN_DELAY = input_float("Délai 3. Attente ouverture Hôte Multi App", HOST_APP_OPEN_DELAY, DEFAULT_HOST_APP_OPEN_DELAY)
    URL_OPEN_TO_CLONE_SELECT_DELAY = input_float("Délai 4. Attente sélection de clone", URL_OPEN_TO_CLONE_SELECT_DELAY, DEFAULT_URL_OPEN_TO_CLONE_SELECT_DELAY)
    CLONE_OPEN_DELAY = input_float("Délai 5. Ouverture Clone/Vidéo", CLONE_OPEN_DELAY, DEFAULT_CLONE_OPEN_DELAY)
    SWIPE_ACTUALISATION_DELAY = input_float("Délai 6. Après Swipe d'Actualisation", SWIPE_ACTUALISATION_DELAY, DEFAULT_SWIPE_ACTUALISATION_DELAY)
    POPUP_CLOSE_DELAY = input_float("Délai 7. Après Fermeture Pop-up (TikTok Lite)", POPUP_CLOSE_DELAY, DEFAULT_POPUP_CLOSE_DELAY)
    MENU_CLOSE_BACK_DELAY = input_float("Délai 8. Après 'Back' (Fermeture menu 'Télécharger')", MENU_CLOSE_BACK_DELAY, DEFAULT_MENU_CLOSE_BACK_DELAY)
    POST_ACTION_DELAY = input_float("Délai 9. Post-Action (Like/Follow/Commentaire/Vue)", POST_ACTION_DELAY, DEFAULT_POST_ACTION_DELAY)
    COMMENT_PANEL_OPEN_DELAY = input_float("Délai 10. Chargement Panneau Commentaire", COMMENT_PANEL_OPEN_DELAY, DEFAULT_COMMENT_PANEL_OPEN_DELAY)
    COMMENT_PANEL_BACK_DELAY = input_float("Délai 11. Après 1er 'Back' (Panneau Com.)", COMMENT_PANEL_BACK_DELAY, DEFAULT_COMMENT_PANEL_BACK_DELAY)
    COMMENT_INPUT_ACTIVATE_DELAY = input_float("Délai 12. Activation Champ de Saisie Com.", COMMENT_INPUT_ACTIVATE_DELAY, DEFAULT_COMMENT_INPUT_ACTIVATE_DELAY)
    COMMENT_SEND_KEYS_DELAY = input_float("Délai 13. Après Saisie du Commentaire", COMMENT_SEND_KEYS_DELAY, DEFAULT_COMMENT_SEND_KEYS_DELAY)
    TERMUX_RE_ACQUIRE_FOCUS_DELAY = input_float("Délai 14. Termux Reprise de Focus (Fin tâche)", TERMUX_RE_ACQUIRE_FOCUS_DELAY, DEFAULT_TERMUX_RE_ACQUIRE_FOCUS_DELAY)
    COMMENT_AFTER_BUBBLE_DELAY = input_float("Délai 15. Après clic bulle commentaire", COMMENT_AFTER_BUBBLE_DELAY, DEFAULT_COMMENT_AFTER_BUBBLE_DELAY)
    COMMENT_KEYBOARD_OPEN_DELAY = input_float("Délai 16. Attente ouverture clavier", COMMENT_KEYBOARD_OPEN_DELAY, DEFAULT_COMMENT_KEYBOARD_OPEN_DELAY)
    COMMENT_PASTE_MENU_DELAY = input_float("Délai 17. Attente menu coller", COMMENT_PASTE_MENU_DELAY, DEFAULT_COMMENT_PASTE_MENU_DELAY)
    COMMENT_PASTE_DELAY = input_float("Délai 18. Attente collage texte", COMMENT_PASTE_DELAY, DEFAULT_COMMENT_PASTE_DELAY)
    CAPTCHA_OUVRIR_DELAY = input_float("Délai 19. Attente popup OUVIR captcha", CAPTCHA_OUVRIR_DELAY, DEFAULT_CAPTCHA_OUVRIR_DELAY)
    CAPTCHA_WAIT_DELAY = input_float("Délai 20. Attente résolution captcha (15s)", CAPTCHA_WAIT_DELAY, DEFAULT_CAPTCHA_WAIT_DELAY)
    CAPTCHA_VERIFY_DELAY = input_float("Délai 21. Attente après vérification", CAPTCHA_VERIFY_DELAY, DEFAULT_CAPTCHA_VERIFY_DELAY)

    save_config(config)
    print(Fore.GREEN + Style.BRIGHT + "[✔ SUCCÈS] Tous les délais ont été mis à jour et sauvegardés dans config.json." + Style.NORMAL)
    time.sleep(1)

def manage_actions_filter_menu():
    """Menu 12 : Activer / Désactiver Like et Commentaire."""
    global DISABLE_LIKE, DISABLE_COMMENT
    while True:
        config = load_config()
        # S'assurer que les globals sont synchronisés avec le fichier
        DISABLE_LIKE = config.get('disable_like', DISABLE_LIKE)
        DISABLE_COMMENT = config.get('disable_comment', DISABLE_COMMENT)

        print(Fore.BLUE + Style.BRIGHT + "\n--- [ FILTRE DES ACTIONS LIKE / COMMENTAIRE ] ---" + Style.NORMAL)
        state_like = Fore.RED + "DÉSACTIVÉ" + Style.NORMAL if DISABLE_LIKE else Fore.GREEN + "ACTIVÉ" + Style.NORMAL
        state_comment = Fore.RED + "DÉSACTIVÉ" + Style.NORMAL if DISABLE_COMMENT else Fore.GREEN + "ACTIVÉ" + Style.NORMAL
        print(f" - Like        : {state_like}")
        print(f" - Commentaire : {state_comment}")
        print("\nChoisissez une option :")
        print(" 1) Basculer état du LIKE")
        print(" 2) Basculer état du COMMENTAIRE")
        print(" 3) Désactiver LIKE + COMMENTAIRE")
        print(" 4) Activer LIKE + COMMENTAIRE")
        print(" R) Retour au menu principal")

        choice = input("Votre choix (1/2/3/4/R) : ").strip().upper()
        if choice == 'R':
            return
        elif choice == '1':
            DISABLE_LIKE = not DISABLE_LIKE
        elif choice == '2':
            DISABLE_COMMENT = not DISABLE_COMMENT
        elif choice == '3':
            DISABLE_LIKE = True
            DISABLE_COMMENT = True
        elif choice == '4':
            DISABLE_LIKE = False
            DISABLE_COMMENT = False
        else:
            print(Fore.RED + "[❌] Choix invalide." + Style.NORMAL)
            continue

        config['disable_like'] = DISABLE_LIKE
        config['disable_comment'] = DISABLE_COMMENT
        save_config(config)
        print(Fore.GREEN + "[✔] Configuration des filtres mise à jour et sauvegardée." + Style.NORMAL)
        time.sleep(1)

def list_accounts_menu():
    accounts = load_json(ACCOUNTS_FILE)
    if not accounts:
        print(Fore.RED + Style.BRIGHT + "[⚠] Aucune compte TikTok enregistré." + Style.NORMAL)
        return
    print(Fore.BLUE + Style.BRIGHT + "\n--- [ LISTE DES COMPTES TIKTOK ] ---" + Style.NORMAL)
    for i, acc in enumerate(accounts):
        username = acc.get('username', 'N/A')
        apk_id = acc.get('apk_id', '1')
        print(f" {i+1}) Username: {Fore.GREEN}{username}{Style.NORMAL} | Clone Multi App n°: {Fore.MAGENTA}{apk_id}{Style.NORMAL}")

def add_account_menu():
    accounts = load_json(ACCOUNTS_FILE)
    print(Fore.CYAN + "\n--- [ AJOUTER UN COMPTE TIKTOK ] ---" + Style.NORMAL)
    username = input("Entrez l'Username TikTok (Ex: @johndoe) : ").strip().lstrip('@')
    if not username:
        print(Fore.RED + "[❌] Username non valide. Annulation." + Style.NORMAL)
        return
    try:
        apk_id = input("Numéro du clone Multi App associé (1, 2, 3...) [Défaut: 1] : ").strip()
        apk_id = int(apk_id) if apk_id.isdigit() and int(apk_id) > 0 else 1
    except ValueError:
        apk_id = 1
    if any(acc['username'].lstrip('@').lower() == username.lower() for acc in accounts):
        print(Fore.YELLOW + f"[⚠] Le compte @{username} est déjà enregistré. Mise à jour de l'ID du clone." + Style.NORMAL)
        for acc in accounts:
            if acc['username'].lstrip('@').lower() == username.lower():
                acc['apk_id'] = str(apk_id)
                break
    else:
        accounts.append({"username": f"@{username}", "apk_id": str(apk_id)})
        print(Fore.GREEN + Style.BRIGHT + f"[✔ SUCCÈS] Compte @{username} ajouté (Clone n°{apk_id})." + Style.NORMAL)
    save_json(ACCOUNTS_FILE, accounts)

def delete_account_menu():
    accounts = load_json(ACCOUNTS_FILE)
    if not accounts:
        print(Fore.RED + Style.BRIGHT + "[⚠] Aucune compte TikTok enregistré." + Style.NORMAL)
        return
    list_accounts_menu()
    print(Fore.CYAN + "\n--- [ SUPPRIMER UN COMPTE TIKTOK ] ---" + Style.NORMAL)
    try:
        n = input("Numéro du compte à supprimer (1, 2, ...) : ")
        n = int(n)
        if 1 <= n <= len(accounts):
            deleted_acc = accounts.pop(n-1)
            save_json(ACCOUNTS_FILE, accounts)
            print(Fore.GREEN + Style.BRIGHT + f"[✔ SUCCÈS] Compte @{deleted_acc['username']} supprimé." + Style.NORMAL)
        else:
            print(Fore.RED + Style.BRIGHT + "[❌ Numéro invalide]" + Style.NORMAL)
    except ValueError:
        print(Fore.RED + Style.BRIGHT + "[❌ Entrée invalide]" + Style.NORMAL)

def change_telegram_credentials_menu():
    global TELEGRAM_API_ID, TELEGRAM_API_HASH, TELEGRAM_PHONE_NUMBER
    config = load_config()
    print(Fore.BLUE + Style.BRIGHT + "\n--- [ MISE À JOUR DES IDENTIFIANTS TELEGRAM ] ---" + Style.NORMAL)
    print(Fore.YELLOW + f"API ID actuel : {TELEGRAM_API_ID}")
    new_api_id = input("Nouvel API ID (Laissez vide pour conserver) : ").strip()
    if new_api_id and new_api_id.isdigit():
        TELEGRAM_API_ID = int(new_api_id)
        print(Fore.GREEN + f"API ID mis à jour: {TELEGRAM_API_ID}" + Style.NORMAL)
    print(Fore.YELLOW + f"API HASH actuel : {TELEGRAM_API_HASH}")
    new_api_hash = input("Nouvel API HASH (Laissez vide pour conserver) : ").strip()
    if new_api_hash:
        TELEGRAM_API_HASH = new_api_hash
        print(Fore.GREEN + "API HASH mis à jour." + Style.NORMAL)
    print(Fore.YELLOW + f"Numéro de téléphone de session actuel : {TELEGRAM_PHONE_NUMBER}")
    new_phone = input("Nouveau Numéro de téléphone (Ex: +336xxxxxxxxx - Laissez vide pour conserver) : ").strip()
    if new_phone:
        TELEGRAM_PHONE_NUMBER = new_phone
        print(Fore.GREEN + f"Numéro de téléphone de session mis à jour: {TELEGRAM_PHONE_NUMBER}" + Style.NORMAL)
    save_config(config)
    print(Fore.GREEN + Style.BRIGHT + "[✔ SUCCÈS] Les identifiants Telegram ont été sauvegardés." + Style.NORMAL)
    print(Fore.YELLOW + "Utilisez maintenant l'option 8 (Connexion) pour établir la nouvelle session." + Style.NORMAL)

async def connect_telegram_menu():
    global client, client_status_user, TELEGRAM_PHONE_NUMBER, TELEGRAM_API_ID, TELEGRAM_API_HASH
    print(Fore.CYAN + "\n--- [ CONNEXION ET AUTHENTIFICATION TELEGRAM ] ---" + Style.NORMAL)
    if client and await client.is_user_authorized():
        user = await client.get_me()
        print(Fore.GREEN + f"[ℹ] Telegram est déjà connecté pour l'utilisateur: @{user.username or user.id}" + Style.NORMAL)
        print(Fore.YELLOW + "Voulez-vous vous déconnecter et vous reconnecter avec un autre numéro/API ?" + Style.NORMAL)
        if await asyncio.to_thread(input, "Continuer (O/N) : ").upper() != 'O':
            return
        await client.disconnect()
        client = None
        client_status_user = "Déconnecté"
    phone = TELEGRAM_PHONE_NUMBER
    if not phone:
        print(Fore.YELLOW + "\n[!] Numéro de téléphone de session manquant. Veuillez le saisir." + Style.NORMAL)
        phone = await asyncio.to_thread(input, Fore.YELLOW + "Entrez votre numéro de téléphone (Ex: +336xxxxxxxx) : " + Style.NORMAL)
        TELEGRAM_PHONE_NUMBER = phone.strip()
        config = load_config()
        save_config(config)
    if not TELEGRAM_PHONE_NUMBER or TELEGRAM_API_ID == 0 or TELEGRAM_API_HASH == "":
        print(Fore.RED + "[❌] ÉCHEC : Numéro de téléphone, API ID ou API HASH non valide ou manquant." + Style.NORMAL)
        print(Fore.YELLOW + "Veuillez utiliser l'option 9 pour configurer les identifiants." + Style.NORMAL)
        return
    try:
        client = TelegramClient(SESSION_NAME, TELEGRAM_API_ID, TELEGRAM_API_HASH)
        await client.start(TELEGRAM_PHONE_NUMBER)
        if not await client.is_user_authorized():
            print(Fore.RED + Style.BRIGHT + "[❌ ÉCHEC] Authentification Telegram échouée (vérifiez le code ou le numéro/2FA)." + Style.NORMAL)
            await client.disconnect()
            client = None
            client_status_user = "Déconnecté"
        else:
            user = await client.get_me()
            client_status_user = f"Connecté (@{user.username or user.id})"
            print(Fore.GREEN + Style.BRIGHT + f"[✔ SUCCÈS] Connexion Telegram réussie pour @{user.username or user.id}!" + Style.NORMAL)
    except FloodWaitError as e:
        print(Fore.RED + Style.BRIGHT + f"[❌ Erreur d'inondation] Trop de tentatives. Réessayez dans {e.seconds} secondes." + Style.NORMAL)
        await asyncio.sleep(e.seconds)
        client = None
    except Exception as e:
        print(Fore.RED + Style.BRIGHT + f"[❌] Échec de la connexion Telegram : {e.__class__.__name__} - {e}" + Style.NORMAL)
        client = None

def configure_groq_menu():
    global groq_api_key, groq_model
    print(Fore.BLUE + Style.BRIGHT + "\n--- [ CONFIGURATION API GROQ ] ---" + Style.NORMAL)
    print(Fore.YELLOW + f"Clé actuelle : {groq_api_key[:4]}...{groq_api_key[-4:] if groq_api_key else 'NON CONFIGURÉE'}" + Style.NORMAL)
    print(Fore.YELLOW + f"Modèle actuel : {groq_model}" + Style.NORMAL)
    new_key = input("Nouvelle clé API Groq (laissez vide pour conserver) : ").strip()
    if new_key:
        groq_api_key = new_key
    new_model = input(f"Nouveau modèle (défaut {DEFAULT_GROQ_MODEL}) : ").strip()
    if new_model:
        groq_model = new_model
    save_groq_config()
    print(Fore.GREEN + "✅ Configuration Groq sauvegardée." + Style.NORMAL)

async def manual_ui_test_menu():
    accounts = await asyncio.to_thread(load_json, ACCOUNTS_FILE)
    if not accounts:
        print(Fore.RED + Style.BRIGHT + "[⚠ Ajoutez d'abord un compte actif (Option 2)]" + Style.NORMAL)
        return
    print(Fore.CYAN + "\n--- [ TEST MANUEL UI TIKTOK ] ---" + Style.NORMAL)
    await asyncio.to_thread(list_accounts_menu)
    try:
        n = await asyncio.to_thread(input, "Sélectionnez le numéro du compte à tester : ")
        n = int(n)
        if n < 1 or n > len(accounts): raise ValueError
        acc = accounts[n - 1]
    except (ValueError, IndexError):
        print(Fore.RED + Style.BRIGHT + "[❌ Numéro de compte invalide]" + Style.NORMAL)
        return
    print(Fore.YELLOW + "Actions disponibles : (L) Like, (F) Follow, (C) Commentaire, (V) Visualisation simple" + Style.NORMAL)
    action = await asyncio.to_thread(input, "Action (L/F/C/V) : ")
    action = action.upper()
    url = await asyncio.to_thread(input, "URL (Vidéo ou Profil) : ")
    comment = "Nice!"
    if action == "C":
        comment = await asyncio.to_thread(input, "Texte du commentaire : ")
    if action not in ["L", "F", "C", "V"]:
        print(Fore.RED + Style.BRIGHT + "[❌ Action invalide]" + Style.NORMAL)
        return
    print(Fore.MAGENTA + f"\n[🚀] Lancement du test manuel UI pour le compte {acc['username']} (Clone n°{acc['apk_id']})..." + Style.NORMAL)
    await perform_ui_task(
        acc.get('apk_id', '1'),
        url,
        action,
        comment
    )

async def test_ui_connection_menu():
    global DEVICE_IP
    print(Fore.CYAN + "\n--- [ TEST DE CONNEXION UI ] ---" + Style.NORMAL)
    print(f"Tentative de connexion à l'IP active: {Fore.YELLOW}{DEVICE_IP}{Style.NORMAL}")
    d = None
    try:
        d = await asyncio.to_thread(u2.connect, DEVICE_IP)
        info = await asyncio.to_thread(lambda: d.info)
        print(Fore.GREEN + Style.BRIGHT + "[✔ CONNEXION UI RÉUSSIE]" + Style.NORMAL)
        print(f"Informations de l'appareil: {info.get('model', 'N/A')} (Android {info.get('sdkInt', 'N/A')})" + Style.NORMAL)
    except ConnectError as e:
        print(Fore.RED + Style.BRIGHT + f"[❌ ÉCHEC CRITIQUE DE CONNEXION UI-AUTOMATOR]" + Style.NORMAL)
        print(f"Détails: Impossible de se connecter à {DEVICE_IP}. Assurez-vous que 'adb forward' est actif. ({e.__class__.__name__})" + Style.NORMAL)
    except Exception as e:
        print(Fore.RED + Style.BRIGHT + f"[❌ ERREUR INCONNUE] : {e.__class__.__name__} - {e}" + Style.NORMAL)
    finally:
        if d:
            try:
                await asyncio.to_thread(d.shell, "pm clear-cache com.waxmoon.ma.gp")
                await asyncio.to_thread(d.shell, "pm trim-caches 999G")
                try:
                    await asyncio.to_thread(d.press, "back")
                except: pass
            except: pass

async def menu_configuration_coords():
    while True:
        c = load_config()
        os.system('clear')
        print(f"{Fore.CYAN}==================================================")
        print(f"   MENU 10 : COORDONNÉES TIKTOK (X, Y) ")
        print(f"=================================================={Style.RESET_ALL}")
        print(f"1) Bouton LIKE         -> X: {c.get('lx', 1000)}, Y: {c.get('ly', 1385)}")
        print(f"2) Icône COMMENTAIRE   -> X: {c.get('cx', 1000)}, Y: {c.get('cy', 1522)}")
        print(f"3) Barre de TEXTE      -> X: {c.get('tx', 468)},  Y: {c.get('ty', 2138)}")
        print(f"4) Bouton ENVOYER (=>) -> X: {c.get('sx', 958)},  Y: {c.get('sy', 2046)}")
        print(f"5) Appui LONG          -> X: {c.get('long_x', 468)}, Y: {c.get('long_y', 2138)}")
        print(f"6) Bouton COLLER       -> X: {c.get('paste_x', 500)}, Y: {c.get('paste_y', 1800)}")
        print(f"7) Bouton FOLLOW       -> X: {c.get('follow_x', 1000)}, Y: {c.get('follow_y', 500)}")
        print(f"8) Bouton OUVIR Popup  -> X: {c.get('ouvrir_x', 800)}, Y: {c.get('ouvrir_y', 1200)}")
        print(f"9) Chrome Multi App    -> X: {c.get('chrome_x', 540)}, Y: {c.get('chrome_y', 900)}")
        print(f"10) Bouton Continue    -> X: {c.get('continue_x', 540)}, Y: {c.get('continue_y', 1800)}")
        print(f"11) Start Verification -> X: {c.get('start_verify_x', 540)}, Y: {c.get('start_verify_y', 1400)}")
        print(f"12) Checkbox Cloudflare-> X: {c.get('checkbox_x', 300)}, Y: {c.get('checkbox_y', 1400)}")
        print(f"13) Bouton Submit      -> X: {c.get('submit_x', 540)}, Y: {c.get('submit_y', 1800)}")
        print("--------------------------------------------------")
        print("0) Retour au Menu Principal")
        
        ch = input("\nChoix : ")
        if ch == '0': break
        try:
            if ch == '1':
                c['lx'] = int(input("Nouveau X Like : ")); c['ly'] = int(input("Nouveau Y Like : "))
            elif ch == '2':
                c['cx'] = int(input("Nouveau X Comm : ")); c['cy'] = int(input("Nouveau Y Comm : "))
            elif ch == '3':
                c['tx'] = int(input("Nouveau X Texte : ")); c['ty'] = int(input("Nouveau Y Texte : "))
            elif ch == '4':
                c['sx'] = int(input("Nouveau X Envoi : ")); c['sy'] = int(input("Nouveau Y Envoi : "))
            elif ch == '5':
                c['long_x'] = int(input("Nouveau X Appui Long : ")); c['long_y'] = int(input("Nouveau Y Appui Long : "))
            elif ch == '6':
                c['paste_x'] = int(input("Nouveau X Coller : ")); c['paste_y'] = int(input("Nouveau Y Coller : "))
            elif ch == '7':
                c['follow_x'] = int(input("Nouveau X Follow : ")); c['follow_y'] = int(input("Nouveau Y Follow : "))
            elif ch == '8':
                c['ouvrir_x'] = int(input("Nouveau X OUVIR : ")); c['ouvrir_y'] = int(input("Nouveau Y OUVIR : "))
            elif ch == '9':
                c['chrome_x'] = int(input("Nouveau X Chrome : ")); c['chrome_y'] = int(input("Nouveau Y Chrome : "))
            elif ch == '10':
                c['continue_x'] = int(input("Nouveau X Continue : ")); c['continue_y'] = int(input("Nouveau Y Continue : "))
            elif ch == '11':
                c['start_verify_x'] = int(input("Nouveau X Start Verify : ")); c['start_verify_y'] = int(input("Nouveau Y Start Verify : "))
            elif ch == '12':
                c['checkbox_x'] = int(input("Nouveau X Checkbox : ")); c['checkbox_y'] = int(input("Nouveau Y Checkbox : "))
            elif ch == '13':
                c['submit_x'] = int(input("Nouveau X Submit : ")); c['submit_y'] = int(input("Nouveau Y Submit : "))
            
            with open('config.json', 'w') as f:
                json.dump(c, f, indent=4)
            print(Fore.GREEN + "✅ Coordonnées sauvegardées !")
            time.sleep(1)
        except ValueError:
            print(Fore.RED + "Erreur : Entrez des chiffres uniquement !")
            time.sleep(1)

def display_menu():
    print(Fore.BLUE + Style.BRIGHT + "\n" + "="*60)
    print(Fore.YELLOW + Style.BRIGHT + "   🚀 BOT TIKTOK TASKS 🚀")
    print(Fore.CYAN + Style.BRIGHT + "   Version V44.2.21 - Téléchargement fiable")
    print(Fore.BLUE + "="*60 + Style.NORMAL)
    
    print(Fore.MAGENTA + "\n--- [ 📱 COMPTES TIKTOK ] ---" + Style.NORMAL)
    print(f" {Fore.GREEN}1){Style.NORMAL} Lister les comptes")
    print(f" {Fore.GREEN}2){Style.NORMAL} Ajouter un compte")
    print(f" {Fore.GREEN}3){Style.NORMAL} Supprimer un compte")
    
    print(Fore.MAGENTA + "\n--- [ ⚙️ CONFIGURATION ] ---" + Style.NORMAL)
    print(f" {Fore.YELLOW}4){Style.NORMAL} Gérer les IPs d'appareil (Actif: {Fore.GREEN}{DEVICE_IP}{Style.NORMAL})")
    print(f" {Fore.YELLOW}5){Style.NORMAL} Gérer les délais d'attente (Tous les Sleeps)")
    print(f" {Fore.YELLOW}10){Style.NORMAL} Gérer les Coordonnées Fixes TikTok")
    groq_status = Fore.GREEN + "CONFIGURÉE" if groq_api_key else Fore.RED + "NON CONFIGURÉE"
    print(f" {Fore.YELLOW}11){Style.NORMAL} Configurer l'API Groq (Clé: {groq_status}{Style.NORMAL})")
    # État du filtre Like / Commentaire
    filter_states = []
    if DISABLE_LIKE:
        filter_states.append("Like OFF")
    if DISABLE_COMMENT:
        filter_states.append("Commentaire OFF")
    filter_label = ", ".join(filter_states) if filter_states else "Tout activé"
    print(f" {Fore.YELLOW}12){Style.NORMAL} Activer/Désactiver Like & Commentaire ({filter_label})")
    
    print(Fore.MAGENTA + "\n--- [ 🚀 MOTEUR ] ---" + Style.NORMAL)
    print(f" {Fore.CYAN}6){Style.NORMAL} Démarrer la boucle de tâches automatique")
    print(f" {Fore.CYAN}7){Style.NORMAL} Test Manuel UI (Pour debug/test)")
    
    print(Fore.MAGENTA + "\n--- [ 📱 TELEGRAM ] ---" + Style.NORMAL)
    print(f" {Fore.BLUE}8){Style.NORMAL} Connexion/Déconnexion Telegram (Statut: {Fore.MAGENTA}{client_status_user}{Style.NORMAL})")
    print(f" {Fore.BLUE}9){Style.NORMAL} Changer l'API ID / HASH / Numéro de Session")
    
    print(Fore.MAGENTA + "\n--- [ 🔧 OUTILS ] ---" + Style.NORMAL)
    print(f" {Fore.RED}0){Style.NORMAL} Tester la Connexion UI-Automator")
    print(f" {Fore.RED}Q){Style.NORMAL} Quitter")
    
    print(Fore.BLUE + "="*60 + Style.NORMAL)

async def main():
    global client
    client = None
    check_adb_port()
    while True:
        display_menu()
        try:
            choice = await asyncio.to_thread(input, Fore.BLUE + Style.BRIGHT + "\nChoix (0-12/Q): " + Style.NORMAL)
            choice = choice.upper()
            
            if choice == '0':
                await test_ui_connection_menu()
            elif choice == 'Q':
                if client and client.is_connected(): await client.disconnect()
                print(Fore.RED + Style.BRIGHT + "\n[🛑 ARRÊT] Fermeture du bot. Au revoir !" + Style.NORMAL)
                break
            elif choice == '1':
                await asyncio.to_thread(list_accounts_menu)
            elif choice == '2':
                await asyncio.to_thread(add_account_menu)
            elif choice == '3':
                await asyncio.to_thread(delete_account_menu)
            elif choice == '4':
                await asyncio.to_thread(manage_device_ips_menu)
            elif choice == '5':
                await asyncio.to_thread(manage_delays_menu)
            elif choice == '6':
                await task_loop()
            elif choice == '7':
                await manual_ui_test_menu()
            elif choice == '8':
                await connect_telegram_menu()
            elif choice == '9':
                await asyncio.to_thread(change_telegram_credentials_menu)
            elif choice == '10':
                await menu_configuration_coords()
            elif choice == '11':
                await asyncio.to_thread(configure_groq_menu)
            elif choice == '12':
                await asyncio.to_thread(manage_actions_filter_menu)
            else:
                print(Fore.RED + "[❌] Choix invalide." + Style.NORMAL)
        except EOFError:
            if client and client.is_connected(): await client.disconnect()
            print(Fore.RED + Style.BRIGHT + "\n[🛑 ARRÊT] Fermeture forcée (EOF)." + Style.NORMAL)
            break
        except Exception as e:
            print(Fore.RED + Style.BRIGHT + f"\n[❌ ERREUR MAJEURE] : {e.__class__.__name__} - {e}" + Style.NORMAL)
            await asyncio.sleep(1)

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print(Fore.RED + Style.BRIGHT + "\n[🛑 ARRÊT] Interruption par l'utilisateur (Ctrl+C). Fermeture." + Style.NORMAL)
    except RuntimeError as e:
        if "cannot run non-coroutine" in str(e):
            print(Fore.RED + Style.BRIGHT + "\n[❌ ERREUR] Problème d'environnement asyncio (Python 3.7+ requis). Veuillez mettre à jour ou vérifier votre installation." + Style.NORMAL)
        else:
            raise
