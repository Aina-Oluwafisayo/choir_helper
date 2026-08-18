import streamlit as st
import yt_dlp
import librosa
import numpy as np
import os
import re
import difflib
import spotipy
from spotipy.oauth2 import SpotifyClientCredentials
import pandas as pd
from datetime import datetime
import json
import random
import string
import hashlib
import secrets
import uuid
import smtplib
from email.mime.text import MIMEText
import time

# --- SPOTIFY CREDENTIALS SETUP ---
# Prefer st.secrets (set these in .streamlit/secrets.toml or your host's secrets
# manager) so real credentials never live in source control. The hardcoded
# values below only act as a fallback for local/dev use.
def _get_secret(key, fallback):
    try:
        return st.secrets.get(key, fallback)
    except Exception:
        return fallback

SPOTIFY_CLIENT_ID = _get_secret("SPOTIFY_CLIENT_ID", "cbb64fdcb0c9477d98ef648881525d8c")
SPOTIFY_CLIENT_SECRET = _get_secret("SPOTIFY_CLIENT_SECRET", "14502c49baf64772a116bc9bb783446e")

# --- EMAIL (PASSWORD RESET) SETUP ---
# Set these in .streamlit/secrets.toml — none are hardcoded, since these are
# real credentials for an account that can send mail on your behalf:
#   EMAIL_ADDRESS      = "youraddress@gmail.com"
#   EMAIL_APP_PASSWORD = "16-character app password"   (NOT your normal Gmail password)
#   EMAIL_SMTP_HOST     = "smtp.gmail.com"    (optional, this is the default)
#   EMAIL_SMTP_PORT     = 587                  (optional, this is the default)
EMAIL_ADDRESS = _get_secret("EMAIL_ADDRESS", None)
EMAIL_APP_PASSWORD = _get_secret("EMAIL_APP_PASSWORD", None)
EMAIL_SMTP_HOST = _get_secret("EMAIL_SMTP_HOST", "smtp.gmail.com")
EMAIL_SMTP_PORT = int(_get_secret("EMAIL_SMTP_PORT", 587))
RESET_CODE_TTL_SECONDS = 15 * 60  # reset codes expire after 15 minutes

# --- Server-side reset abuse protection ---
# Tracked per email address, independent of any single browser session, so an
# attacker can't defeat the limit just by requesting a fresh code or opening
# a new incognito tab (both of which would otherwise reset a session-only
# attempt counter back to zero).
_reset_rate_lock = threading.Lock()
_reset_rate_state = {}  # email -> {"fail_count": int, "locked_until": float, "last_sent": float}
RESET_MAX_FAILURES = 5
RESET_LOCKOUT_SECONDS = 15 * 60       # lock further attempts for 15 min after too many failures
RESET_RESEND_COOLDOWN_SECONDS = 45    # minimum gap between reset emails to the same address

def check_reset_lockout(email):
    """Returns a human-readable lockout message if this email is currently
    locked out from resetting, or None if it's clear to proceed."""
    with _reset_rate_lock:
        state = _reset_rate_state.get(email)
        if state and state.get("locked_until", 0) > time.time():
            wait_min = max(1, int((state["locked_until"] - time.time()) / 60) + 1)
            return f"Too many incorrect attempts for this account. Please try again in about {wait_min} minute(s)."
    return None

def check_resend_cooldown(email):
    """Returns a message if a reset code was requested for this email too
    recently, or None if it's clear to send another."""
    with _reset_rate_lock:
        state = _reset_rate_state.get(email)
        if state and time.time() - state.get("last_sent", 0) < RESET_RESEND_COOLDOWN_SECONDS:
            wait_s = int(RESET_RESEND_COOLDOWN_SECONDS - (time.time() - state["last_sent"]))
            return f"Please wait {wait_s}s before requesting another code."
    return None

def record_reset_code_sent(email):
    with _reset_rate_lock:
        state = _reset_rate_state.setdefault(email, {"fail_count": 0, "locked_until": 0, "last_sent": 0})
        state["last_sent"] = time.time()

def record_reset_failure(email):
    """Records a wrong-code attempt server-side. Locks the account out for
    RESET_LOCKOUT_SECONDS once RESET_MAX_FAILURES is reached."""
    with _reset_rate_lock:
        state = _reset_rate_state.setdefault(email, {"fail_count": 0, "locked_until": 0, "last_sent": 0})
        state["fail_count"] += 1
        if state["fail_count"] >= RESET_MAX_FAILURES:
            state["locked_until"] = time.time() + RESET_LOCKOUT_SECONDS
            state["fail_count"] = 0

def clear_reset_rate_state(email):
    with _reset_rate_lock:
        _reset_rate_state.pop(email, None)


def send_reset_code_email(to_email, code):
    """Emails a 6-digit password reset code. Returns (success, message)."""
    if not EMAIL_ADDRESS or not EMAIL_APP_PASSWORD:
        return False, "Email sending isn't configured on this app yet. Ask your app administrator to set it up."
    try:
        msg = MIMEText(
            f"Your Inner Sound Portal password reset code is: {code}\n\n"
            f"This code expires in 15 minutes. If you didn't request this, you can safely ignore this email."
        )
        msg["Subject"] = "Password Reset Code - Inner Sound Portal"
        msg["From"] = EMAIL_ADDRESS
        msg["To"] = to_email
        with smtplib.SMTP(EMAIL_SMTP_HOST, EMAIL_SMTP_PORT, timeout=15) as server:
            server.starttls()
            server.login(EMAIL_ADDRESS, EMAIL_APP_PASSWORD)
            server.sendmail(EMAIL_ADDRESS, [to_email], msg.as_string())
        return True, "Reset code sent! Check your inbox (and spam folder)."
    except Exception as e:
        return False, f"Couldn't send the email: {e}"

# --- PERSISTENT FILE DATABASE ENGINE ---
DB_FILE = "choir_db.json"

def hash_password(password, salt=None):
    """Hashes a password with PBKDF2-HMAC-SHA256 + a per-user random salt.
    Returns (salt, hash_hex). Pass an existing salt to verify a password
    against a stored hash."""
    if salt is None:
        salt = secrets.token_hex(16)
    pwd_hash = hashlib.pbkdf2_hmac("sha256", password.encode(), salt.encode(), 100_000).hex()
    return salt, pwd_hash

def verify_password(password, salt, expected_hash):
    _, computed = hash_password(password, salt)
    return computed == expected_hash

def legacy_hash_password(password):
    """Old unsalted SHA-256 hash. Kept ONLY to verify/migrate accounts that
    were created before salted hashing was added. New accounts never use this."""
    return hashlib.sha256(password.encode()).hexdigest()

import threading
_db_lock = threading.Lock()

def _read_db_from_disk():
    """Reads the database file directly from disk with no locking of its
    own — only call this while holding _db_lock if the result will be
    written back, otherwise a concurrent writer's change can be lost."""
    if not os.path.exists(DB_FILE):
        return {"churches": {}, "users": {}, "assignments": [], "submissions": []}
    try:
        with open(DB_FILE, "r") as f:
            return json.load(f)
    except Exception:
        return {"churches": {}, "users": {}, "assignments": [], "submissions": []}

def _write_db_to_disk(data):
    """Writes the database atomically: to a temp file first, then swaps it
    into place with os.replace. This means a crash or restart mid-write can
    never leave choir_db.json half-written/corrupted."""
    tmp_path = f"{DB_FILE}.tmp"
    with open(tmp_path, "w") as f:
        json.dump(data, f, indent=4)
    os.replace(tmp_path, DB_FILE)

def load_permanent_database():
    """Loads multi-tenant data for DISPLAY/READ purposes. Any code that
    WRITES to the database should go through safe_db_update() instead —
    this alone doesn't protect against two users' changes silently
    overwriting one another."""
    if not os.path.exists(DB_FILE):
        with _db_lock:
            if not os.path.exists(DB_FILE):  # re-check inside the lock
                _write_db_to_disk({"churches": {}, "users": {}, "assignments": [], "submissions": []})
    return _read_db_from_disk()

def save_permanent_database(data):
    """Writes the given snapshot to disk as-is, under lock. Prefer
    safe_db_update() for anything that mutates data based on what's
    currently stored (registrations, evaluations, etc.) — this function
    alone can still overwrite a concurrent change if the snapshot you're
    saving was loaded before another user's write happened."""
    with _db_lock:
        _write_db_to_disk(data)

def safe_db_update(mutator_fn):
    """Safely applies a change to the database: locks, reloads the FRESHEST
    copy straight from disk (so it can never clobber a change another user
    just saved), lets mutator_fn mutate/inspect that fresh copy, and saves —
    all as one atomic step no other write can interleave with.
    mutator_fn should return False if it decided NOT to make a change (e.g.
    a duplicate-email check failed against the fresh data); any other
    return value is treated as success and gets saved. Always returns
    (fresh_db, mutator_fn's return value) so the caller can keep using
    up-to-date data for the rest of the script run."""
    with _db_lock:
        fresh_db = _read_db_from_disk()
        outcome = mutator_fn(fresh_db)
        if outcome is not False:
            _write_db_to_disk(fresh_db)
        return fresh_db, outcome

def generate_church_code():
    """Generates a clean, unique 6-character uppercase identification code."""
    return ''.join(random.choices(string.ascii_uppercase + string.digits, k=6))

def generate_reset_code():
    """Generates a 6-digit numeric password reset code."""
    return ''.join(random.choices(string.digits, k=6))

def find_similar_church(candidate_name, churches, threshold=0.85):
    """Checks a candidate church name against all registered churches for a
    near-duplicate (typos, casing/spacing differences, resubmits). Returns
    (code, existing_name, ratio) for the closest match at/above threshold,
    or (None, None, 0.0) if nothing looks like a duplicate. This is a soft
    heuristic, not a hard identity check — shared/generic names (e.g. two
    different branches both called "RCCG") are common and legitimate, so it
    only flags, it never silently blocks."""
    normalized_candidate = re.sub(r"\s+", " ", candidate_name.strip().lower())
    best_code, best_name, best_ratio = None, None, 0.0
    for code, info in churches.items():
        existing_name = info.get("church_name", "")
        normalized_existing = re.sub(r"\s+", " ", existing_name.strip().lower())
        ratio = difflib.SequenceMatcher(None, normalized_candidate, normalized_existing).ratio()
        if ratio > best_ratio:
            best_code, best_name, best_ratio = code, existing_name, ratio
    if best_ratio >= threshold:
        return best_code, best_name, best_ratio
    return None, None, 0.0

def create_new_church_account(db, church_name, md_name, md_email, md_pass, md_role):
    """Creates a new church + its founding MD/executive account. Re-checks
    for a duplicate email against the freshest data at write time (not the
    possibly-stale `db` passed in), so two people racing to register with
    the same email can't both succeed. Returns (church_code_or_None, fresh_db)."""
    md_salt, md_hash = hash_password(md_pass)

    def _create(fresh, church=church_name, name=md_name, email=md_email, salt=md_salt, hashed=md_hash, role=md_role):
        if email in fresh["users"]:
            return False
        code = generate_church_code()
        while code in fresh["churches"]:  # astronomically unlikely, but guard anyway
            code = generate_church_code()
        fresh["churches"][code] = {"church_name": church, "created_at": datetime.now().strftime("%Y-%m-%d")}
        fresh["users"][email] = {
            "name": name, "role": role, "part": "Executive",
            "church_code": code, "password_salt": salt, "password_hash": hashed
        }
        return code

    fresh_db, result = safe_db_update(_create)
    if result is False:
        st.error("This email is already registered on the system.")
        return None, fresh_db
    st.success("✨ Church Created Successfully!")
    st.info(f"👉 **YOUR UNIQUE CHURCH CODE IS: {result}** \n\n Share this code with your choir members on WhatsApp so they can join your network space.")
    return result, fresh_db

# Instantiate Persistent Storage Engine
db = load_permanent_database()

if "current_user" not in st.session_state:
    st.session_state.current_user = None

# --- UTILITY METADATA & AUDIO FUNCTIONS ---
def get_spotify_search_term(url):
    try:
        track_id_match = re.search(r"track/([a-zA-Z0-9]+)", url)
        if not track_id_match: return None, None, None
        track_id = track_id_match.group(1)
        auth_manager = SpotifyClientCredentials(client_id=SPOTIFY_CLIENT_ID, client_secret=SPOTIFY_CLIENT_SECRET)
        sp = spotipy.Spotify(auth_manager=auth_manager)
        track_info = sp.track(track_id)
        song_name = track_info['name']
        artist_name = track_info['artists'][0]['name']
        return f"{song_name} {artist_name} audio", song_name, artist_name
    except:
        return None, None, None

def download_by_search_or_link(search_query):
    # Unique per call so concurrent users (or concurrent tabs) never overwrite
    # each other's in-progress download.
    output_filename = f"choir_track_{uuid.uuid4().hex}"
    final_query = search_query if ("youtube.com" in search_query.lower() or "youtu.be" in search_query.lower()) else f"ytsearch1:{search_query}"
    ydl_opts = {
        'format': 'bestaudio/best',
        'outtmpl': output_filename,
        'postprocessors': [{'key': 'FFmpegExtractAudio', 'preferredcodec': 'wav', 'preferredquality': '192'}],
        'quiet': True, 'no_warnings': True,
        'extractor_args': {'youtube': {'player_client': ['android', 'web']}},
    }
    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        info = ydl.extract_info(final_query, download=True)
        video_info = info['entries'][0] if 'entries' in info else info
        extracted_title = video_info.get('title', 'Unknown Track')
        extracted_uploader = video_info.get('uploader', 'Unknown Artist')
    return f"{output_filename}.wav", extracted_title, extracted_uploader

def analyze_song_key(audio_path):
    try:
        if not os.path.exists(audio_path): return "Error", "File tracking missing."
        y, sr = librosa.load(audio_path, sr=22050, duration=45)
        chroma = librosa.feature.chroma_cqt(y=y, sr=sr, bins_per_octave=24)
        note_energies = np.mean(chroma, axis=1)
        y_bass = librosa.effects.preemphasis(y)
        chroma_bass = librosa.feature.chroma_cqt(y=y_bass, sr=sr, fmin=float(librosa.note_to_hz('C1')))
        bass_energies = np.mean(chroma_bass, axis=1)
        NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']
        major_profile = np.array([6.35, 2.23, 3.48, 2.33, 4.38, 4.09, 2.52, 5.19, 2.39, 3.66, 2.29, 2.88])
        minor_profile = np.array([6.33, 2.68, 3.52, 5.38, 2.60, 3.53, 2.54, 4.75, 3.98, 2.69, 3.34, 3.17])
        best_score = -999
        detected_key = "Unknown"
        for i in range(12):
            shifted_major = np.roll(major_profile, i)
            shifted_minor = np.roll(minor_profile, i)
            total_major_score = np.corrcoef(note_energies, shifted_major)[0, 1] + (bass_energies[i] * 0.45)
            total_minor_score = np.corrcoef(note_energies, shifted_minor)[0, 1] + (bass_energies[(i + 9) % 12] * 0.25)
            if total_major_score > best_score:
                best_score = total_major_score
                detected_key = f"{NOTE_NAMES[i]} Major"
            if total_minor_score > best_score:
                best_score = total_minor_score
                detected_key = f"{NOTE_NAMES[i]} Minor"
        return "Success", detected_key
    except Exception as e:
        return "Error", str(e)

def hz_to_note_name(hz):
    if hz is None or hz < 40 or np.isnan(hz): return None
    midi_note = 12 * np.log2(hz / 440.0) + 69
    rounded_note = int(round(midi_note))
    NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']
    return NOTE_NAMES[rounded_note % 12]

def run_ai_pitch_audit(filename):
    """Calibrated vocal scanning script to analyze singing notes from uploaded files."""
    try:
        if not os.path.exists(filename): return "Unreadable"
        y, sr = librosa.load(filename, sr=22050, duration=30)
        if len(y) == 0 or np.max(np.abs(y)) < 0.005: return "Silent Track"
        
        y_cleaned = librosa.effects.preemphasis(y)
        f0 = librosa.yin(y_cleaned, fmin=80, fmax=600, sr=sr, frame_length=2048, hop_length=512)
        valid_pitches = f0[~np.isnan(f0)]
        valid_pitches = [pitch for pitch in valid_pitches if 80 <= pitch <= 600]
        
        if len(valid_pitches) == 0: return "No Steady Pitch"
        detected_notes = [hz_to_note_name(hz) for hz in valid_pitches if hz_to_note_name(hz) is not None]
        if not detected_notes: return "Undetermined"
        
        unique_notes, counts = np.unique(detected_notes, return_counts=True)
        dominant_note = unique_notes[np.argsort(counts)[::-1][0]]
        return f"{dominant_note}"
    except:
        return "Analysis Interrupted"

# --- SCREEN RENDERING LAYER ---
st.set_page_config(page_title="Inner Sound Pro Portal", page_icon="🎼", layout="wide")

if st.session_state.current_user is None:
    st.title("🎼 Inner Sound Campus Unified Portal")
    st.caption("Secure Multi-Tenant Network Platform with Automated Vocal Signal Assessments")
    st.write("---")
    
    col_a, col_b = st.columns([1, 1], gap="large")
    
    with col_a:
        st.markdown("### 🔐 Member Secure Login")
        login_email = st.text_input("Registered Email Address", key="login_em").strip().lower()
        login_pass = st.text_input("Account Password", type="password", key="login_pw")
        
        if st.button("Access Dashboard Profile", type="primary", use_container_width=True):
            if login_email in db["users"] and login_pass:
                user_record = db["users"][login_email]
                stored_hash = user_record.get("password_hash")
                is_valid = False

                if stored_hash and "password_salt" in user_record:
                    # Current salted-hash accounts.
                    is_valid = verify_password(login_pass, user_record["password_salt"], stored_hash)
                elif stored_hash:
                    # Legacy unsalted accounts created before salting was added.
                    # Verify against the old scheme, then upgrade the stored
                    # hash in place so it never gets checked the old way again.
                    is_valid = (legacy_hash_password(login_pass) == stored_hash)
                    if is_valid:
                        new_salt, new_hash = hash_password(login_pass)
                        def _migrate_hash(fresh, email=login_email, ns=new_salt, nh=new_hash):
                            if email not in fresh["users"]:
                                return False
                            fresh["users"][email]["password_salt"] = ns
                            fresh["users"][email]["password_hash"] = nh
                            return True
                        db, migrated = safe_db_update(_migrate_hash)
                        if migrated:
                            user_record = db["users"][login_email]
                # NOTE: if stored_hash is missing entirely, is_valid stays False —
                # a record with no password can never be logged into.

                if is_valid:
                    st.session_state.current_user = user_record
                    st.session_state.current_user["email"] = login_email
                    st.toast("Access Granted!", icon="🎉")
                    st.rerun()
                else:
                    st.error("🔒 Incorrect password credentials.")
            else:
                st.error("Account email profile not recognized in server index.")

        with st.expander("🔑 Forgot your password?"):
            reset_stage = st.session_state.get("reset_stage", "request")
            MAX_RESET_ATTEMPTS = 5

            if reset_stage == "request":
                st.caption("Enter your registered email and we'll send you a 6-digit reset code.")
                reset_target_email = st.text_input("Registered Email Address", key="reset_target_email").strip().lower()
                if st.button("Send Reset Code", key="send_reset_code_btn"):
                    if not reset_target_email:
                        st.error("Please enter your email address.")
                    elif reset_target_email not in db["users"]:
                        # Same message whether or not the account exists, so this
                        # form can't be used to probe which emails are registered.
                        st.success("If that email is registered, a reset code has been sent.")
                    else:
                        lockout_msg = check_reset_lockout(reset_target_email)
                        cooldown_msg = check_resend_cooldown(reset_target_email)
                        if lockout_msg:
                            st.error(lockout_msg)
                        elif cooldown_msg:
                            st.warning(cooldown_msg)
                        else:
                            code = generate_reset_code()
                            sent, message = send_reset_code_email(reset_target_email, code)
                            if sent:
                                record_reset_code_sent(reset_target_email)
                                st.session_state["reset_email"] = reset_target_email
                                st.session_state["reset_code"] = code
                                st.session_state["reset_code_expires"] = time.time() + RESET_CODE_TTL_SECONDS
                                st.session_state["reset_attempts"] = 0
                                st.session_state["reset_stage"] = "confirm"
                                st.rerun()
                            else:
                                st.error(message)

            elif reset_stage == "confirm":
                attempts_left = MAX_RESET_ATTEMPTS - st.session_state.get("reset_attempts", 0)
                st.caption(f"Enter the 6-digit code sent to **{st.session_state.get('reset_email', '')}**. ({attempts_left} attempt{'s' if attempts_left != 1 else ''} remaining)")
                entered_code = st.text_input("Reset Code", key="entered_reset_code", max_chars=6)
                new_reset_pass = st.text_input("New Password", type="password", key="new_reset_pass")
                col_r1, col_r2 = st.columns(2)
                with col_r1:
                    if st.button("Reset Password", type="primary", key="confirm_reset_btn", use_container_width=True):
                        target_email = st.session_state.get("reset_email", "")
                        lockout_msg = check_reset_lockout(target_email)
                        if lockout_msg:
                            st.error(lockout_msg)
                            st.session_state["reset_stage"] = "request"
                        elif time.time() > st.session_state.get("reset_code_expires", 0):
                            st.error("This code has expired. Please request a new one.")
                            st.session_state["reset_stage"] = "request"
                        elif st.session_state.get("reset_attempts", 0) >= MAX_RESET_ATTEMPTS:
                            st.error("Too many incorrect attempts. Please request a new code.")
                            st.session_state["reset_stage"] = "request"
                        elif not secrets.compare_digest(str(entered_code), str(st.session_state.get("reset_code", ""))):
                            st.session_state["reset_attempts"] = st.session_state.get("reset_attempts", 0) + 1
                            record_reset_failure(target_email)
                            remaining = MAX_RESET_ATTEMPTS - st.session_state["reset_attempts"]
                            if remaining <= 0:
                                st.error("Too many incorrect attempts. Please request a new code.")
                                for k in ("reset_stage", "reset_email", "reset_code", "reset_code_expires", "reset_attempts"):
                                    st.session_state.pop(k, None)
                            else:
                                st.error(f"Incorrect reset code. {remaining} attempt{'s' if remaining != 1 else ''} remaining.")
                        elif not new_reset_pass:
                            st.error("Please enter a new password.")
                        else:
                            new_salt, new_hash = hash_password(new_reset_pass)
                            def _apply_reset(fresh, email=target_email, ns=new_salt, nh=new_hash):
                                if email not in fresh["users"]:
                                    return False
                                fresh["users"][email]["password_salt"] = ns
                                fresh["users"][email]["password_hash"] = nh
                                return True
                            db, reset_ok = safe_db_update(_apply_reset)
                            if reset_ok:
                                clear_reset_rate_state(target_email)
                                for k in ("reset_stage", "reset_email", "reset_code", "reset_code_expires", "reset_attempts"):
                                    st.session_state.pop(k, None)
                                st.success("✅ Password reset! You can now log in with your new password.")
                            else:
                                st.error("That account no longer exists.")
                with col_r2:
                    if st.button("Cancel", key="cancel_reset_btn", use_container_width=True):
                        for k in ("reset_stage", "reset_email", "reset_code", "reset_code_expires", "reset_attempts"):
                            st.session_state.pop(k, None)
                        st.rerun()
                
    with col_b:
        st.markdown("### 🚀 Registration & Onboarding")
        onboard_action = st.tabs(["👥 Join Existing Choir", "⛪ Register New Church Unit"])
        
        with onboard_action[0]:
            with st.form("join_choir_form", clear_on_submit=False):
                reg_name = st.text_input("Full Name")
                reg_email = st.text_input("Email Address", key="reg_em")
                reg_pass = st.text_input("Create Password", type="password", key="reg_pw")
                reg_code = st.text_input("Paste Unique Church Code")
                reg_role = st.selectbox("Joining As", ["Chorister", "Asst. MD", "Official"])
                reg_part = st.selectbox("Vocal Range Line (applies only if joining as Chorister)", ["Soprano", "Alto", "Tenor", "Bass"])
                join_submitted = st.form_submit_button("Register as Active Member", use_container_width=True)

            if join_submitted:
                clean_reg_name = reg_name.strip()
                clean_reg_email = reg_email.strip().lower()
                clean_reg_code = reg_code.strip().upper()
                final_part = reg_part if reg_role == "Chorister" else "Executive"
                if clean_reg_name and clean_reg_email and reg_pass and clean_reg_code:
                    if clean_reg_code not in db["churches"]:
                        st.error("Invalid Church Code! Please request the correct string from your MD.")
                    elif clean_reg_email in db["users"]:
                        st.error("This email is already linked to a profile.")
                    else:
                        reg_salt, reg_hash = hash_password(reg_pass)
                        def _join(fresh, code=clean_reg_code, email=clean_reg_email, name=clean_reg_name, role=reg_role, part=final_part, salt=reg_salt, hashed=reg_hash):
                            if code not in fresh["churches"] or email in fresh["users"]:
                                return False
                            fresh["users"][email] = {
                                "name": name, "role": role, "part": part,
                                "church_code": code, "password_salt": salt, "password_hash": hashed
                            }
                            return True
                        db, joined = safe_db_update(_join)
                        if joined:
                            st.success(f"Successfully joined {db['churches'][clean_reg_code]['church_name']}! Go to Login.")
                        elif clean_reg_code not in db["churches"]:
                            st.error("Invalid Church Code! Please request the correct string from your MD.")
                        else:
                            st.error("This email is already linked to a profile.")
                else:
                    missing = []
                    if not clean_reg_name: missing.append("Full Name")
                    if not clean_reg_email: missing.append("Email Address")
                    if not reg_pass: missing.append("Password")
                    if not clean_reg_code: missing.append("Church Code")
                    st.error(f"Please fill in: {', '.join(missing)}")
                
        with onboard_action[1]:
            with st.form("register_church_form", clear_on_submit=False):
                new_church_name = st.text_input("Full Official Church Name (e.g., RCCG Genesis Choir)")
                md_name = st.text_input("MD / Lead Official Name")
                md_email = st.text_input("MD Official Email Address")
                md_pass = st.text_input("Create Admin Password", type="password", key="md_reg_pw")
                md_role = st.selectbox("Your Executive Leadership Designation", ["MD", "Asst. MD", "Official"])
                church_submitted = st.form_submit_button("Deploy Church Network Hub", use_container_width=True)
            
            if church_submitted:
                clean_church = new_church_name.strip()
                clean_md_name = md_name.strip()
                clean_md_email = md_email.strip().lower()
                
                if clean_church and clean_md_name and clean_md_email and md_pass:
                    if clean_md_email in db["users"]:
                        st.error("This email is already registered on the system.")
                    else:
                        match_code, match_name, ratio = find_similar_church(clean_church, db["churches"])
                        if match_code:
                            st.session_state["pending_church_reg"] = {
                                "church": clean_church, "md_name": clean_md_name, "md_email": clean_md_email,
                                "md_pass": md_pass, "md_role": md_role, "match_name": match_name
                            }
                        else:
                            _, db = create_new_church_account(db, clean_church, clean_md_name, clean_md_email, md_pass, md_role)
                else:
                    missing = []
                    if not clean_church: missing.append("Church Name")
                    if not clean_md_name: missing.append("MD/Lead Name")
                    if not clean_md_email: missing.append("MD Email")
                    if not md_pass: missing.append("Admin Password")
                    st.error(f"Please fill in: {', '.join(missing)}")

            if "pending_church_reg" in st.session_state:
                pending = st.session_state["pending_church_reg"]
                st.warning(
                    f"⚠️ **\"{pending['church']}\"** looks very similar to an already-registered church: "
                    f"**\"{pending['match_name']}\"**. Creating a duplicate splits your choir's members, songs, "
                    f"and submissions into two separate networks with different codes — usually not what you want. "
                    f"If this is actually your church, ask its existing MD for the join code instead."
                )
                conf_col1, conf_col2 = st.columns(2)
                with conf_col1:
                    if st.button("✅ This is genuinely a different church — Create Anyway", use_container_width=True):
                        _, db = create_new_church_account(db, pending["church"], pending["md_name"], pending["md_email"], pending["md_pass"], pending["md_role"])
                        del st.session_state["pending_church_reg"]
                with conf_col2:
                    if st.button("❌ Cancel Registration", use_container_width=True):
                        del st.session_state["pending_church_reg"]
                        st.rerun()

else:
    current_user = st.session_state.current_user
    user_church_code = current_user["church_code"]
    user_church_name = db["churches"][user_church_code]["church_name"]
    is_admin = current_user["role"] in ["MD", "Asst. MD", "Official"]
    
    st.markdown(f"## ⛪ Hub: {user_church_name}")
    st.caption(f"Authenticated Session: **{current_user['name']}** ({current_user['role']}) | Code Security Base: `{user_church_code}`")
    
    with st.sidebar:
        st.header("👤 Session Panel")
        st.info(f"**User:** {current_user['name']}\n\n**Role:** {current_user['role']}\n\n**Part Line:** {current_user['part']}\n\n**Network Code:** `{user_church_code}`")
        if st.button("Log Out Securely", type="secondary", use_container_width=True):
            st.session_state.current_user = None
            st.rerun()
            
    app_tabs = ["🎵 Rehearsal Center", "📤 Submit Part Score"]
    if is_admin:
        app_tabs.append("👑 Executive Command Vault")
    app_tabs.append("🔍 Instant Key Finder (AI Engine)")
    
    active_tabs = st.tabs(app_tabs)
    
    with active_tabs[0]:
        st.subheader(f"🎶 {current_user['part']} Rehearsal Desk")
        filtered_tasks = [t for t in db["assignments"] if t["church_code"] == user_church_code]
        
        if not filtered_tasks:
            st.info("Your choir leaders have not posted any score schedules for this period.")
        else:
            for task in filtered_tasks:
                with st.container():
                    st.info(f"### 🎵 Task: **{task['title']}** — *by {task['artist']}*\n\n**Assigned Reference Target Key:** `{task['target_key']}` | *Date Posted: {task['date']}*")
                    
                    member_subs = [s for s in db.get("submissions", []) if s.get("church_code") == user_church_code and s.get("email") == current_user.get("email") and s.get("song") == task["title"]]
                    if member_subs:
                        latest_sub = member_subs[-1]
                        if "evaluation" in latest_sub:
                            eval_data = latest_sub["evaluation"]
                            st.markdown("#### 📊 Evaluation Review Verdict:")
                            if "Approved" in eval_data["status"]:
                                st.success(f"**Status:** {eval_data['status']} | **Pitch Accuracy:** {eval_data['pitch_score']}/10 | **Timing:** {eval_data['timing_score']}/10")
                            else:
                                st.warning(f"**Status:** {eval_data['status']} | **Pitch Accuracy:** {eval_data['pitch_score']}/10 | **Timing:** {eval_data['timing_score']}/10")
                            st.markdown(f"> *MD Feedback Notes:* \"{eval_data['md_comments']}\" — *Checked by {eval_data['evaluated_by']}*")
                        else:
                            st.markdown("⏳ *Submission uploaded successfully. Waiting for official grading assessment review.*")
                    st.write("---")

    with active_tabs[1]:
        st.subheader("📤 Performance File Submission Node")
        filtered_tasks = [t for t in db["assignments"] if t["church_code"] == user_church_code]
        
        if not filtered_tasks:
            st.warning("No live assignments running to attach recording streams to.")
        else:
            select_task = st.selectbox("Select Active Assignment Context:", [t['title'] for t in filtered_tasks])
            uploaded_recording = st.file_uploader("Upload voice part submission (WAV or MP3):", type=["mp3", "wav"])

            def _save_submission_file(song, file_obj, remove_ids=None):
                """Saves a recording to disk + the database. If remove_ids is
                given, those prior submission records (and their audio files)
                are removed first so re-recording replaces rather than stacks."""
                global db
                with st.spinner("Processing performance telemetry and backing up data lines..."):
                    target_dir = f"choir_audio_vault/{user_church_code}"
                    os.makedirs(target_dir, exist_ok=True)
                    submission_id = ''.join(random.choices(string.ascii_uppercase + string.digits, k=8))
                    safe_filename = f"{target_dir}/{current_user['name'].replace(' ', '_')}_{submission_id}.wav"

                    with open(safe_filename, "wb") as f:
                        f.write(file_obj.getbuffer())

                    ai_note = run_ai_pitch_audit(safe_filename)

                    new_submission = {
                        "id": f"SUB_{submission_id}",
                        "church_code": user_church_code,
                        "email": current_user.get("email"),
                        "name": current_user['name'],
                        "part": current_user['part'],
                        "song": song,
                        "audio_path": safe_filename,
                        "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M"),
                        "ai_detected_note": ai_note
                    }

                    if remove_ids:
                        for s in db.get("submissions", []):
                            if s.get("id") in remove_ids and os.path.exists(s.get("audio_path", "")):
                                try:
                                    os.remove(s["audio_path"])
                                except Exception:
                                    pass  # best-effort cleanup, not worth failing the submission over

                    def _mutate(fresh, entry=new_submission, rm=remove_ids):
                        if rm:
                            fresh["submissions"] = [s for s in fresh.get("submissions", []) if s.get("id") not in rm]
                        fresh.setdefault("submissions", []).append(entry)
                        return True
                    db, _ = safe_db_update(_mutate)

                    st.success("🎉 Recording processed and securely logged!" + (" Your previous attempt was replaced." if remove_ids else ""))
                    if ai_note not in ["Unreadable", "Silent Track", "No Steady Pitch"]:
                        st.info(f"🎯 **AI Vocal Insight:** Our engine matched your sustained frequency to the note: **{ai_note}**.")
                    else:
                        st.warning(f"⚠️ **AI Vocal Insight Notice:** Audio data processed successfully, but the engine noted: *{ai_note}*.")

            if st.button("Submit Recording Archive"):
                if uploaded_recording is None:
                    st.error("Please insert a recorded media file first.")
                else:
                    prior_subs = [
                        s for s in db.get("submissions", [])
                        if s.get("email") == current_user.get("email")
                        and s.get("church_code") == user_church_code
                        and s.get("song", "").strip().lower() == select_task.strip().lower()
                    ]
                    if prior_subs:
                        st.session_state["pending_resubmission"] = select_task
                    else:
                        _save_submission_file(select_task, uploaded_recording)

            if st.session_state.get("pending_resubmission") == select_task:
                prior_subs = [
                    s for s in db.get("submissions", [])
                    if s.get("email") == current_user.get("email")
                    and s.get("church_code") == user_church_code
                    and s.get("song", "").strip().lower() == select_task.strip().lower()
                ]
                if not prior_subs:
                    st.session_state.pop("pending_resubmission", None)
                else:
                    most_recent = max(prior_subs, key=lambda s: s.get("timestamp", ""))
                    eval_info = most_recent.get("evaluation")
                    status_line = f"marked **{eval_info['status']}**" if eval_info else "*not yet reviewed*"
                    st.warning(
                        f"⚠️ You already submitted **'{select_task}'** on {most_recent['timestamp']} ({status_line}). "
                        f"What would you like to do with this new recording?"
                    )
                    rc1, rc2, rc3 = st.columns(3)
                    with rc1:
                        if st.button("🔁 Replace Previous Attempt", use_container_width=True):
                            if uploaded_recording is None:
                                st.error("Please insert a recorded media file first.")
                            else:
                                _save_submission_file(select_task, uploaded_recording, remove_ids=[s.get("id") for s in prior_subs])
                                st.session_state.pop("pending_resubmission", None)
                    with rc2:
                        if st.button("➕ Keep Both (New Attempt)", use_container_width=True):
                            if uploaded_recording is None:
                                st.error("Please insert a recorded media file first.")
                            else:
                                _save_submission_file(select_task, uploaded_recording)
                                st.session_state.pop("pending_resubmission", None)
                    with rc3:
                        if st.button("❌ Cancel", use_container_width=True):
                            st.session_state.pop("pending_resubmission", None)
                            st.rerun()

    if is_admin:
        with active_tabs[2]:
            st.subheader("👑 Executive Command Control Console")

            st.write("### 👥 Choir Member Roster")
            roster = [
                {"Name": u["name"], "Email": email, "Role": u["role"], "Part": u["part"]}
                for email, u in db["users"].items() if u.get("church_code") == user_church_code
            ]
            if not roster:
                st.info("No members yet — share your church code so people can join.")
            else:
                roster_df = pd.DataFrame(roster).sort_values(by=["Role", "Part", "Name"], ascending=[False, True, True])
                metric_cols = st.columns(5)
                metric_cols[0].metric("Total Members", len(roster))
                for i, part in enumerate(["Soprano", "Alto", "Tenor", "Bass"], start=1):
                    metric_cols[i].metric(part, sum(1 for r in roster if r["Part"] == part))
                st.dataframe(roster_df, use_container_width=True, hide_index=True)

            st.write("---")
            
            st.write("### 📢 Post New Target Score")
            with st.form("publish_assignment_form", clear_on_submit=True):
                col1, col2 = st.columns(2)
                with col1:
                    new_title = st.text_input("Song Title Label")
                    new_artist = st.text_input("Original Composer Name")
                with col2:
                    new_key = st.text_input("Target Pitch Signature Key (e.g., F# Major)")
                publish_submitted = st.form_submit_button("Publish Assignment to Your Choir Feed", type="primary", use_container_width=True)

            if publish_submitted:
                clean_title, clean_artist, clean_key = new_title.strip(), new_artist.strip(), new_key.strip()
                if clean_title and clean_artist and clean_key:
                    def _publish(fresh, church=user_church_code, title=clean_title, artist=clean_artist, key=clean_key):
                        fresh.setdefault("assignments", []).append({
                            "id": (max([a.get("id", 0) for a in fresh["assignments"]], default=0) + 1),
                            "church_code": church, "title": title, "artist": artist, "target_key": key,
                            "date": datetime.now().strftime("%Y-%m-%d")
                        })
                        return True
                    db, _ = safe_db_update(_publish)
                    st.toast(f"'{clean_title}' published!", icon="✅")
                    st.success(f"✅ **Published to your choir feed!** '{clean_title}' by {clean_artist} — Target Key: **{clean_key}**")
                else:
                    st.error("All fields are required.")
            
            st.write("---")
            
            st.write("### 🎧 Filtered Choir Performance Logs & Evaluation Panel")
            filtered_subs = [s for s in db.get("submissions", []) if s["church_code"] == user_church_code]
            
            if not filtered_subs:
                st.info("No members from your church branch have submitted parts yet.")
            else:
                sub_options = {f"{s['name']} - {s['song']} ({s['part']}) [{s['timestamp']}]": s for s in filtered_subs}
                selected_sub_label = st.selectbox("🎯 Choose a tracking line recording to evaluate:", list(sub_options.keys()))
                sub_to_audit = sub_options[selected_sub_label]
                
                st.markdown(f"#### 🛠️ Auditing Workspace: **{sub_to_audit['name']}**")
                st.write(f"Vocal Line Part: `{sub_to_audit['part']}` | Targeted Song Context: **{sub_to_audit['song']}**")
                
                ai_pitch = sub_to_audit.get("ai_detected_note", "No Scan Saved")
                st.metric(label="AI Frequency Engine Analysis Note Output", value=f"Note: {ai_pitch}")
                
                if os.path.exists(sub_to_audit["audio_path"]):
                    with open(sub_to_audit["audio_path"], "rb") as audio_file:
                        st.audio(audio_file.read(), format="audio/wav")
                
                current_eval = sub_to_audit.get("evaluation", {})
                eval_status = st.radio("Review Audit Checklist Status:", ["Approved ✅", "Needs Re-Recording ❌"], index=0 if "Approved" in current_eval.get("status", "Approved") else 1)
                
                col_s1, col_s2 = st.columns(2)
                with col_s1:
                    p_score = st.slider("Pitch Accuracy Tuning Score (0-10)", 0, 10, value=current_eval.get("pitch_score", 8))
                with col_s2:
                    t_score = st.slider("Timing, Pulse & Pocket Execution Score (0-10)", 0, 10, value=current_eval.get("timing_score", 8))
                    
                md_notes = st.text_area("Official Feedback Review Comments", value=current_eval.get("md_comments", ""))
                
                if st.button("Save Evaluation Review Verdict", type="primary"):
                    def _save_eval(fresh, target=sub_to_audit, status=eval_status, p=p_score, t=t_score, notes=md_notes, evaluator=current_user["name"]):
                        for s in fresh.get("submissions", []):
                            if s.get("id") == target.get("id") or (s["name"] == target["name"] and s["song"] == target["song"] and s["timestamp"] == target["timestamp"]):
                                s["evaluation"] = {
                                    "status": status,
                                    "pitch_score": p,
                                    "timing_score": t,
                                    "md_comments": notes,
                                    "evaluated_by": evaluator,
                                    "evaluated_at": datetime.now().strftime("%Y-%m-%d %H:%M")
                                }
                                return True
                        return False
                    db, found = safe_db_update(_save_eval)
                    if found:
                        st.toast(f"Evaluation saved for {sub_to_audit['name']}!", icon="✅")
                        st.success(f"✅ **Evaluation saved!** {sub_to_audit['name']} — '{sub_to_audit['song']}' marked **{eval_status}** (Pitch: {p_score}/10, Timing: {t_score}/10)")
                    else:
                        st.error("Couldn't find that submission anymore — it may have been removed.")

    with active_tabs[-1]:
        st.subheader("🔍 Independent AI Song Key Extractor Profile")
        standalone_input = st.text_input("Input Box:", placeholder="Paste link or type song name here...", key="standalone_search")
        
        if st.button("🚀 Find Exact Key (Link/Search)", type="primary", use_container_width=True):
            if not standalone_input:
                st.warning("Please enter a link or song name first!")
            else:
                with st.spinner("Sourcing and streaming audio elements..."):
                    try:
                        detected_title, detected_artist = None, None
                        active_query = standalone_input
                        is_spotify = False
                        
                        if "spotify" in standalone_input.lower():
                            st.info("🎯 Spotify Link Detected! Fetching metadata...")
                            spotify_query, spot_title, spot_artist = get_spotify_search_term(standalone_input)
                            if spotify_query:
                                active_query, detected_title, detected_artist, is_spotify = spotify_query, spot_title, spot_artist, True
                        
                        target_wav, yt_title, yt_uploader = download_by_search_or_link(active_query)
                        status, result = analyze_song_key(target_wav)
                        
                        if status == "Success":
                            st.write("---")
                            if is_spotify and detected_title and detected_artist:
                                st.markdown(f"🎵 **Track Identified:** `{detected_title}` — *by {detected_artist}*")
                            else:
                                st.markdown(f"🎵 **Source Track:** `{yt_title}` — *via {yt_uploader}*")
                            st.success(f"## **Exact Song Key: {result}**")
                        else: st.error(f"Analysis Bottleneck: {result}")
                        if os.path.exists(target_wav): os.remove(target_wav)
                    except Exception as err: st.error(f"Extraction failed: {err}")
