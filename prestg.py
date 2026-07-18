#  300 hour expiry after first use
from flask import Flask, request, jsonify, send_from_directory, Response, render_template_string
from flask_cors import CORS
import os
import re
import json
import subprocess
from datetime import datetime, timedelta
import base64
import hashlib
import mimetypes
import threading
import time
import uuid
import secrets
from functools import wraps
from io import BytesIO
from xml.sax.saxutils import escape as xml_escape
from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.lib import colors
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer

app = Flask(__name__)
CORS(app)

# All data files/folders are anchored to this script's own directory, not the
# process's current working directory. Relying on cwd is fragile: it depends
# on *where the server happens to be launched from* (a different terminal, a
# service manager, a cron job, etc.), and a mismatch causes errors like
# "[Errno 2] No such file or directory: 'users_db.json'" even though the app
# looks fine. Anchoring to __file__ makes storage location independent of
# how/where the process is started.
BASE_DIR = os.path.dirname(os.path.abspath(__file__))

def _data_path(filename):
    return os.path.join(BASE_DIR, filename)

# Configuration
UPLOAD_FOLDER = _data_path('MergeTV')
THUMBNAIL_FOLDER = _data_path('thumbnails')
ALLOWED_EXTENSIONS = {'mp4', 'avi', 'mov', 'mkv', 'webm', 'flv', 'wmv', 'm4v'}
MAX_CONTENT_LENGTH = 500 * 1024 * 1024
MAX_FILES_PER_UPLOAD = 20
TRIAL_HOURS = 300  # 300 hour trial period

# Create folders
os.makedirs(UPLOAD_FOLDER, exist_ok=True)
os.makedirs(THUMBNAIL_FOLDER, exist_ok=True)

app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER
app.config['THUMBNAIL_FOLDER'] = THUMBNAIL_FOLDER
app.config['MAX_CONTENT_LENGTH'] = MAX_CONTENT_LENGTH * MAX_FILES_PER_UPLOAD

# Channel definitions
CHANNELS = [
    {
        'id': 'english1',
        'name': 'English1 Teacher',
        'icon': 'fas fa-book',
        'color': '#28a745',
        'description': 'English language and literature lessons'
    },
    {
        'id': 'math1',
        'name': 'Math1 Teacher',
        'icon': 'fas fa-calculator',
        'color': '#007bff',
        'description': 'Mathematics fundamentals and problem solving'
    },
    {
        'id': 'science1',
        'name': 'Science1 Teacher',
        'icon': 'fas fa-flask',
        'color': '#dc3545',
        'description': 'Science concepts and experiments'
    }
]

CHANNEL_DB_FILE = _data_path('channel_db.json')
TRIAL_DB_FILE = _data_path('trial_db.json')
RATINGS_DB_FILE = _data_path('ratings_db.json')
QUIZ_DB_FILE = _data_path('quiz_db.json')
QUIZ_RESULTS_FILE = _data_path('quiz_results_db.json')
USERS_DB_FILE = _data_path('users_db.json')
UPLOAD_LOCK = threading.Lock()
RATING_LOCK = threading.Lock()
QUIZ_LOCK = threading.Lock()
USERS_LOCK = threading.Lock()

# Merge Nursing Review branding logo (embedded so the app stays a single file).
# Decoded once to disk on startup and reused for PDF generation.
PRESTIGE_LOGO_BASE64 = (
    "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"
)
BRANDING_DIR = os.path.join(BASE_DIR, 'branding')
os.makedirs(BRANDING_DIR, exist_ok=True)
BRANDING_LOGO_PATH = os.path.join(BRANDING_DIR, 'prestige_logo.png')
if not os.path.exists(BRANDING_LOGO_PATH):
    try:
        with open(BRANDING_LOGO_PATH, 'wb') as _logo_f:
            _logo_f.write(base64.b64decode(PRESTIGE_LOGO_BASE64))
    except Exception:
        pass

def load_channel_db():
    if os.path.exists(CHANNEL_DB_FILE):
        try:
            with open(CHANNEL_DB_FILE, 'r') as f:
                return json.load(f)
        except:
            return {}
    return {}

def save_channel_db(db):
    with open(CHANNEL_DB_FILE, 'w') as f:
        json.dump(db, f, indent=2)

def load_trial_db():
    if os.path.exists(TRIAL_DB_FILE):
        try:
            with open(TRIAL_DB_FILE, 'r') as f:
                return json.load(f)
        except:
            return {}
    return {}

def save_trial_db(db):
    with open(TRIAL_DB_FILE, 'w') as f:
        json.dump(db, f, indent=2)

def load_ratings_db():
    if os.path.exists(RATINGS_DB_FILE):
        try:
            with open(RATINGS_DB_FILE, 'r') as f:
                return json.load(f)
        except:
            return {}
    return {}

def save_ratings_db(db):
    with open(RATINGS_DB_FILE, 'w') as f:
        json.dump(db, f, indent=2)

def rating_key(channel_id, filename):
    return f"{channel_id}/{filename}"

def get_rating_entry(db, channel_id, filename):
    key = rating_key(channel_id, filename)
    if key not in db:
        db[key] = {'likes': 0, 'dislikes': 0, 'shares': 0, 'voters': {}}
    else:
        db[key].setdefault('likes', 0)
        db[key].setdefault('dislikes', 0)
        db[key].setdefault('shares', 0)
        db[key].setdefault('voters', {})
    return db[key]

def load_quiz_db():
    if os.path.exists(QUIZ_DB_FILE):
        try:
            with open(QUIZ_DB_FILE, 'r') as f:
                return json.load(f)
        except:
            return {}
    return {}

def save_quiz_db(db):
    with open(QUIZ_DB_FILE, 'w') as f:
        json.dump(db, f, indent=2)

def load_quiz_results_db():
    if os.path.exists(QUIZ_RESULTS_FILE):
        try:
            with open(QUIZ_RESULTS_FILE, 'r') as f:
                return json.load(f)
        except:
            return {}
    return {}

def save_quiz_results_db(db):
    with open(QUIZ_RESULTS_FILE, 'w') as f:
        json.dump(db, f, indent=2)

def quiz_key(channel_id, filename):
    return f"{channel_id}/{filename}"

# ---------------------------------------------------------------------------
# User accounts (registration is required before the app can be used)
# ---------------------------------------------------------------------------

def load_users_db():
    if os.path.exists(USERS_DB_FILE):
        try:
            with open(USERS_DB_FILE, 'r') as f:
                return json.load(f)
        except:
            return {}
    return {}

def save_users_db(db):
    with open(USERS_DB_FILE, 'w') as f:
        json.dump(db, f, indent=2)

def hash_password(password, salt=None):
    """PBKDF2-style salted hash so plaintext passwords are never stored."""
    if salt is None:
        salt = secrets.token_hex(16)
    digest = hashlib.sha256((salt + password).encode('utf-8')).hexdigest()
    return salt, digest

def verify_password(password, salt, expected_digest):
    _, digest = hash_password(password, salt)
    return secrets.compare_digest(digest, expected_digest)

# ---------------------------------------------------------------------------
# Login tokens
#
# We deliberately do NOT use Flask's cookie-based session here. This app is
# usually opened as a local HTML file (or from a different port) talking to
# the Flask server on localhost:5000, and browsers frequently refuse to
# store/send cross-origin cookies (SameSite/third-party-cookie blocking),
# which makes the login silently fail. A simple bearer token avoids that
# entirely: the client stores the token itself (in localStorage) and sends
# it back on every request, which works regardless of origin.
# ---------------------------------------------------------------------------
AUTH_TOKENS = {}  # token -> {'username':..., 'display_name':..., 'created_at':...}
AUTH_TOKENS_LOCK = threading.Lock()

def create_token(username, display_name):
    token = secrets.token_hex(24)
    with AUTH_TOKENS_LOCK:
        AUTH_TOKENS[token] = {
            'username': username,
            'display_name': display_name,
            'created_at': datetime.now().isoformat()
        }
    return token

def get_user_from_token(token):
    if not token:
        return None
    with AUTH_TOKENS_LOCK:
        return AUTH_TOKENS.get(token)

def get_request_token():
    """Reads the bearer token from the Authorization header (used by normal
    fetch() calls), falling back to a ?token= query param for the handful
    of endpoints that are opened as plain links/new tabs (video streaming,
    downloads, PDF export) where custom headers can't be attached."""
    auth_header = request.headers.get('Authorization', '')
    if auth_header.startswith('Bearer '):
        return auth_header[7:].strip()
    return request.args.get('token', '').strip()

def login_required(view_func):
    """Blocks access until the visitor has registered/logged in."""
    @wraps(view_func)
    def wrapped(*args, **kwargs):
        user = get_user_from_token(get_request_token())
        if not user:
            return jsonify({'error': 'Please log in to continue.', 'auth_required': True}), 401
        request.current_username = user['username']
        request.current_display_name = user['display_name']
        return view_func(*args, **kwargs)
    return wrapped

def check_trial_status(client_ip):
    """Check if the trial has expired for a given IP"""
    db = load_trial_db()
    
    if client_ip not in db:
        # First time user - create trial record
        db[client_ip] = {
            'first_use': datetime.now().isoformat(),
            'trial_hours': TRIAL_HOURS
        }
        save_trial_db(db)
        return True, TRIAL_HOURS, None
    
    # Calculate hours elapsed
    first_use = datetime.fromisoformat(db[client_ip]['first_use'])
    hours_elapsed = (datetime.now() - first_use).total_seconds() / 3600
    hours_remaining = max(0, TRIAL_HOURS - hours_elapsed)
    
    if hours_remaining <= 0:
        return False, 0, "you have reached the maximum trial hours for this software."
    
    return True, hours_remaining, None

def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

def format_size(bytes):
    if bytes == 0:
        return '0 MB'
    mb = bytes / (1024 * 1024)
    return f'{mb:.2f} MB' if mb >= 0.01 else '< 0.01 MB'

def sanitize_filename(filename):
    filename = os.path.basename(filename)
    filename = filename.replace(' ', '_')
    filename = re.sub(r'[^a-zA-Z0-9._-]', '', filename)
    return filename

def get_unique_filename(directory, filename):
    base, ext = os.path.splitext(filename)
    counter = 1
    new_filename = filename
    while os.path.exists(os.path.join(directory, new_filename)):
        new_filename = f"{base}_{counter}{ext}"
        counter += 1
    return new_filename

def get_video_duration(file_path):
    try:
        cmd = ['ffprobe', '-v', 'error', '-show_entries', 'format=duration', 
               '-of', 'default=noprint_wrappers=1:nokey=1', file_path]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
        if result.returncode == 0 and result.stdout.strip():
            return float(result.stdout.strip())
        return 0
    except Exception as e:
        print(f"Error getting duration: {e}")
        return 0

def format_duration(seconds):
    if seconds <= 0:
        return "--:--"
    hours = int(seconds // 3600)
    minutes = int((seconds % 3600) // 60)
    secs = int(seconds % 60)
    if hours > 0:
        return f"{hours:02d}:{minutes:02d}:{secs:02d}"
    else:
        return f"{minutes:02d}:{secs:02d}"

def generate_thumbnail(video_path, thumbnail_path):
    try:
        duration = get_video_duration(video_path)
        if duration <= 0:
            return False
        
        timestamp = min(duration * 0.1, duration - 1)
        if timestamp < 0:
            timestamp = 1
        
        cmd = [
            'ffmpeg',
            '-ss', str(timestamp),
            '-i', video_path,
            '-vframes', '1',
            '-vf', 'scale=320:-1',
            '-y',
            thumbnail_path
        ]
        result = subprocess.run(cmd, capture_output=True, timeout=30)
        return result.returncode == 0 and os.path.exists(thumbnail_path)
    except Exception as e:
        print(f"Error generating thumbnail: {e}")
        return False

def generate_thumbnail_base64(video_path):
    try:
        hash_obj = hashlib.md5(video_path.encode())
        thumbnail_filename = hash_obj.hexdigest() + '.png'
        thumbnail_path = os.path.join(app.config['THUMBNAIL_FOLDER'], thumbnail_filename)
        
        if os.path.exists(thumbnail_path):
            with open(thumbnail_path, 'rb') as f:
                return base64.b64encode(f.read()).decode('utf-8')
        
        if generate_thumbnail(video_path, thumbnail_path):
            with open(thumbnail_path, 'rb') as f:
                return base64.b64encode(f.read()).decode('utf-8')
        return None
    except Exception as e:
        print(f"Error generating thumbnail base64: {e}")
        return None

def _draw_pdf_branding_header(canvas_obj, doc):
    """Draws the Merge Nursing Review logo in the upper-right corner of every page."""
    canvas_obj.saveState()
    try:
        if os.path.exists(BRANDING_LOGO_PATH):
            logo_w = 100
            logo_h = 100 * (108 / 221)  # preserve the source image's aspect ratio
            margin = 32
            page_w, page_h = doc.pagesize
            x = page_w - margin - logo_w
            y = page_h - margin - logo_h + 12
            canvas_obj.drawImage(
                BRANDING_LOGO_PATH, x, y, width=logo_w, height=logo_h,
                preserveAspectRatio=True, mask='auto'
            )
    except Exception as e:
        print(f"Error drawing PDF branding header: {e}")
    canvas_obj.restoreState()

def generate_quiz_results_pdf(result):
    """Builds a Quiz Results PDF for a single submission, with the branding logo
    positioned in the upper-right corner of every page."""
    buffer = BytesIO()
    doc = SimpleDocTemplate(
        buffer, pagesize=letter,
        topMargin=1.3 * inch, bottomMargin=0.75 * inch,
        leftMargin=0.75 * inch, rightMargin=0.75 * inch,
        title='Quiz Results'
    )
    styles = getSampleStyleSheet()
    title_style = ParagraphStyle('QuizTitle', parent=styles['Title'], textColor=colors.HexColor('#c8102e'), fontSize=22, spaceAfter=6)
    meta_style = ParagraphStyle('Meta', parent=styles['Normal'], fontSize=10.5, textColor=colors.HexColor('#333333'), spaceAfter=2)
    score_style = ParagraphStyle('Score', parent=styles['Heading1'], fontSize=18, textColor=colors.HexColor('#1f5a8a'), spaceBefore=14, spaceAfter=4)
    section_style = ParagraphStyle('Section', parent=styles['Heading2'], fontSize=13, textColor=colors.HexColor('#1f5a8a'), spaceBefore=12, spaceAfter=8)
    question_style = ParagraphStyle('Question', parent=styles['Normal'], fontSize=10.5, textColor=colors.HexColor('#111111'), spaceAfter=2, leading=14)
    answer_correct_style = ParagraphStyle('AnsCorrect', parent=styles['Normal'], fontSize=9.5, textColor=colors.HexColor('#1a7a3c'), leading=13)
    answer_wrong_style = ParagraphStyle('AnsWrong', parent=styles['Normal'], fontSize=9.5, textColor=colors.HexColor('#c8102e'), leading=13)

    flow = []
    flow.append(Paragraph('Quiz Results', title_style))
    flow.append(Paragraph(f"Video: {xml_escape(str(result.get('video_title', '')))}", meta_style))
    flow.append(Paragraph(f"Channel: {xml_escape(str(result.get('channel_name', '')))}", meta_style))
    flow.append(Paragraph(f"Student: {xml_escape(str(result.get('student_name', '')))}", meta_style))

    submitted = result.get('submitted_at', '')
    try:
        submitted_fmt = datetime.fromisoformat(submitted).strftime('%B %d, %Y %I:%M %p')
    except Exception:
        submitted_fmt = submitted
    flow.append(Paragraph(f"Date: {xml_escape(str(submitted_fmt))}", meta_style))
    flow.append(Spacer(1, 8))

    score = result.get('score', 0)
    total = result.get('total', 0)
    percentage = result.get('percentage', 0)
    flow.append(Paragraph(f"Score: {score} / {total} ({percentage}%)", score_style))
    flow.append(Spacer(1, 6))

    flow.append(Paragraph('Question Breakdown', section_style))

    for i, item in enumerate(result.get('breakdown', []), start=1):
        question_text = xml_escape(str(item.get('question', '')))
        your_answer = xml_escape(str(item.get('your_answer', '')))
        correct_answer = xml_escape(str(item.get('correct_answer', '')))
        is_correct = bool(item.get('correct'))

        flow.append(Paragraph(f"{i}. {question_text}", question_style))
        mark = '&#10003;' if is_correct else '&#10007;'
        style = answer_correct_style if is_correct else answer_wrong_style
        flow.append(Paragraph(f"{mark} Your answer: {your_answer}", style))
        if not is_correct:
            flow.append(Paragraph(f"Correct answer: {correct_answer}", answer_correct_style))
        flow.append(Spacer(1, 8))

    doc.build(flow, onFirstPage=_draw_pdf_branding_header, onLaterPages=_draw_pdf_branding_header)
    buffer.seek(0)
    return buffer

def process_single_file(file, channel_id, description='', downloadable=False, uploaded_by=''):
    try:
        if not file or file.filename == '':
            return None, 'No file selected'
        
        if not allowed_file(file.filename):
            return None, f'File type not allowed: {file.filename}'
        
        channel = next((c for c in CHANNELS if c['id'] == channel_id), None)
        if not channel:
            return None, 'Invalid channel'
        
        original_filename = sanitize_filename(file.filename)
        channel_folder = os.path.join(app.config['UPLOAD_FOLDER'], channel_id)
        os.makedirs(channel_folder, exist_ok=True)
        
        final_filename = get_unique_filename(channel_folder, original_filename)
        file_path = os.path.join(channel_folder, final_filename)
        file.save(file_path)
        
        duration_seconds = get_video_duration(file_path)
        duration_formatted = format_duration(duration_seconds)
        thumbnail_base64 = generate_thumbnail_base64(file_path)
        
        file_size = os.path.getsize(file_path)
        
        # Keep descriptions reasonably sized and free of stray whitespace
        description = (description or '').strip()[:2000]
        
        return {
            'filename': final_filename,
            'original_name': original_filename,
            'size': file_size,
            'duration_seconds': duration_seconds,
            'duration_formatted': duration_formatted,
            'uploaded_at': datetime.now().isoformat(),
            'path': file_path,
            'thumbnail': thumbnail_base64,
            'description': description,
            'downloadable': bool(downloadable),
            'uploaded_by': uploaded_by
        }, None
        
    except Exception as e:
        return None, str(e)

@app.route('/')
def index():
    # Check trial status
    client_ip = request.remote_addr
    is_valid, hours_remaining, error_message = check_trial_status(client_ip)
    
    if not is_valid:
        # Return expired page
        expired_html = """
        <!DOCTYPE html>
        <html>
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <title>Trial Expired</title>
            <style>
                * { margin: 0; padding: 0; box-sizing: border-box; }
                body {
                    display: flex;
                    justify-content: center;
                    align-items: center;
                    min-height: 100vh;
                    background: #d4e6f5;
                    font-family: 'Inter', -apple-system, BlinkMacSystemFont, sans-serif;
                }
                .expired-container {
                    background: white;
                    padding: 60px 50px;
                    border-radius: 20px;
                    text-align: center;
                    max-width: 500px;
                    box-shadow: 0 20px 60px rgba(0,0,0,0.15);
                    border: 1px solid #b0c8dd;
                }
                .expired-container .icon {
                    font-size: 80px;
                    color: #dc3545;
                    margin-bottom: 20px;
                }
                .expired-container h1 {
                    color: #0b1e2e;
                    font-size: 28px;
                    margin-bottom: 15px;
                }
                .expired-container p {
                    color: #4a6a8a;
                    font-size: 18px;
                    line-height: 1.6;
                    margin-bottom: 10px;
                }
                .expired-container .message {
                    background: #f8d7da;
                    color: #721c24;
                    padding: 15px 20px;
                    border-radius: 10px;
                    margin: 20px 0;
                    border: 1px solid #f5c6cb;
                    font-weight: 500;
                }
                .expired-container .small-note {
                    font-size: 14px;
                    color: #6c757d;
                    margin-top: 15px;
                }
            </style>
        </head>
        <body>
            <div class="expired-container">
                <div class="icon">⏰</div>
                <h1>Trial Expired</h1>
                <div class="message">you have reached the maximum trial hours for this software.</div>
                <p>Please contact the administrator to extend your trial or purchase a license.</p>
                <div class="small-note">Thank you for using MergeMedia</div>
            </div>
        </body>
        </html>
        """
        return expired_html, 403
    
    return send_from_directory('.', 'index.html')

@app.route('/api/trial-status', methods=['GET'])
def trial_status():
    """Check trial status and return hours remaining"""
    client_ip = request.remote_addr
    is_valid, hours_remaining, error_message = check_trial_status(client_ip)
    
    return jsonify({
        'valid': is_valid,
        'hours_remaining': round(hours_remaining, 2),
        'trial_hours': TRIAL_HOURS,
        'expired': not is_valid,
        'message': error_message
    }), 200

@app.route('/auth/register', methods=['POST'])
def register():
    """Create a new account. Registration is required before using the app."""
    try:
        data = request.get_json(silent=True) or {}
        username = (data.get('username') or '').strip().lower()
        password = data.get('password') or ''
        display_name = (data.get('display_name') or username).strip()[:80]

        if not re.match(r'^[a-zA-Z0-9._-]{3,32}$', username):
            return jsonify({'error': 'Username must be 3-32 characters (letters, numbers, ._- only)'}), 400
        if len(password) < 6:
            return jsonify({'error': 'Password must be at least 6 characters'}), 400

        with USERS_LOCK:
            users_db = load_users_db()
            if username in users_db:
                return jsonify({'error': 'That username is already taken'}), 409

            salt, digest = hash_password(password)
            users_db[username] = {
                'username': username,
                'display_name': display_name or username,
                'salt': salt,
                'password_hash': digest,
                'created_at': datetime.now().isoformat()
            }
            save_users_db(users_db)

        token = create_token(username, display_name or username)

        return jsonify({
            'success': True,
            'token': token,
            'username': username,
            'display_name': display_name or username
        }), 201

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/auth/login', methods=['POST'])
def login():
    try:
        data = request.get_json(silent=True) or {}
        username = (data.get('username') or '').strip().lower()
        password = data.get('password') or ''

        with USERS_LOCK:
            users_db = load_users_db()
        user = users_db.get(username)

        if not user or not verify_password(password, user['salt'], user['password_hash']):
            return jsonify({'error': 'Invalid username or password'}), 401

        token = create_token(username, user.get('display_name', username))

        return jsonify({
            'success': True,
            'token': token,
            'username': username,
            'display_name': user.get('display_name', username)
        }), 200

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/auth/logout', methods=['POST'])
def logout():
    token = get_request_token()
    with AUTH_TOKENS_LOCK:
        AUTH_TOKENS.pop(token, None)
    return jsonify({'success': True}), 200

@app.route('/auth/me', methods=['GET'])
def me():
    user = get_user_from_token(get_request_token())
    if not user:
        return jsonify({'authenticated': False}), 200
    return jsonify({
        'authenticated': True,
        'username': user['username'],
        'display_name': user.get('display_name', user['username'])
    }), 200

@app.route('/channels', methods=['GET'])
@login_required
def get_channels():
    client_ip = request.remote_addr
    is_valid, _, error_message = check_trial_status(client_ip)
    if not is_valid:
        return jsonify({'error': error_message}), 403
    return jsonify({'channels': CHANNELS}), 200

@app.route('/upload', methods=['POST'])
@login_required
def upload_files():
    client_ip = request.remote_addr
    is_valid, _, error_message = check_trial_status(client_ip)
    if not is_valid:
        return jsonify({'error': error_message}), 403
    
    try:
        if 'videos' not in request.files:
            return jsonify({'error': 'No video files provided'}), 400
        
        files = request.files.getlist('videos')
        channel_id = request.form.get('channel', 'english1')
        
        # Optional per-file descriptions, sent as a JSON object mapping the
        # original (client-side) filename to its description text, e.g.
        # {"lesson1.mp4": "Intro to fractions"}. Also accept a JSON array
        # aligned by upload order as a fallback.
        descriptions_by_name = {}
        descriptions_by_index = []
        raw_descriptions = request.form.get('descriptions', '')
        if raw_descriptions:
            try:
                parsed_descriptions = json.loads(raw_descriptions)
                if isinstance(parsed_descriptions, dict):
                    descriptions_by_name = parsed_descriptions
                elif isinstance(parsed_descriptions, list):
                    descriptions_by_index = parsed_descriptions
            except (ValueError, TypeError):
                pass

        # Per-file "downloadable" choice, sent the same way as descriptions:
        # {"lesson1.mp4": true} or a boolean array aligned by upload order.
        downloadable_by_name = {}
        downloadable_by_index = []
        raw_downloadable = request.form.get('downloadable', '')
        if raw_downloadable:
            try:
                parsed_downloadable = json.loads(raw_downloadable)
                if isinstance(parsed_downloadable, dict):
                    downloadable_by_name = parsed_downloadable
                elif isinstance(parsed_downloadable, list):
                    downloadable_by_index = parsed_downloadable
            except (ValueError, TypeError):
                pass

        uploaded_by = request.current_username

        if not files or len(files) == 0:
            return jsonify({'error': 'No files selected'}), 400
        
        if len(files) > MAX_FILES_PER_UPLOAD:
            return jsonify({'error': f'Maximum {MAX_FILES_PER_UPLOAD} files allowed per upload'}), 400
        
        channel = next((c for c in CHANNELS if c['id'] == channel_id), None)
        if not channel:
            return jsonify({'error': 'Invalid channel'}), 400
        
        results = []
        errors = []
        successful_uploads = []
        
        with UPLOAD_LOCK:
            db = load_channel_db()
            if channel_id not in db:
                db[channel_id] = []
            
            for idx, file in enumerate(files):
                description = descriptions_by_name.get(file.filename, '')
                if not description and idx < len(descriptions_by_index):
                    description = descriptions_by_index[idx]

                downloadable = downloadable_by_name.get(file.filename)
                if downloadable is None and idx < len(downloadable_by_index):
                    downloadable = downloadable_by_index[idx]
                downloadable = bool(downloadable)

                file_info, error = process_single_file(file, channel_id, description, downloadable, uploaded_by)
                if error:
                    errors.append({'filename': file.filename, 'error': error})
                else:
                    db[channel_id].append(file_info)
                    successful_uploads.append({
                        'filename': file_info['filename'],
                        'original_name': file_info['original_name'],
                        'size_formatted': format_size(file_info['size']),
                        'duration_formatted': file_info['duration_formatted'],
                        'description': file_info['description'],
                        'downloadable': file_info['downloadable']
                    })
            
            save_channel_db(db)
        
        return jsonify({
            'success': True,
            'message': f'Uploaded {len(successful_uploads)} files to {channel["name"]}',
            'channel': channel_id,
            'successful': successful_uploads,
            'errors': errors,
            'total_uploaded': len(successful_uploads),
            'total_errors': len(errors)
        }), 200
        
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/list-files', methods=['GET'])
@login_required
def list_files():
    client_ip = request.remote_addr
    is_valid, _, error_message = check_trial_status(client_ip)
    if not is_valid:
        return jsonify({'error': error_message}), 403
    
    try:
        search_query = request.args.get('search', '').lower().strip()
        channel_filter = request.args.get('channel', '').strip()
        
        db = load_channel_db()
        ratings_db = load_ratings_db()
        all_files = []
        
        channels_to_process = [channel_filter] if channel_filter else [c['id'] for c in CHANNELS]
        
        for channel_id in channels_to_process:
            if channel_id in db:
                for file_info in db[channel_id]:
                    filename = file_info['filename']
                    description = file_info.get('description', '')
                    if search_query:
                        haystack = f"{filename} {file_info.get('original_name', '')} {description}".lower()
                        if search_query not in haystack:
                            continue
                    
                    channel = next((c for c in CHANNELS if c['id'] == channel_id), None)
                    channel_name = channel['name'] if channel else channel_id
                    duration_formatted = file_info.get('duration_formatted', '--:--')
                    thumbnail_base64 = file_info.get('thumbnail')
                    
                    if not thumbnail_base64:
                        file_path = file_info.get('path')
                        if file_path and os.path.exists(file_path):
                            thumbnail_base64 = generate_thumbnail_base64(file_path)
                            file_info['thumbnail'] = thumbnail_base64
                            save_channel_db(db)
                    
                    rating_entry = ratings_db.get(rating_key(channel_id, filename), {})
                    
                    all_files.append({
                        'name': filename,
                        'original_name': file_info.get('original_name', filename),
                        'size': file_info['size'],
                        'size_formatted': format_size(file_info['size']),
                        'duration_seconds': file_info.get('duration_seconds', 0),
                        'duration_formatted': duration_formatted,
                        'channel': channel_id,
                        'channel_name': channel_name,
                        'uploaded_at': file_info.get('uploaded_at', ''),
                        'thumbnail': thumbnail_base64,
                        'path': file_info.get('path', ''),
                        'description': file_info.get('description', ''),
                        'likes': rating_entry.get('likes', 0),
                        'dislikes': rating_entry.get('dislikes', 0),
                        'shares': rating_entry.get('shares', 0),
                        'user_vote': rating_entry.get('voters', {}).get(client_ip),
                        'downloadable': file_info.get('downloadable', False),
                        'uploaded_by': file_info.get('uploaded_by', ''),
                        'is_owner': file_info.get('uploaded_by', '') == request.current_username
                    })
        
        all_files.sort(key=lambda x: x['uploaded_at'], reverse=True)
        total_size = sum(f['size'] for f in all_files)
        
        return jsonify({
            'files': all_files,
            'count': len(all_files),
            'total_hits': len(all_files),
            'total_size': total_size,
            'total_size_formatted': format_size(total_size)
        }), 200
        
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/check-duplicate', methods=['POST'])
@login_required
def check_duplicate():
    """Check whether any of the given filenames already exist in a channel."""
    client_ip = request.remote_addr
    is_valid, _, error_message = check_trial_status(client_ip)
    if not is_valid:
        return jsonify({'error': error_message}), 403

    try:
        data = request.get_json(silent=True) or {}
        channel_id = data.get('channel', '')
        filenames = data.get('filenames', [])

        if not channel_id or not filenames:
            return jsonify({'duplicates': []}), 200

        db = load_channel_db()
        existing_files = db.get(channel_id, [])

        existing_names = set()
        for f in existing_files:
            if f.get('original_name'):
                existing_names.add(f['original_name'].lower())
            if f.get('filename'):
                existing_names.add(f['filename'].lower())

        duplicates = []
        for filename in filenames:
            sanitized = sanitize_filename(filename).lower()
            if sanitized in existing_names or filename.lower() in existing_names:
                duplicates.append(filename)

        return jsonify({'duplicates': duplicates}), 200

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/rate/<channel_id>/<filename>', methods=['POST'])
@login_required
def rate_video(channel_id, filename):
    """Thumbs up / thumbs down a video. One active vote per client IP; clicking the
    same button again removes the vote, clicking the other switches it."""
    client_ip = request.remote_addr
    is_valid, _, error_message = check_trial_status(client_ip)
    if not is_valid:
        return jsonify({'error': error_message}), 403

    try:
        if '..' in channel_id or '..' in filename:
            return jsonify({'error': 'Invalid path'}), 403

        data = request.get_json(silent=True) or {}
        action = data.get('action')
        if action not in ('like', 'dislike'):
            return jsonify({'error': 'action must be "like" or "dislike"'}), 400

        with RATING_LOCK:
            db = load_ratings_db()
            entry = get_rating_entry(db, channel_id, filename)
            previous_vote = entry['voters'].get(client_ip)

            if previous_vote == action:
                # Clicking the same button again removes the vote
                entry[f'{action}s'] = max(0, entry[f'{action}s'] - 1)
                del entry['voters'][client_ip]
                new_vote = None
            else:
                if previous_vote:
                    entry[f'{previous_vote}s'] = max(0, entry[f'{previous_vote}s'] - 1)
                entry[f'{action}s'] += 1
                entry['voters'][client_ip] = action
                new_vote = action

            save_ratings_db(db)

        return jsonify({
            'likes': entry['likes'],
            'dislikes': entry['dislikes'],
            'shares': entry.get('shares', 0),
            'user_vote': new_vote
        }), 200

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/share/<channel_id>/<filename>', methods=['POST'])
@login_required
def share_video(channel_id, filename):
    """Record a share and return a shareable link for the video."""
    client_ip = request.remote_addr
    is_valid, _, error_message = check_trial_status(client_ip)
    if not is_valid:
        return jsonify({'error': error_message}), 403

    try:
        if '..' in channel_id or '..' in filename:
            return jsonify({'error': 'Invalid path'}), 403

        with RATING_LOCK:
            db = load_ratings_db()
            entry = get_rating_entry(db, channel_id, filename)
            entry['shares'] = entry.get('shares', 0) + 1
            save_ratings_db(db)
            share_count = entry['shares']

        share_url = f"{request.host_url.rstrip('/')}/stream/{channel_id}/{filename}"

        return jsonify({
            'shares': share_count,
            'share_url': share_url
        }), 200

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/stream/<channel_id>/<filename>')
@login_required
def stream_video(channel_id, filename):
    client_ip = request.remote_addr
    is_valid, _, error_message = check_trial_status(client_ip)
    if not is_valid:
        return jsonify({'error': error_message}), 403
    
    try:
        if '..' in channel_id or '..' in filename:
            return jsonify({'error': 'Invalid path'}), 403
        
        file_path = os.path.join(app.config['UPLOAD_FOLDER'], channel_id, filename)
        if not os.path.exists(file_path):
            return jsonify({'error': 'File not found'}), 404
        
        file_size = os.path.getsize(file_path)
        range_header = request.headers.get('Range', None)
        
        if not range_header:
            response = send_from_directory(
                os.path.join(app.config['UPLOAD_FOLDER'], channel_id),
                filename,
                as_attachment=False,
                download_name=None
            )
            response.headers['Content-Disposition'] = 'inline'
            response.headers['Accept-Ranges'] = 'bytes'
            return response
        
        byte_range = range_header.replace('bytes=', '').split('-')
        start = int(byte_range[0]) if byte_range[0] else 0
        end = int(byte_range[1]) if byte_range[1] else file_size - 1
        
        if start >= file_size or end >= file_size:
            return jsonify({'error': 'Range not satisfiable'}), 416
        
        content_length = end - start + 1
        
        with open(file_path, 'rb') as f:
            f.seek(start)
            data = f.read(content_length)
        
        mime_type, _ = mimetypes.guess_type(file_path)
        if not mime_type:
            mime_type = 'video/mp4'
        
        response = Response(
            data,
            status=206,
            mimetype=mime_type,
            direct_passthrough=True
        )
        response.headers['Content-Range'] = f'bytes {start}-{end}/{file_size}'
        response.headers['Content-Length'] = str(content_length)
        response.headers['Accept-Ranges'] = 'bytes'
        response.headers['Content-Disposition'] = 'inline'
        response.headers['Cache-Control'] = 'no-cache, no-store, must-revalidate'
        response.headers['Pragma'] = 'no-cache'
        response.headers['Expires'] = '0'
        
        return response
        
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/download/<channel_id>/<filename>', methods=['GET'])
@login_required
def download_file(channel_id, filename):
    """Serves the raw video file as an attachment, but only when the
    uploader has marked that specific video as downloadable."""
    client_ip = request.remote_addr
    is_valid, _, error_message = check_trial_status(client_ip)
    if not is_valid:
        return jsonify({'error': error_message}), 403

    try:
        if '..' in channel_id or '..' in filename:
            return jsonify({'error': 'Invalid path'}), 403

        with UPLOAD_LOCK:
            db = load_channel_db()
        file_entry = next((f for f in db.get(channel_id, []) if f['filename'] == filename), None)

        if not file_entry:
            return jsonify({'error': 'File not found'}), 404

        if not file_entry.get('downloadable', False):
            return jsonify({'error': 'The uploader has not enabled downloads for this video.'}), 403

        file_path = os.path.join(app.config['UPLOAD_FOLDER'], channel_id, filename)
        if not os.path.exists(file_path):
            return jsonify({'error': 'File not found on disk'}), 404

        download_name = file_entry.get('original_name', filename)
        return send_from_directory(
            os.path.join(app.config['UPLOAD_FOLDER'], channel_id),
            filename,
            as_attachment=True,
            download_name=download_name
        )

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/toggle-download/<channel_id>/<filename>', methods=['POST'])
@login_required
def toggle_download(channel_id, filename):
    """Lets the uploader flip a video between downloadable and streaming-only."""
    client_ip = request.remote_addr
    is_valid, _, error_message = check_trial_status(client_ip)
    if not is_valid:
        return jsonify({'error': error_message}), 403

    try:
        if '..' in channel_id or '..' in filename:
            return jsonify({'error': 'Invalid path'}), 403

        username = request.current_username

        with UPLOAD_LOCK:
            db = load_channel_db()
            file_entry = next((f for f in db.get(channel_id, []) if f['filename'] == filename), None)

            if not file_entry:
                return jsonify({'error': 'File not found'}), 404

            if file_entry.get('uploaded_by') and file_entry.get('uploaded_by') != username:
                return jsonify({'error': 'Only the uploader can change this setting'}), 403

            data = request.get_json(silent=True) or {}
            if 'downloadable' in data:
                file_entry['downloadable'] = bool(data['downloadable'])
            else:
                file_entry['downloadable'] = not file_entry.get('downloadable', False)

            save_channel_db(db)

        return jsonify({'success': True, 'downloadable': file_entry['downloadable']}), 200

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/delete/<channel_id>/<filename>', methods=['DELETE'])
@login_required
def delete_file(channel_id, filename):
    """Lets the uploader permanently delete one of their own uploaded videos:
    removes the file from disk plus its channel-db entry, rating, quiz, and
    quiz-result records."""
    try:
        if '..' in channel_id or '..' in filename:
            return jsonify({'error': 'Invalid path'}), 403

        username = request.current_username

        with UPLOAD_LOCK:
            db = load_channel_db()
            channel_files = db.get(channel_id, [])
            file_entry = next((f for f in channel_files if f['filename'] == filename), None)

            if not file_entry:
                return jsonify({'error': 'File not found'}), 404

            if file_entry.get('uploaded_by') and file_entry.get('uploaded_by') != username:
                return jsonify({'error': 'Only the uploader can delete this video'}), 403

            file_path = file_entry.get('path')

            db[channel_id] = [f for f in channel_files if f['filename'] != filename]
            save_channel_db(db)

        # Remove the physical file. Best-effort: the DB entry is already
        # gone either way, so a missing/locked file shouldn't block the response.
        if file_path and os.path.exists(file_path):
            try:
                os.remove(file_path)
            except OSError:
                pass

        # Clean up any rating tallies tied to this video.
        with RATING_LOCK:
            ratings_db = load_ratings_db()
            rkey = rating_key(channel_id, filename)
            if rkey in ratings_db:
                del ratings_db[rkey]
                save_ratings_db(ratings_db)

        # Clean up any quiz (and its submitted results) tied to this video.
        with QUIZ_LOCK:
            quiz_db = load_quiz_db()
            qkey = quiz_key(channel_id, filename)
            if qkey in quiz_db:
                del quiz_db[qkey]
                save_quiz_db(quiz_db)

            results_db = load_quiz_results_db()
            remaining_results = {
                rid: r for rid, r in results_db.items()
                if not (r.get('channel_id') == channel_id and r.get('filename') == filename)
            }
            if len(remaining_results) != len(results_db):
                save_quiz_results_db(remaining_results)

        return jsonify({'success': True, 'filename': filename, 'channel': channel_id}), 200

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/quiz/<channel_id>/<filename>', methods=['GET'])
@login_required
def get_quiz(channel_id, filename):
    """Public quiz view for students: questions and options only, no correct answers."""
    try:
        if '..' in channel_id or '..' in filename:
            return jsonify({'error': 'Invalid path'}), 403

        with QUIZ_LOCK:
            db = load_quiz_db()
        entry = db.get(quiz_key(channel_id, filename))

        if not entry or not entry.get('questions'):
            return jsonify({'exists': False, 'questions': []}), 200

        public_questions = [
            {'id': q['id'], 'type': q['type'], 'question': q['question'], 'options': q.get('options', [])}
            for q in entry['questions']
        ]
        return jsonify({'exists': True, 'questions': public_questions}), 200

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/quiz/<channel_id>/<filename>/edit', methods=['GET'])
@login_required
def get_quiz_for_edit(channel_id, filename):
    """Full quiz view for teachers editing questions, including correct answers."""
    try:
        if '..' in channel_id or '..' in filename:
            return jsonify({'error': 'Invalid path'}), 403

        with QUIZ_LOCK:
            db = load_quiz_db()
        entry = db.get(quiz_key(channel_id, filename), {'questions': []})
        return jsonify({'questions': entry.get('questions', [])}), 200

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/quiz/<channel_id>/<filename>', methods=['POST'])
@login_required
def save_quiz(channel_id, filename):
    """Create or replace the quiz questions for a video."""
    client_ip = request.remote_addr
    is_valid, _, error_message = check_trial_status(client_ip)
    if not is_valid:
        return jsonify({'error': error_message}), 403

    try:
        if '..' in channel_id or '..' in filename:
            return jsonify({'error': 'Invalid path'}), 403

        data = request.get_json(silent=True) or {}
        raw_questions = data.get('questions')
        if not isinstance(raw_questions, list) or len(raw_questions) == 0:
            return jsonify({'error': 'At least one question is required'}), 400
        if len(raw_questions) > 50:
            return jsonify({'error': 'Maximum 50 questions per quiz'}), 400

        clean_questions = []
        for idx, q in enumerate(raw_questions):
            if not isinstance(q, dict):
                return jsonify({'error': f'Question {idx + 1}: invalid format'}), 400

            q_type = q.get('type')
            question_text = (q.get('question') or '').strip()[:500]

            if q_type not in ('mcq', 'tf'):
                return jsonify({'error': f'Question {idx + 1}: invalid type'}), 400
            if not question_text:
                return jsonify({'error': f'Question {idx + 1}: question text is required'}), 400

            if q_type == 'tf':
                options = ['True', 'False']
            else:
                options = [str(o).strip()[:200] for o in (q.get('options') or []) if str(o).strip()]
                if len(options) < 2:
                    return jsonify({'error': f'Question {idx + 1}: at least 2 options are required'}), 400
                options = options[:6]

            try:
                correct_index = int(q.get('correct_index'))
            except (TypeError, ValueError):
                return jsonify({'error': f'Question {idx + 1}: correct answer is required'}), 400
            if correct_index < 0 or correct_index >= len(options):
                return jsonify({'error': f'Question {idx + 1}: invalid correct answer'}), 400

            qid = q.get('id') or uuid.uuid4().hex[:8]
            clean_questions.append({
                'id': qid,
                'type': q_type,
                'question': question_text,
                'options': options,
                'correct_index': correct_index
            })

        with QUIZ_LOCK:
            db = load_quiz_db()
            db[quiz_key(channel_id, filename)] = {
                'questions': clean_questions,
                'updated_at': datetime.now().isoformat()
            }
            save_quiz_db(db)

        return jsonify({'success': True, 'count': len(clean_questions)}), 200

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/quiz/<channel_id>/<filename>', methods=['DELETE'])
@login_required
def delete_quiz(channel_id, filename):
    try:
        if '..' in channel_id or '..' in filename:
            return jsonify({'error': 'Invalid path'}), 403

        with QUIZ_LOCK:
            db = load_quiz_db()
            key = quiz_key(channel_id, filename)
            if key in db:
                del db[key]
                save_quiz_db(db)

        return jsonify({'success': True}), 200

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/quiz/<channel_id>/<filename>/submit', methods=['POST'])
@login_required
def submit_quiz(channel_id, filename):
    """Grade a student's answers server-side and store a result record for PDF export."""
    client_ip = request.remote_addr
    is_valid, _, error_message = check_trial_status(client_ip)
    if not is_valid:
        return jsonify({'error': error_message}), 403

    try:
        if '..' in channel_id or '..' in filename:
            return jsonify({'error': 'Invalid path'}), 403

        data = request.get_json(silent=True) or {}
        student_name = (data.get('student_name') or 'Student').strip()[:120] or 'Student'
        answers = data.get('answers') or {}
        if not isinstance(answers, dict):
            return jsonify({'error': 'answers must be an object'}), 400

        with QUIZ_LOCK:
            quiz_db = load_quiz_db()
        quiz_entry = quiz_db.get(quiz_key(channel_id, filename))

        if not quiz_entry or not quiz_entry.get('questions'):
            return jsonify({'error': 'No quiz found for this video'}), 404

        questions = quiz_entry['questions']
        total = len(questions)
        score = 0
        breakdown = []

        for q in questions:
            qid = q['id']
            options = q.get('options', [])
            correct_index = q.get('correct_index')
            given_index = answers.get(qid)

            is_correct = False
            if given_index is not None:
                try:
                    is_correct = int(given_index) == int(correct_index)
                except (TypeError, ValueError):
                    is_correct = False

            if is_correct:
                score += 1

            try:
                your_answer_text = options[int(given_index)] if given_index is not None else 'No answer'
            except (TypeError, ValueError, IndexError):
                your_answer_text = 'No answer'

            try:
                correct_answer_text = options[int(correct_index)]
            except (TypeError, ValueError, IndexError):
                correct_answer_text = ''

            breakdown.append({
                'question': q['question'],
                'your_answer': your_answer_text,
                'correct_answer': correct_answer_text,
                'correct': is_correct
            })

        percentage = round((score / total) * 100, 1) if total else 0

        channel = next((c for c in CHANNELS if c['id'] == channel_id), None)
        channel_name = channel['name'] if channel else channel_id

        video_title = filename
        with UPLOAD_LOCK:
            channel_db = load_channel_db()
            file_entry = next((f for f in channel_db.get(channel_id, []) if f['filename'] == filename), None)
            if file_entry:
                video_title = file_entry.get('original_name', filename)

        result_id = uuid.uuid4().hex[:12]
        result = {
            'result_id': result_id,
            'channel_id': channel_id,
            'filename': filename,
            'video_title': video_title,
            'channel_name': channel_name,
            'student_name': student_name,
            'score': score,
            'total': total,
            'percentage': percentage,
            'breakdown': breakdown,
            'submitted_at': datetime.now().isoformat()
        }

        with QUIZ_LOCK:
            results_db = load_quiz_results_db()
            results_db[result_id] = result
            save_quiz_results_db(results_db)

        return jsonify({
            'result_id': result_id,
            'score': score,
            'total': total,
            'percentage': percentage,
            'breakdown': breakdown
        }), 200

    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/quiz/<channel_id>/<filename>/result/<result_id>/pdf', methods=['GET'])
@login_required
def quiz_result_pdf(channel_id, filename, result_id):
    """Streams a Quiz Results PDF, branded with the Merge Nursing Review logo
    in the upper-right corner of every page."""
    client_ip = request.remote_addr
    is_valid, _, error_message = check_trial_status(client_ip)
    if not is_valid:
        return jsonify({'error': error_message}), 403

    try:
        if '..' in channel_id or '..' in filename:
            return jsonify({'error': 'Invalid path'}), 403

        with QUIZ_LOCK:
            results_db = load_quiz_results_db()
        result = results_db.get(result_id)

        if not result or result.get('channel_id') != channel_id or result.get('filename') != filename:
            return jsonify({'error': 'Quiz result not found'}), 404

        pdf_buffer = generate_quiz_results_pdf(result)
        safe_student = sanitize_filename(result.get('student_name', 'student')) or 'student'
        safe_video = sanitize_filename(os.path.splitext(filename)[0]) or 'video'
        download_name = f"QuizResults_{safe_student}_{safe_video}.pdf"

        return Response(
            pdf_buffer.read(),
            mimetype='application/pdf',
            headers={'Content-Disposition': f'attachment; filename="{download_name}"'}
        )

    except Exception as e:
        return jsonify({'error': str(e)}), 500

if __name__ == '__main__':
    print(f"🚀 MergeMedia Server Starting...")
    print(f"📁 Upload folder: {os.path.abspath(UPLOAD_FOLDER)}")
    print(f"🖼️  Thumbnail folder: {os.path.abspath(THUMBNAIL_FOLDER)}")
    print(f"📡 Channels: {', '.join([c['name'] for c in CHANNELS])}")
    print(f"📤 Max files per upload: {MAX_FILES_PER_UPLOAD}")
    print(f"⏰ Trial period: {TRIAL_HOURS} hours from first use")
    print(f"🔐 Registration/login required before use")
    print(f"⬇️  Videos are downloadable only if the uploader enables it per video")
    print(f"🌐 Server running at: http://localhost:5000")
    print(f"📝 Press Ctrl+C to stop")
    app.run(debug=True, host='0.0.0.0', port=5000)
