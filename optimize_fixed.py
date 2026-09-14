import asyncio
import os
import sys
import time
import logging
import signal
# FIX_OPT_1.4: subprocess is required by the script runner.
import subprocess
import functools
import psutil
import sqlite3
import hashlib
import json
import zipfile
from collections import defaultdict
import aiosqlite
from datetime import datetime, timedelta
from pathlib import Path
from pathlib import PurePosixPath
from typing import Optional, Dict, Any
from aiogram import Bot, Dispatcher, types, F
from aiogram.filters import Command
from aiogram.types import InlineKeyboardMarkup, InlineKeyboardButton, FSInputFile
from aiogram.fsm.storage.memory import MemoryStorage
from aiohttp import web
import aiohttp
from dotenv import load_dotenv

load_dotenv()

# ─── Logging ──────────────────────────────────────────────────────────────
BASE_DIR = Path(__file__).parent.absolute()
IROTECH_DIR = BASE_DIR / 'inf'
IROTECH_DIR.mkdir(exist_ok=True)

# FIX_OPT_4.4: structured file + console logging.
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)-7s | %(name)s | %(message)s",
    handlers=[
        logging.FileHandler(IROTECH_DIR / "bot.log"),
        logging.StreamHandler(),
    ],
)
logger = logging.getLogger(__name__)

# ─── Optional rich-message support (FIX_OPT_11) ──────────────────────────
try:
    from richmsg import (
        RichClient,
        RichMessageError,
        heading,
        paragraph,
        divider,
        spacer,
        quote,
        code as rich_code,
        bullet_list,
        checklist,
        compact_table,
        button_row,
        button_grid,
        rich_callback_button,
        rich_url_button,
        success_card,
        error_card,
        info_card,
        progress_card,
        stats_card,
        confirm_card,
        wizard_card,
        section_card,
        validate_blocks,
        extract_message_id,
    )
    RICH_AVAILABLE = True
except Exception as _rich_exc:
    logger.warning("richmsg unavailable, using HTML fallback: %s", _rich_exc)
    RICH_AVAILABLE = False

# ─── CONFIG ──────────────────────────────────────────────────────────────
# FIX_OPT_1.1: secrets are loaded from the environment; no hardcoded token/owner ID.
TOKEN = os.getenv("BOT_TOKEN")
OWNER_ID_RAW = os.getenv("OWNER_ID")
if not TOKEN:
    raise RuntimeError("BOT_TOKEN is missing. Put it in .env or the environment.")
if not OWNER_ID_RAW:
    raise RuntimeError("OWNER_ID is missing. Put it in .env or the environment.")
try:
    OWNER_ID = int(OWNER_ID_RAW)
except ValueError as exc:
    raise RuntimeError("OWNER_ID must be a numeric Telegram user ID.") from exc

try:
    ADMIN_ID = int(os.getenv("ADMIN_ID", str(OWNER_ID)))
except ValueError as exc:
    raise RuntimeError("ADMIN_ID must be a numeric Telegram user ID.") from exc
YOUR_USERNAME = os.getenv("YOUR_USERNAME", "Xalonexdev03")
UPDATE_CHANNEL = os.getenv("UPDATE_CHANNEL", "https://t.me/pdf_making_hub")
# FIX_OPT_4.2: web server port is configurable.
PORT = int(os.getenv("PORT", "5000"))
MAX_UPLOAD_BYTES = 50 * 1024 * 1024
MAX_EXTRACTED_BYTES = 200 * 1024 * 1024

UPLOAD_BOTS_DIR = BASE_DIR / 'upload_bots'
DATABASE_PATH = IROTECH_DIR / 'bot_data.db'

FREE_USER_LIMIT = 10
SUBSCRIBED_USER_LIMIT = 20
ADMIN_LIMIT = 999
OWNER_LIMIT = float('inf')

UPLOAD_BOTS_DIR.mkdir(exist_ok=True)
IROTECH_DIR.mkdir(exist_ok=True)

bot = Bot(token=TOKEN)
dp = Dispatcher(storage=MemoryStorage())

# FIX_OPT_3.2: singleton RichClient created once.
rich_client = None
if RICH_AVAILABLE:
    rich_client = RichClient(
        token=TOKEN,
        debug=True,  # FIX_RICH_SEND: TEMPORARY debug; flip back to False after VPS verification.
        max_attempts=3,
        timeout=15,
    )

# Semaphore to limit concurrent script executions
CONCURRENCY_LIMIT = 10
script_semaphore = asyncio.Semaphore(CONCURRENCY_LIMIT)

# FIX_OPT_2.5: one long-lived database connection.
db_conn: Optional[aiosqlite.Connection] = None
_db_lock: Optional[asyncio.Lock] = None


def _get_db_lock() -> asyncio.Lock:
    global _db_lock
    if _db_lock is None:
        _db_lock = asyncio.Lock()
    return _db_lock

bot_scripts: Dict[str, Dict[str, Any]] = {}
user_subscriptions = {}
user_files = {}
user_favorites = {}
banned_users = set()
active_users = set()
admin_ids = {ADMIN_ID, OWNER_ID}
bot_locked = False
pending_confirmations: Dict[int, Dict[str, Any]] = {}

# FIX_BUG_4: bound the lifetime of pending confirmation state.
_CONFIRM_TTL_SECONDS = 300

def _prune_pending_confirmations() -> None:
    """Drop abandoned confirmation entries older than the TTL."""
    if not pending_confirmations:
        return
    now = time.time()
    for uid in list(pending_confirmations.keys()):
        entry = pending_confirmations.get(uid)
        if not isinstance(entry, dict):
            pending_confirmations.pop(uid, None)
            continue
        created = entry.get("_created_at", 0)
        if now - created > _CONFIRM_TTL_SECONDS:
            pending_confirmations.pop(uid, None)


def _set_pending_confirmation(user_id: int, payload: dict) -> None:
    """Store a pending confirmation with a creation timestamp."""
    _prune_pending_confirmations()
    payload = dict(payload)
    payload["_created_at"] = time.time()
    pending_confirmations[user_id] = payload


def _take_pending_confirmation(user_id: int, expected_action: str):
    """Pop a pending confirmation if it matches the expected action."""
    _prune_pending_confirmations()
    entry = pending_confirmations.pop(user_id, None)
    if not isinstance(entry, dict):
        return None
    if entry.get("action") != expected_action:
        return None
    return entry
bot_stats = {'total_uploads': 0, 'total_downloads': 0, 'total_runs': 0}

# FIX_OPT_4 / FIX_OPT_3: upload throttling and per-script lifecycle tracking.
_upload_times: Dict[int, list] = defaultdict(list)
_script_watch_tasks: Dict[str, asyncio.Task] = {}
_shutdown_started = False


def _upload_allowed(user_id: int, max_per_min: int = 5) -> bool:
    now = asyncio.get_running_loop().time()
    times = [t for t in _upload_times[user_id] if now - t < 60]
    _upload_times[user_id] = times
    if len(times) >= max_per_min:
        return False
    times.append(now)
    return True


async def get_db() -> aiosqlite.Connection:
    global db_conn
    async with _get_db_lock():
        if db_conn is None:
            db_conn = await aiosqlite.connect(DATABASE_PATH)
            db_conn.row_factory = aiosqlite.Row
        return db_conn


async def close_db() -> None:
    global db_conn
    async with _get_db_lock():
        if db_conn is not None:
            await db_conn.close()
            db_conn = None


def _safe_filename(name: str) -> str:
    """Return a single safe filename; reject path components."""
    value = str(name or "")
    safe = Path(value).name
    if not value or safe != value or value in {".", ".."}:
        raise ValueError("unsafe filename")
    return safe

# FIX_ISSUE_1: friendly display for unlimited owner/admin file quotas.
def _format_limit(limit) -> str:
    """Friendly limit string for UI display."""
    if limit == float("inf"):
        return "∞"
    try:
        return str(int(limit))
    except (TypeError, ValueError):
        return str(limit)


# FIX_ISSUE_2: persist rich-card message IDs across VPS/bot restarts.
async def _save_tracked_message(user_id: int, key: str, message_id: int) -> None:
    try:
        conn = await get_db()
        await conn.execute(
            'INSERT OR REPLACE INTO config (key, value, updated_at) VALUES (?, ?, ?)',
            (f"tracked_{user_id}_{key}", str(int(message_id)), datetime.now().isoformat())
        )
        await conn.commit()
    except Exception:
        logger.exception("Failed to save tracked message")


async def _load_tracked_message(user_id: int, key: str) -> Optional[int]:
    try:
        conn = await get_db()
        cursor = await conn.execute(
            'SELECT value FROM config WHERE key = ?',
            (f"tracked_{user_id}_{key}",)
        )
        row = await cursor.fetchone()
        if row and row[0]:
            return int(row[0])
    except Exception:
        logger.debug("Failed to load tracked message", exc_info=True)
    return None


async def _delete_tracked_message(bot_instance, chat_id: int, user_id: int, key: str) -> None:
    mid = await _load_tracked_message(user_id, key)
    if mid:
        try:
            await bot_instance.delete_message(chat_id=chat_id, message_id=mid)
        except Exception:
            logger.debug("Failed to delete tracked message %s", mid)
    try:
        conn = await get_db()
        await conn.execute(
            'DELETE FROM config WHERE key = ?',
            (f"tracked_{user_id}_{key}",)
        )
        await conn.commit()
    except Exception:
        logger.debug("Failed to clear tracked message key", exc_info=True)


async def _track_rich_response(user_id: int, key: str, response: Any) -> None:
    mid = extract_message_id(response) if response else None
    if mid:
        await _save_tracked_message(user_id, key, mid)


def _md5_stream(path: Path) -> str:
    """Compute MD5 without loading the whole file into memory."""
    h = hashlib.md5()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def _unique_filename(base: str, existing: set[str]) -> str:
    """Return a collision-safe flat filename for a user's file namespace."""
    if base not in existing:
        return base
    stem, ext = os.path.splitext(base)
    suffix = hashlib.md5(f"{base}:{datetime.now().isoformat()}".encode()).hexdigest()[:6]
    candidate = f"{stem}{suffix}{ext}"
    counter = 2
    while candidate in existing:
        candidate = f"{stem}{suffix}{counter}{ext}"
        counter += 1
    return candidate


# FIX_OPT_3.3: single rich send/edit wrapper with HTML fallback.
async def send_rich(
    chat_id: int,
    blocks: list,
    fallback_callable,
    *,
    message_id: Optional[int] = None,
) -> Any:
    """Send/edit a rich card, always falling back to the supplied HTML handler."""
    # FIX_UI_FALLBACK: wrapper-level guarantee; each invocation also supplies a fallback.
    if not RICH_AVAILABLE or rich_client is None:
        try:
            return await fallback_callable()
        except Exception:
            logger.exception("HTML fallback failed")
            return None
    try:
        if message_id is None:
            return await rich_client.send_or(chat_id, blocks, fallback_callable)
        return await rich_client.replace_or(
            chat_id, message_id, blocks, fallback_callable,
        )
    except Exception:
        logger.exception("send_rich failed, trying HTML fallback")
        try:
            return await fallback_callable()
        except Exception:
            logger.exception("HTML fallback also failed")
            return None

# FIX_OPT_2.6: apply the lock guard to every registered handler.
def user_access_guard(func):
    """FIX_OPT_6: enforce ban status first, then maintenance lock."""
    @functools.wraps(func)
    async def wrapper(event, *args, **kwargs):
        user = getattr(event, "from_user", None)
        user_id = getattr(user, "id", None)
        if user_id in banned_users and user_id not in admin_ids:
            if isinstance(event, types.CallbackQuery):
                await event.answer("🚫 You are banned.", show_alert=True)
            else:
                await event.answer("🚫 You are banned from using this bot.")
            return
        if bot_locked and user_id not in admin_ids:
            if isinstance(event, types.CallbackQuery):
                await event.answer("🔒 Bot is locked.", show_alert=True)
            else:
                await event.answer("🔒 Bot is locked for maintenance.")
            return
        return await func(event, *args, **kwargs)
    return wrapper

async def show_confirmation(
    event,
    title: str,
    body: str,
    yes_label: str,
    yes_data: str,
    no_label: str = "❌ Cancel",
    no_data: str = "back_to_main",
):
    """Render a destructive-action confirmation with a guaranteed HTML fallback."""
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text=yes_label, callback_data=yes_data),
            InlineKeyboardButton(text=no_label, callback_data=no_data),
        ],
        [InlineKeyboardButton(text="🏠 Home", callback_data="back_to_main")],
    ])
    html = f"<b>{title}</b>\n\n{body}\n\n⚠️ Please confirm to continue."
    blocks = confirm_card(title, body, yes_label, yes_data, no_label, no_data)
    blocks.extend([
        divider(),
        button_row([rich_callback_button("🏠 Home", "back_to_main", "primary")]),
    ])
    if isinstance(event, types.CallbackQuery):
        # FIX_UI_FALLBACK: HTML fallback for confirmation cards.
        await send_rich(
            event.message.chat.id,
            blocks,
            lambda: event.message.edit_text(html, reply_markup=keyboard, parse_mode="HTML"),
            message_id=event.message.message_id,
        )
    else:
        # FIX_UI_FALLBACK: HTML fallback for confirmation cards sent from commands.
        await send_rich(
            event.chat.id,
            blocks,
            lambda: event.answer(html, reply_markup=keyboard, parse_mode="HTML"),
        )


# ─── ASYNC DATABASE FUNCTIONS ──────────────────────────────────────────────
async def migrate_db():
    # FIX_OPT_2.1: use execute() cursor.fetchall(), not conn.fetchall().
    """FIX_OPT_2: migrate using real cursors on the shared DB connection."""
    logger.info("Running database migrations...")
    try:
        conn = await get_db()
        cursor = await conn.execute("PRAGMA table_info(user_files)")
        columns = [row[1] for row in await cursor.fetchall()]
        if 'upload_date' not in columns:
            logger.info("Adding upload_date column to user_files table...")
            await conn.execute('ALTER TABLE user_files ADD COLUMN upload_date TEXT')

        cursor = await conn.execute("PRAGMA table_info(active_users)")
        columns = [row[1] for row in await cursor.fetchall()]
        if 'join_date' not in columns:
            await conn.execute('ALTER TABLE active_users ADD COLUMN join_date TEXT')
        if 'last_active' not in columns:
            await conn.execute('ALTER TABLE active_users ADD COLUMN last_active TEXT')

        await conn.execute("INSERT OR IGNORE INTO bot_stats (stat_name, stat_value) VALUES ('bot_locked', 0)")
        await conn.execute("""CREATE TABLE IF NOT EXISTS running_scripts
                             (script_key TEXT PRIMARY KEY, pid INTEGER, user_id INTEGER,
                              file_name TEXT, started_at TEXT)""")
        await conn.commit()
        logger.info("Database migrations completed successfully.")
    except Exception as e:
        logger.error(f"Database migration error: {e}", exc_info=True)
        raise


async def init_db():
    logger.info(f"Initializing database at: {DATABASE_PATH}")
    try:
        conn = await get_db()
        await conn.execute("""CREATE TABLE IF NOT EXISTS subscriptions
                             (user_id INTEGER PRIMARY KEY, expiry TEXT)""")
        await conn.execute("""CREATE TABLE IF NOT EXISTS user_files
                             (user_id INTEGER, file_name TEXT, file_type TEXT, upload_date TEXT,
                              PRIMARY KEY (user_id, file_name))""")
        await conn.execute("""CREATE TABLE IF NOT EXISTS active_users
                             (user_id INTEGER PRIMARY KEY, join_date TEXT, last_active TEXT)""")
        await conn.execute("""CREATE TABLE IF NOT EXISTS admins
                             (user_id INTEGER PRIMARY KEY)""")
        await conn.execute("""CREATE TABLE IF NOT EXISTS banned_users
                             (user_id INTEGER PRIMARY KEY, banned_date TEXT, reason TEXT)""")
        await conn.execute("""CREATE TABLE IF NOT EXISTS favorites
                             (user_id INTEGER, file_name TEXT, PRIMARY KEY (user_id, file_name))""")
        await conn.execute("""CREATE TABLE IF NOT EXISTS bot_stats
                             (stat_name TEXT PRIMARY KEY, stat_value INTEGER)""")
        await conn.execute("""CREATE TABLE IF NOT EXISTS running_scripts
                             (script_key TEXT PRIMARY KEY, pid INTEGER, user_id INTEGER,
                              file_name TEXT, started_at TEXT)""")
        # FIX_ISSUE_2: persist tracked Telegram message IDs across bot restarts.
        await conn.execute("""CREATE TABLE IF NOT EXISTS config
                             (key TEXT PRIMARY KEY, value TEXT, updated_at TEXT)""")

        await conn.execute('INSERT OR IGNORE INTO admins (user_id) VALUES (?)', (OWNER_ID,))
        if ADMIN_ID != OWNER_ID:
            await conn.execute('INSERT OR IGNORE INTO admins (user_id) VALUES (?)', (ADMIN_ID,))

        for stat in ['total_uploads', 'total_downloads', 'total_runs', 'bot_locked']:
            await conn.execute('INSERT OR IGNORE INTO bot_stats (stat_name, stat_value) VALUES (?, 0)', (stat,))
        await conn.commit()
        logger.info("Database initialized successfully.")
    except Exception as e:
        logger.error(f"Database initialization error: {e}", exc_info=True)
        raise


async def load_data():
    global bot_locked
    logger.info("Loading data from database...")
    try:
        conn = await get_db()
        cursor = await conn.execute('SELECT user_id, expiry FROM subscriptions')
        for user_id, expiry in await cursor.fetchall():
            try:
                user_subscriptions[user_id] = {'expiry': datetime.fromisoformat(expiry)}
            except ValueError:
                logger.warning(f"Invalid expiry date for user {user_id}")

        cursor = await conn.execute('SELECT user_id, file_name, file_type FROM user_files')
        for user_id, file_name, file_type in await cursor.fetchall():
            user_files.setdefault(user_id, []).append((file_name, file_type))

        cursor = await conn.execute('SELECT user_id FROM active_users')
        active_users.update(user_id for (user_id,) in await cursor.fetchall())

        cursor = await conn.execute('SELECT user_id FROM admins')
        admin_ids.update(user_id for (user_id,) in await cursor.fetchall())

        cursor = await conn.execute('SELECT user_id FROM banned_users')
        banned_users.update(user_id for (user_id,) in await cursor.fetchall())

        cursor = await conn.execute('SELECT user_id, file_name FROM favorites')
        for user_id, file_name in await cursor.fetchall():
            user_favorites.setdefault(user_id, []).append(file_name)

        cursor = await conn.execute('SELECT stat_name, stat_value FROM bot_stats')
        for stat_name, stat_value in await cursor.fetchall():
            bot_stats[stat_name] = stat_value
        bot_locked = bool(bot_stats.get('bot_locked', 0))

        # FIX_OPT_4: kill processes left behind by a previous bot instance.
        cursor = await conn.execute('SELECT script_key, pid, started_at FROM running_scripts')
        stale = await cursor.fetchall()
        cutoff = datetime.now() - timedelta(hours=24)
        for script_key, pid, started_at in stale:
            try:
                started = datetime.fromisoformat(started_at) if started_at else None
            except (TypeError, ValueError):
                started = None
            if started is None or started < cutoff:
                await conn.execute('DELETE FROM running_scripts WHERE script_key = ?', (script_key,))
                continue
            try:
                proc = psutil.Process(int(pid))
                if proc.is_running():
                    for child in proc.children(recursive=True):
                        try:
                            child.terminate()
                        except Exception:
                            pass
                    try:
                        proc.terminate()
                    except Exception:
                        pass
            except (psutil.NoSuchProcess, psutil.AccessDenied, ValueError):
                pass
            await conn.execute('DELETE FROM running_scripts WHERE script_key = ?', (script_key,))
        await conn.commit()

        logger.info(f"Data loaded: {len(active_users)} users, {len(banned_users)} banned, {len(admin_ids)} admins, locked={bot_locked}.")
    except Exception as e:
        logger.error(f"Error loading data: {e}", exc_info=True)
        raise


def get_user_file_limit(user_id):
    if user_id == OWNER_ID: return OWNER_LIMIT
    if user_id in admin_ids: return ADMIN_LIMIT
    if user_id in user_subscriptions and user_subscriptions[user_id]['expiry'] > datetime.now():
        return SUBSCRIBED_USER_LIMIT
    return FREE_USER_LIMIT

def get_main_keyboard(user_id):
    if user_id in admin_ids:
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📢 Updates", url=UPDATE_CHANNEL)],
            [InlineKeyboardButton(text="📤 Upload File", callback_data="upload_file"),
             InlineKeyboardButton(text="📁 My Files", callback_data="check_files")],
            [InlineKeyboardButton(text="⭐ Favorites", callback_data="my_favorites"),
             InlineKeyboardButton(text="🔍 Search Files", callback_data="search_files")],
            [InlineKeyboardButton(text="⚡ Bot Speed", callback_data="bot_speed"),
             InlineKeyboardButton(text="📊 My Stats", callback_data="statistics")],
            [InlineKeyboardButton(text="ℹ️ Help & Info", callback_data="help_info"),
             InlineKeyboardButton(text="🎯 Features", callback_data="all_features")],
            [InlineKeyboardButton(text="👨‍💼 Admin Panel", callback_data="admin_panel"),
             InlineKeyboardButton(text="💬 Contact", url=f"https://t.me/{YOUR_USERNAME.replace('@', '')}")]
        ])
    else:
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📢 Updates Channel", url=UPDATE_CHANNEL)],
            [InlineKeyboardButton(text="📤 Upload File", callback_data="upload_file"),
             InlineKeyboardButton(text="📁 My Files", callback_data="check_files")],
            [InlineKeyboardButton(text="⭐ Favorites", callback_data="my_favorites"),
             InlineKeyboardButton(text="🔍 Search Files", callback_data="search_files")],
            [InlineKeyboardButton(text="⚡ Bot Speed", callback_data="bot_speed"),
             InlineKeyboardButton(text="📊 My Stats", callback_data="statistics")],
            [InlineKeyboardButton(text="💎 Get Premium", callback_data="get_premium"),
             InlineKeyboardButton(text="ℹ️ Help", callback_data="help_info")],
            [InlineKeyboardButton(text="🎯 Features", callback_data="all_features"),
             InlineKeyboardButton(text="💬 Contact Owner", url=f"https://t.me/{YOUR_USERNAME.replace('@', '')}")]
        ])
    return keyboard

def get_admin_panel_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="👥 User Stats", callback_data="admin_total_users"),
         InlineKeyboardButton(text="📁 Files Stats", callback_data="admin_total_files")],
        [InlineKeyboardButton(text="🚀 Running Scripts", callback_data="admin_running_scripts"),
         InlineKeyboardButton(text="💎 Premium Users", callback_data="admin_premium_users")],
        [InlineKeyboardButton(text="➕ Add Admin", callback_data="admin_add_admin"),
         InlineKeyboardButton(text="➖ Remove Admin", callback_data="admin_remove_admin")],
        [InlineKeyboardButton(text="🚫 Ban User", callback_data="admin_ban_user"),
         InlineKeyboardButton(text="✅ Unban User", callback_data="admin_unban_user")],
        [InlineKeyboardButton(text="📊 Bot Analytics", callback_data="admin_analytics"),
         InlineKeyboardButton(text="⚙️ System Info", callback_data="admin_system_status")],
        [InlineKeyboardButton(text="🔒 Lock/Unlock", callback_data="lock_bot"),
         InlineKeyboardButton(text="📢 Broadcast", callback_data="broadcast")],
        [InlineKeyboardButton(text="🗑️ Clean Files", callback_data="admin_clean_files"),
         InlineKeyboardButton(text="💾 Backup DB", callback_data="admin_backup_db")],
        [InlineKeyboardButton(text="📝 View Logs", callback_data="admin_view_logs"),
         InlineKeyboardButton(text="🔄 Restart Bot", callback_data="admin_restart_bot")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    return keyboard

# FIX_OPT_3.4: rich UI — start handler.
@dp.message(Command("start"))
@user_access_guard
async def cmd_start(message: types.Message):
    user_id = message.from_user.id
    # FIX_ISSUE_2: delete stale cards before sending a fresh /start card.
    for key in ("start_card", "menu_card", "upload_card",
                "files_card", "help_card", "stats_card"):
        await _delete_tracked_message(bot, message.chat.id, user_id, key)
    active_users.add(user_id)

    try:
        conn = await get_db()
        now = datetime.now().isoformat()
        await conn.execute(
            'INSERT OR REPLACE INTO active_users (user_id, join_date, last_active) VALUES (?, ?, ?)',
            (user_id, now, now)
        )
        await conn.commit()
    except Exception as e:
        logger.error(f"Error saving active user: {e}")

    keyboard = get_main_keyboard(user_id)
    account = "Premium ✨" if user_id in user_subscriptions else "Free 🆓"
    limit = get_user_file_limit(user_id)
    welcome_text = f"""
🌟 <b>Welcome to File Host Bot</b>

👋 Hi, {message.from_user.full_name}!

📊 <b>Account</b>
• ID: <code>{user_id}</code>
• Plan: {account}
• File usage: {len(user_files.get(user_id, []))}/{_format_limit(limit)}

<b>What you can do</b>
• Upload .py, .js and .zip files
• Run scripts and manage logs
• Search, favorite and inspect files
• View statistics and bot speed

✨ Choose an option below to get started.
"""
    promo_url = UPDATE_CHANNEL
    blocks = [
        heading("🌟 Welcome to File Host Bot"),
        divider(),
        compact_table(
            ["Account", "Value"],
            [["Plan", account],
             ["Files", f"{len(user_files.get(user_id, []))}/{_format_limit(limit)}"],
             ["User ID", str(user_id)]],
        ),
        bullet_list([
            "📤 Upload and manage .py, .js and .zip files.",
            "▶️ Run scripts and monitor their logs.",
            "🔍 Search and ⭐ favorite files.",
            "📊 View statistics and ⚡ test bot speed.",
        ]),
        quote("Tip: start with Upload File or My Files."),
        divider(),
        button_row([
            rich_callback_button("📤 Upload", "upload_file", "success"),
            rich_callback_button("📁 My Files", "check_files", "primary"),
        ]),
        button_row([
            rich_callback_button("📊 My Stats", "statistics", "primary"),
            rich_callback_button("ℹ️ Help", "help_info", "primary"),
        ]),
        button_row([
            rich_url_button("🎬 Updates / Promo", promo_url, "primary"),
        ]),
    ]
    # FIX_UI_FALLBACK: HTML fallback for the Welcome rich card.
    response = await send_rich(
        message.chat.id, blocks,
        lambda: message.answer(welcome_text, reply_markup=keyboard, parse_mode="HTML"),
    )
    await _track_rich_response(user_id, "start_card", response)

@dp.callback_query(F.data == "back_to_main")
@user_access_guard
async def callback_back_to_main(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    keyboard = get_main_keyboard(user_id)
    html = f"""
🏠 <b>Main Menu</b>

👤 <b>User:</b> {callback.from_user.full_name}
📁 <b>Files:</b> {len(user_files.get(user_id, []))}/{_format_limit(get_user_file_limit(user_id))}

Choose an option below to continue.
"""
    blocks = [
        heading("🏠 Main Menu"), divider(),
        paragraph(
            f"Welcome back, {callback.from_user.full_name}. "
            "Choose an option below to continue."
        ),
        compact_table(
            ["Metric", "Value"],
            [["Files", f"{len(user_files.get(user_id, []))}/{_format_limit(get_user_file_limit(user_id))}"],
             ["Plan", "Premium ✨" if user_id in user_subscriptions else "Free 🆓"]],
        ),
        divider(),
        button_row([
            rich_callback_button("📤 Upload", "upload_file", "success"),
            rich_callback_button("📁 My Files", "check_files", "primary"),
        ]),
        button_row([
            rich_callback_button("⭐ Favorites", "my_favorites", "primary"),
            rich_callback_button("🔍 Search", "search_files", "primary"),
        ]),
        button_row([
            rich_callback_button("📊 Stats", "statistics", "primary"),
            rich_callback_button("ℹ️ Help", "help_info", "primary"),
        ]),
    ]
    # FIX_UI_FALLBACK: HTML fallback for the Main Menu rich card.
    response = await send_rich(
        callback.message.chat.id, blocks,
        lambda: callback.message.edit_text(html, reply_markup=keyboard, parse_mode="HTML"),
        message_id=callback.message.message_id,
    )
    await _track_rich_response(callback.from_user.id, "menu_card", response)
    await callback.answer()

@dp.callback_query(F.data == "upload_file")
@user_access_guard
async def callback_upload_file(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    current_files = len(user_files.get(user_id, []))
    limit = get_user_file_limit(user_id)
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    html = f"""
📤 <b>Upload Files</b>

📊 <b>Current Usage:</b> {current_files}/{_format_limit(limit)}
📁 <b>Supported:</b> Python (.py), JavaScript (.js), ZIP (.zip)

<b>Quick guide</b>
1️⃣ Tap Upload File and send your document.
2️⃣ Wait for the upload confirmation.
3️⃣ For ZIPs, choose Extract ZIP after upload.

💡 Maximum upload size: {MAX_UPLOAD_BYTES // (1024 * 1024)} MB.
"""
    blocks = [
        heading("📤 Upload Files"),
        divider(),
        compact_table(
            ["Metric", "Value"],
            [["Current Usage", f"{current_files}/{_format_limit(limit)}"],
             ["Supported Formats", ".py • .js • .zip"],
             ["Max Upload", f"{MAX_UPLOAD_BYTES // (1024 * 1024)} MB"]],
        ),
        bullet_list([
            "1️⃣ Send your .py, .js, or .zip file.",
            "2️⃣ Wait for the upload confirmation.",
            "3️⃣ Extract ZIPs only after the upload succeeds.",
        ]),
        divider(),
        button_row([rich_callback_button("🏠 Main Menu", "back_to_main", "primary")]),
    ]
    # FIX_UI_FALLBACK: HTML fallback for the Upload Files rich card.
    response = await send_rich(
        callback.message.chat.id, blocks,
        lambda: callback.message.edit_text(html, reply_markup=keyboard, parse_mode="HTML"),
        message_id=callback.message.message_id,
    )
    await _track_rich_response(callback.from_user.id, "upload_card", response)
    await callback.answer()

@dp.callback_query(F.data == "check_files")
@user_access_guard
async def callback_check_files(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    files = user_files.get(user_id, [])
    keyboard_rows = []
    blocks = [heading(f"📁 My Files ({len(files)})" if files else "📁 My Files"), divider()]

    if not files:
        # FIX_BUG_5: keep the empty-state branch free of a duplicate footer; footer is added once below.
        html = """
📁 <b>My Files</b>

📭 No files found yet.
Upload your first file to get started! 🚀
"""
        keyboard_rows = [
            [InlineKeyboardButton(text="📤 Upload File", callback_data="upload_file")],
        ]
        blocks.append(paragraph("📭 No files found yet. Upload your first file to get started! 🚀"))
    else:
        html = f"📁 <b>My Files ({len(files)})</b>\n\n"
        # FIX_BUG_7: cap rich rendering so large file lists stay within rich block limits.
        MAX_FILES_PER_RICH = 10
        display_files = files[:MAX_FILES_PER_RICH]
        remaining = max(0, len(files) - MAX_FILES_PER_RICH)
        grouped = {
            "🐍 Python": [item for item in display_files if item[1] == "py"],
            "🟨 JavaScript": [item for item in display_files if item[1] == "js"],
            "📦 ZIP": [item for item in display_files if item[1] == "zip"],
        }
        for group, group_files in grouped.items():
            if not group_files:
                continue
            # FIX_BUG_8: use the default heading size; size=3 is unverified.
            blocks.append(heading(group))
            blocks.append(bullet_list([name for name, _ in group_files[:20]]))
            if len(group_files) > 20:
                blocks.append(paragraph(f"… and {len(group_files) - 20} more"))

        for i, (file_name, file_type) in enumerate(display_files, 1):
            icon = "🐍" if file_type == "py" else "🟨" if file_type == "js" else "📦"
            html += f"{i}. {icon} <code>{file_name}</code>\n"
            is_favorite = file_name in user_favorites.get(user_id, [])
            star = "⭐" if is_favorite else "☆"
            log_file = UPLOAD_BOTS_DIR / str(user_id) / f"{Path(file_name).stem}.log"
            rich_row = [
                rich_callback_button(f"▶️ {file_name[:15]}", f"run_script:{file_name}", "success"),
                rich_callback_button(star, f"toggle_fav:{file_name}", "primary"),
            ]
            blocks.append(button_row(rich_row))
            keyboard_rows.append([
                InlineKeyboardButton(text=f"▶️ {file_name[:15]}", callback_data=f"run_script:{file_name}"),
                InlineKeyboardButton(text=star, callback_data=f"toggle_fav:{file_name}"),
            ])
            info_delete = [
                rich_callback_button(f"ℹ️ Info", f"file_info:{file_name}", "primary"),
                rich_callback_button("🗑️ Delete", f"delete_file:{file_name}", "danger"),
            ]
            blocks.append(button_row(info_delete))
            keyboard_rows.append([
                InlineKeyboardButton(text=f"ℹ️ Info {file_name[:15]}", callback_data=f"file_info:{file_name}"),
                InlineKeyboardButton(text="🗑️ Delete", callback_data=f"delete_file:{file_name}"),
            ])
            if log_file.exists():
                blocks.append(button_row([
                    rich_callback_button("📄 Logs", f"view_logs:{file_name}", "primary"),
                ]))
                keyboard_rows.append([
                    InlineKeyboardButton(text="📄 Logs", callback_data=f"view_logs:{file_name}")
                ])

        if remaining > 0:
            # FIX_BUG_7: tell the user that rich rendering is intentionally capped.
            blocks.append(paragraph(
                f"… and {remaining} more file(s). Use /search <name> to find specific files."
            ))

        blocks.extend([
            divider(),
            quote("Tap Run to execute, ☆/⭐ to manage favorites, or Info for file details."),
        ])
        html += "\n📊 Use File Stats for a quick overview."

    keyboard_rows.append([
        InlineKeyboardButton(text="📊 File Stats", callback_data="statistics"),
        InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main"),
    ])
    keyboard = InlineKeyboardMarkup(inline_keyboard=keyboard_rows)
    blocks.extend([
        divider(),
        button_row([
            rich_callback_button("📊 File Stats", "statistics", "primary"),
            rich_callback_button("🏠 Main Menu", "back_to_main", "primary"),
        ]),
    ])
    # FIX_UI_FALLBACK: HTML fallback for the My Files rich card.
    response = await send_rich(
        callback.message.chat.id, blocks,
        lambda: callback.message.edit_text(html, reply_markup=keyboard, parse_mode="HTML"),
        message_id=callback.message.message_id,
    )
    await _track_rich_response(callback.from_user.id, "files_card", response)
    await callback.answer()
@dp.callback_query(F.data == "my_favorites")
@user_access_guard
async def callback_my_favorites(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    favorites = user_favorites.get(user_id, [])
    buttons = []
    if favorites:
        for file_name in favorites:
            log_file = UPLOAD_BOTS_DIR / str(user_id) / f"{Path(file_name).stem}.log"
            buttons.append([
                InlineKeyboardButton(text=f"▶️ {file_name[:18]}", callback_data=f"run_script:{file_name}"),
                InlineKeyboardButton(text="❌", callback_data=f"toggle_fav:{file_name}"),
            ])
            if log_file.exists():
                buttons.append([
                    InlineKeyboardButton(text="📄 Logs", callback_data=f"view_logs:{file_name}"),
                    InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
                ])
        html = (
            f"⭐ <b>Favorites ({len(favorites)})</b>\n\n" +
            "\n".join(f"• ⭐ <code>{name}</code>" for name in favorites) +
            "\n\nTap Run to execute a file or ❌ to remove it from favorites."
        )
    else:
        html = "⭐ <b>Favorites</b>\n\n💭 No favorite files yet!\n\nAdd files to favorites for quick access. 🚀"
    buttons.append([
        InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
        InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main"),
    ])
    keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    blocks = [
        heading(f"⭐ Favorites{' (' + str(len(favorites)) + ')' if favorites else ''}"),
        divider(),
        paragraph("Quick access to your saved files." if favorites else "You have no favorite files yet."),
    ]
    if favorites:
        blocks.append(bullet_list([f"⭐ {name}" for name in favorites[:12]]))
        if len(favorites) > 12:
            blocks.append(paragraph(f"… and {len(favorites) - 12} more"))
        for file_name in favorites:
            blocks.append(button_row([
                rich_callback_button(f"▶️ {file_name[:18]}", f"run_script:{file_name}", "success"),
                rich_callback_button("❌", f"toggle_fav:{file_name}", "danger"),
            ]))
            log_file = UPLOAD_BOTS_DIR / str(user_id) / f"{Path(file_name).stem}.log"
            if log_file.exists():
                blocks.append(button_row([
                    rich_callback_button("📄 Logs", f"view_logs:{file_name}", "primary"),
                    rich_callback_button("📁 My Files", "check_files", "primary"),
                ]))
    else:
        blocks.append(quote("Tip: open My Files and tap ☆ to save a file here."))
    blocks.extend([
        divider(),
        button_row([
            rich_callback_button("📁 My Files", "check_files", "primary"),
            rich_callback_button("🏠 Main Menu", "back_to_main", "primary"),
        ]),
    ])
    # FIX_UI_FALLBACK: HTML fallback for the Favorites rich card.
    await send_rich(
        callback.message.chat.id, blocks,
        lambda: callback.message.edit_text(html, reply_markup=keyboard, parse_mode="HTML"),
        message_id=callback.message.message_id,
    )
    await callback.answer()
@dp.callback_query(F.data == "search_files")
@user_access_guard
async def callback_search_files(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    files = user_files.get(user_id, [])
    py_count = sum(1 for f in files if f[1] == "py")
    js_count = sum(1 for f in files if f[1] == "js")
    zip_count = sum(1 for f in files if f[1] == "zip")
    html = f"""
🔍 <b>Search Files</b>

📊 <b>Total:</b> {len(files)}
🐍 Python: {py_count}
🟨 JavaScript: {js_count}
📦 ZIP: {zip_count}

💡 Use <code>/search filename</code> to find matching files.
"""
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📁 View All Files", callback_data="check_files"),
         InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    blocks = [
        heading("🔍 Search Files"), divider(),
        compact_table(["File Type", "Count"],
                      [["All", str(len(files))], ["Python", str(py_count)],
                       ["JavaScript", str(js_count)], ["ZIP", str(zip_count)]]),
        quote("Tip: use /search filename to search your saved files."),
        divider(),
        button_row([
            rich_callback_button("📁 View All Files", "check_files", "primary"),
            rich_callback_button("🏠 Main Menu", "back_to_main", "primary"),
        ]),
    ]
    # FIX_UI_FALLBACK: HTML fallback for the Search Files rich card.
    await send_rich(
        callback.message.chat.id, blocks,
        lambda: callback.message.edit_text(html, reply_markup=keyboard, parse_mode="HTML"),
        message_id=callback.message.message_id,
    )
    await callback.answer()

@dp.callback_query(F.data == "bot_speed")
@user_access_guard
async def callback_bot_speed(callback: types.CallbackQuery):
    start_time = datetime.now()
    await callback.answer("⚡ Testing...")
    end_time = datetime.now()
    speed = (end_time - start_time).total_seconds() * 1000
    if speed < 100:
        status = "🟢 Excellent"
    elif speed < 300:
        status = "🟡 Good"
    else:
        status = "🔴 Slow"
    cpu = psutil.cpu_percent()
    memory = psutil.virtual_memory().percent
    html = f"""
⚡ <b>Speed Test</b>

📡 <b>Response:</b> {speed:.2f} ms
📊 <b>Status:</b> {status}
🖥️ <b>CPU:</b> {cpu}%
🧠 <b>Memory:</b> {memory}%
🤖 <b>Uptime:</b> Online
"""
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Test Again", callback_data="bot_speed"),
         InlineKeyboardButton(text="🏠 Home", callback_data="back_to_main")]
    ])
    blocks = [
        heading("⚡ Speed Test"), divider(),
    ]
    blocks.extend(stats_card("⚡ Live Metrics", [
        ["Response Time", f"{speed:.2f} ms"],
        ["Status", status],
        ["CPU", f"{cpu}%"],
        ["Memory", f"{memory}%"],
        ["Uptime", "Online"],
    ]))
    blocks.extend([
        divider(),
        button_row([
            rich_callback_button("🔄 Retest", "bot_speed", "success"),
            rich_callback_button("🏠 Home", "back_to_main", "primary"),
        ]),
    ])
    # FIX_UI_FALLBACK: HTML fallback for the Speed Test rich card.
    await send_rich(
        callback.message.chat.id, blocks,
        lambda: callback.message.edit_text(html, reply_markup=keyboard, parse_mode="HTML"),
        message_id=callback.message.message_id,
    )

@dp.callback_query(F.data == "statistics")
@user_access_guard
async def callback_statistics(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    user_file_count = len(user_files.get(user_id, []))
    user_fav_count = len(user_favorites.get(user_id, []))
    limit = get_user_file_limit(user_id)
    is_premium = user_id in user_subscriptions and user_subscriptions[user_id]['expiry'] > datetime.now()
    running = sum(1 for k in bot_scripts if k.startswith(f"{user_id}_"))
    global_rows = [
        ["Uploads", str(bot_stats.get("total_uploads", 0))],
        ["Downloads", str(bot_stats.get("total_downloads", 0))],
        ["Script Runs", str(bot_stats.get("total_runs", 0))],
    ]
    html = f"""
📊 <b>Your Statistics</b>

📁 Files: {user_file_count}/{_format_limit(limit)}
⭐ Favorites: {user_fav_count}
💎 Account: {'Premium ✨' if is_premium else 'Free 🆓'}
🚀 Running: {running}

📈 <b>Global</b>
📤 Uploads: {bot_stats.get('total_uploads', 0)}
📥 Downloads: {bot_stats.get('total_downloads', 0)}
▶️ Script Runs: {bot_stats.get('total_runs', 0)}
"""
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Back", callback_data="back_to_main"),
         InlineKeyboardButton(text="🏠 Home", callback_data="back_to_main")]
    ])
    blocks = [heading("📊 Your Statistics"), divider()]
    blocks.extend(stats_card("📊 Your Activity", [
        ["Files", f"{user_file_count}/{_format_limit(limit)}"],
        ["Favorites", str(user_fav_count)],
        ["Account", "Premium ✨" if is_premium else "Free 🆓"],
        ["Running", str(running)],
    ]))
    blocks.extend([divider()])
    blocks.extend(stats_card("🌍 Global", global_rows))
    blocks.extend([
        divider(),
        button_row([
            rich_callback_button("🔙 Back", "back_to_main", "primary"),
            rich_callback_button("🏠 Home", "back_to_main", "primary"),
        ]),
    ])
    # FIX_UI_FALLBACK: HTML fallback for the Statistics rich card.
    response = await send_rich(
        callback.message.chat.id, blocks,
        lambda: callback.message.edit_text(html, reply_markup=keyboard, parse_mode="HTML"),
        message_id=callback.message.message_id,
    )
    await _track_rich_response(callback.from_user.id, "stats_card", response)
    await callback.answer()

@dp.callback_query(F.data == "help_info")
@user_access_guard
async def callback_help_info(callback: types.CallbackQuery):
    html = """
ℹ️ <b>Help & Info</b>

<b>How to use</b>
1️⃣ Upload .py, .js or .zip files.
2️⃣ Open My Files and run/manage them.
3️⃣ Use /search filename to find files.
4️⃣ Open Logs to inspect script output.
5️⃣ Use /stats for usage statistics.

<b>Commands</b>
/start /help /search /stats /premium

Need help? Contact the owner. 💬
"""
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎯 Features", callback_data="all_features"),
         InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    blocks = [
        heading("ℹ️ Help & Info"), divider(),
        paragraph("Everything you need to upload, run and manage your files."),
        bullet_list([
            "📤 Upload .py, .js or .zip files.",
            "▶️ Run scripts from My Files and monitor logs.",
            "⭐ Manage favorites and 🔍 search with /search.",
            "📊 Use /stats for your statistics.",
            "💬 Contact the owner if you need assistance.",
        ]),
        quote("Tip: /search filename finds matching files quickly."),
        divider(),
        button_row([
            rich_callback_button("🎯 Features", "all_features", "primary"),
            rich_callback_button("🏠 Main Menu", "back_to_main", "primary"),
        ]),
    ]
    # FIX_UI_FALLBACK: HTML fallback for the Help & Info rich card.
    response = await send_rich(
        callback.message.chat.id, blocks,
        lambda: callback.message.edit_text(html, reply_markup=keyboard, parse_mode="HTML"),
        message_id=callback.message.message_id,
    )
    await _track_rich_response(callback.from_user.id, "help_card", response)
    await callback.answer()

@dp.callback_query(F.data == "all_features")
@user_access_guard
async def callback_all_features(callback: types.CallbackQuery):
    features = [
        "📤 Upload Python, JavaScript and ZIP files",
        "📁 View and manage your files",
        "⭐ Save favorite files",
        "🔍 Search files by name",
        "▶️ Run Python and JavaScript scripts",
        "🛑 Stop running scripts",
        "📊 View usage statistics",
        "⚡ Check bot response speed",
        "📥 Download your files",
        "💾 Inspect file information",
        "📄 View script logs",
        "📋 Copy logs as a file",
        "ℹ️ Help and support",
        "🎯 Feature discovery",
        "💎 Premium access",
    ]
    html = """
🎯 <b>All Features</b>

✨ <b>15+ features:</b>
""" + "\n".join(f"• {x}" for x in features) + """

💎 <b>Premium:</b> higher file limit, priority processing, analytics and support.
"""
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💎 Get Premium", callback_data="get_premium"),
         InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    blocks = [
        heading("🎯 All Features"), divider(),
        bullet_list(features[:8] + ["… and more features available."]),
        quote("Explore My Files, Search, Statistics and Premium from the main menu."),
        divider(),
        button_row([
            rich_callback_button("💎 Premium", "get_premium", "success"),
            rich_callback_button("🏠 Home", "back_to_main", "primary"),
        ]),
    ]
    # FIX_UI_FALLBACK: HTML fallback for the All Features rich card.
    await send_rich(
        callback.message.chat.id, blocks,
        lambda: callback.message.edit_text(html, reply_markup=keyboard, parse_mode="HTML"),
        message_id=callback.message.message_id,
    )
    await callback.answer()

@dp.callback_query(F.data == "get_premium")
@user_access_guard
async def callback_get_premium(callback: types.CallbackQuery):
    html = f"""
💎 <b>Premium Plan</b>

<b>Pricing</b>
• 1 Month: $5
• 3 Months: $12 (Save 20%)
• 1 Year: $40 (Save 33%)

<b>Benefits</b>
• 20 file upload limit
• Priority processing
• Faster response time
• Advanced analytics
• Priority support
• Premium badge

Contact owner to upgrade.
"""
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💬 Contact Owner", url=f"https://t.me/{YOUR_USERNAME.replace('@', '')}")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    blocks = [
        heading("💎 Premium Plan"), divider(),
        compact_table("Plan Price Benefits".split(), [
            ["1 Month", "$5", "Premium"],
            ["3 Months", "$12", "Save 20%"],
            ["1 Year", "$40", "Save 33%"],
        ]),
        bullet_list([
            "📦 20-file premium limit",
            "⚡ Priority processing",
            "🚀 Faster response time",
            "📊 Advanced analytics",
            "💬 Priority support",
            "⭐ Premium badge",
        ]),
        divider(),
        button_row([
            rich_url_button("💬 Contact Owner", f"https://t.me/{YOUR_USERNAME.replace('@', '')}", "success"),
            rich_callback_button("🏠 Main Menu", "back_to_main", "primary"),
        ]),
    ]
    # FIX_UI_FALLBACK: HTML fallback for the Premium Plan rich card.
    await send_rich(
        callback.message.chat.id, blocks,
        lambda: callback.message.edit_text(html, reply_markup=keyboard, parse_mode="HTML"),
        message_id=callback.message.message_id,
    )
    await callback.answer()

@dp.callback_query(F.data == "admin_panel")
@user_access_guard
async def callback_admin_panel(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    total_files = sum(len(files) for files in user_files.values())
    html = """
👑 <b>Admin Panel</b>

Manage users, files, scripts and system settings.
Select an option below to continue.
"""
    keyboard = get_admin_panel_keyboard()
    blocks = [
        heading("👑 Admin Panel"), divider(),
        compact_table(
            ["Metric", "Value"],
            [["Users", str(len(active_users))],
             ["Files", str(total_files)],
             ["Scripts", str(len(bot_scripts))],
             ["Locked", "Yes 🔒" if bot_locked else "No 🔓"]],
        ),
        paragraph("Control center for moderation, system tools and bot operations."),
        divider(),
    ]
    for row in keyboard.inline_keyboard:
        rich_buttons = []
        for button in row:
            if button.callback_data:
                style = "danger" if any(word in (button.text or "").lower() for word in ("ban", "remove", "clean", "lock", "delete", "restart")) else "primary"
                rich_buttons.append(rich_callback_button(button.text, button.callback_data, style))
            elif button.url:
                rich_buttons.append(rich_url_button(button.text, button.url, "primary"))
        if rich_buttons:
            # Rich UI never puts more than two buttons in a row.
            for i in range(0, len(rich_buttons), 2):
                blocks.append(button_row(rich_buttons[i:i+2]))
    # FIX_UI_FALLBACK: HTML fallback for the Admin Panel rich card.
    await send_rich(
        callback.message.chat.id, blocks,
        lambda: callback.message.edit_text(html, reply_markup=keyboard, parse_mode="HTML"),
        message_id=callback.message.message_id,
    )
    await callback.answer()

@dp.callback_query(F.data.startswith("toggle_fav:"))
@user_access_guard
async def callback_toggle_favorite(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    try:
        file_name = _safe_filename(callback.data.split(":", 1)[1])
    except ValueError:
        await callback.answer("❌ Invalid filename!", show_alert=True)
        return
    
    if user_id not in user_favorites:
        user_favorites[user_id] = []
    
    try:
        conn = await get_db()
        if file_name in user_favorites[user_id]:
            user_favorites[user_id].remove(file_name)
            await conn.execute('DELETE FROM favorites WHERE user_id = ? AND file_name = ?', (user_id, file_name))
            await callback.answer("❌ Removed from favorites!", show_alert=True)
        else:
            user_favorites[user_id].append(file_name)
            await conn.execute('INSERT OR IGNORE INTO favorites (user_id, file_name) VALUES (?, ?)', (user_id, file_name))
        await conn.commit()
            
        await callback_check_files(callback)
        
    except Exception as e:
        logger.error(f"Error toggling favorite: {e}")
        await callback.answer(f"❌ Error: {str(e)}", show_alert=True)

@dp.callback_query(F.data.startswith("file_info:"))
@user_access_guard
async def callback_file_info(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    try:
        file_name = _safe_filename(callback.data.split(":", 1)[1])
    except ValueError:
        await callback.answer("❌ Invalid filename!", show_alert=True)
        return
    
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    file_path = user_folder / file_name
    
    if not file_path.exists():
        await callback.answer("❌ File not found!", show_alert=True)
        return
    
    file_size = file_path.stat().st_size
    file_size_mb = file_size / (1024 * 1024)
    file_ext = file_path.suffix
    modified_time = datetime.fromtimestamp(file_path.stat().st_mtime)
    
    is_favorite = file_name in user_favorites.get(user_id, [])
    
    text = f"""
╔═══════════════════════╗
    ℹ️ <b>FILE INFO</b> ℹ️
╚═══════════════════════╝

📄 <b>Name:</b> <code>{file_name}</code>

📦 <b>Type:</b> {file_ext.upper()} File
💾 <b>Size:</b> {file_size_mb:.2f} MB ({file_size} bytes)
📅 <b>Modified:</b> {modified_time.strftime('%Y-%m-%d %H:%M')}
⭐ <b>Favorite:</b> {'Yes ✨' if is_favorite else 'No'}

🔐 <b>MD5:</b> <code>{_md5_stream(file_path)[:16]}...</code>
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="▶️ Run", callback_data=f"run_script:{file_name}"),
         InlineKeyboardButton(text="🗑️ Delete", callback_data=f"delete_file:{file_name}")],
        [InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
         InlineKeyboardButton(text="🏠 Home", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data.startswith("view_logs:"))
@user_access_guard
async def callback_view_logs(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    try:
        file_name = _safe_filename(callback.data.split(":", 1)[1])
    except ValueError:
        await callback.answer("❌ Invalid filename!", show_alert=True)
        return
    
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    log_file = user_folder / f"{Path(file_name).stem}.log"
    
    if not log_file.exists():
        await callback.answer("❌ No logs found for this script.", show_alert=True)
        return
    
    try:
        with open(log_file, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()
        
        if len(lines) > 200:
            lines = lines[-200:]
            log_text = "".join(lines)
            truncated = True
        else:
            log_text = "".join(lines)
            truncated = False
        
        if not log_text.strip():
            log_text = "(Log file is empty)"
        
        safe_text = log_text.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
        safe_text = safe_text.replace('"', '&quot;').replace("'", '&#39;')
        
        header = f"📄 <b>Logs for:</b> <code>{file_name}</code>\n"
        if truncated:
            header += "⚠️ <i>Showing last 200 lines</i>\n"
        header += "━━━━━━━━━━━━━━━━━━━━━━\n"
        
        max_len = 3900
        full_msg = header + safe_text
        if len(full_msg) > max_len:
            parts = [full_msg[i:i+max_len] for i in range(0, len(full_msg), max_len)]
            for idx, part in enumerate(parts):
                if idx == 0:
                    await callback.message.reply(part, parse_mode="HTML")
                else:
                    await callback.message.reply(f"<pre>{part}</pre>", parse_mode="HTML")
        else:
            await callback.message.reply(full_msg, parse_mode="HTML")
        
        copy_kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📋 Copy Logs (as file)", callback_data=f"copy_logs:{file_name}")],
            [InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
             InlineKeyboardButton(text="🏠 Home", callback_data="back_to_main")]
        ])
        await callback.message.reply(
            "📋 Click below to copy the full log file.",
            reply_markup=copy_kb,
            parse_mode="HTML"
        )
        await callback.answer()
        
    except Exception as e:
        logger.error(f"Error viewing logs: {e}")
        await callback.answer(f"❌ Error: {str(e)}", show_alert=True)

@dp.callback_query(F.data.startswith("copy_logs:"))
@user_access_guard
async def callback_copy_logs(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    try:
        file_name = _safe_filename(callback.data.split(":", 1)[1])
    except ValueError:
        await callback.answer("❌ Invalid filename!", show_alert=True)
        return
    
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    log_file = user_folder / f"{Path(file_name).stem}.log"
    
    if not log_file.exists():
        await callback.answer("❌ Log file not found.", show_alert=True)
        return
    
    try:
        with open(log_file, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        
        if not content.strip():
            content = "(Empty log)"
        
        buffer = content.encode('utf-8')
        input_file = types.BufferedInputFile(buffer, filename=f"{Path(file_name).stem}_log.txt")
        
        await callback.answer("📤 Sending log file...", show_alert=False)
        await callback.message.reply_document(
            document=input_file,
            caption=f"📄 <b>Log file:</b> <code>{file_name}.log</code>\n"
                    f"👤 User: <code>{user_id}</code>",
            parse_mode="HTML"
        )
        await callback.answer("✅ Log sent!")
        
    except Exception as e:
        logger.error(f"Error copying logs: {e}")
        await callback.answer(f"❌ Error: {str(e)}", show_alert=True)

@dp.message(F.document)
@user_access_guard
async def handle_document(message: types.Message):
    user_id = message.from_user.id
    
    if user_id in banned_users:
        await message.answer("🚫 You are banned from using this bot!")
        return
    
    if bot_locked and user_id not in admin_ids:
        await message.answer("🔒 Bot is currently locked!")
        return
    
    document = message.document
    try:
        file_name = _safe_filename(document.file_name)
    except ValueError:
        await message.answer("❌ Unsafe filename rejected.")
        return
    file_ext = os.path.splitext(file_name)[1].lower()

    if file_ext not in ['.py', '.js', '.zip']:
        await message.answer("❌ Only .py, .js, and .zip files are supported!")
        return

    # FIX_OPT_1.3: reject oversized uploads before Telegram download.
    if document.file_size is not None and document.file_size > MAX_UPLOAD_BYTES:
        await message.answer(
            f"❌ File is too large! Maximum upload size is {MAX_UPLOAD_BYTES // (1024 * 1024)} MB."
        )
        return

    # FIX_OPT_4.3: simple per-user upload rate limit.
    if not _upload_allowed(user_id):
        await message.answer("⏳ Upload rate limit reached. Please wait a minute and try again.")
        return

    current_files = len(user_files.get(user_id, []))
    limit = get_user_file_limit(user_id)
    
    if current_files >= limit:
        await message.answer(f"❌ Upload limit reached! ({current_files}/{_format_limit(limit)})\n\n💎 Upgrade to premium for more space!")
        return
    
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    user_folder.mkdir(exist_ok=True)
    
    file_path = user_folder / file_name
    
    try:
        file_size_kb = (document.file_size or 0) / 1024
        
        status_msg = await message.answer(
            f"📤 <b>Preparing upload...</b>\n\n"
            f"📄 File: <code>{file_name}</code>\n"
            f"💾 Size: {file_size_kb:.2f} KB\n\n"
            f"▓░░░░░░░░░ 0%",
            parse_mode="HTML"
        )
        
        await asyncio.sleep(0.3)
        await status_msg.edit_text(
            f"📥 <b>Downloading...</b>\n\n"
            f"📄 File: <code>{file_name}</code>\n"
            f"💾 Size: {file_size_kb:.2f} KB\n\n"
            f"▓▓▓░░░░░░░ 30%",
            parse_mode="HTML"
        )
        
        await bot.download(document, destination=file_path)

        actual_size = file_path.stat().st_size
        if actual_size > MAX_UPLOAD_BYTES:
            try:
                file_path.unlink()
            except OSError:
                pass
            await message.answer(
                f"❌ File too large after download: "
                f"{actual_size / (1024 * 1024):.1f} MB "
                f"(limit {MAX_UPLOAD_BYTES // (1024 * 1024)} MB)."
            )
            return
        
        await status_msg.edit_text(
            f"💾 <b>Saving to database...</b>\n\n"
            f"📄 File: <code>{file_name}</code>\n"
            f"💾 Size: {file_size_kb:.2f} KB\n\n"
            f"▓▓▓▓▓▓▓░░░ 70%",
            parse_mode="HTML"
        )
        
        if user_id not in user_files:
            user_files[user_id] = []

        # Keep the in-memory list consistent with the DB primary key.
        user_files[user_id] = [f for f in user_files[user_id] if f[0] != file_name]
        user_files[user_id].append((file_name, file_ext[1:]))

        conn = await get_db()
        now = datetime.now().isoformat()
        await conn.execute('INSERT OR REPLACE INTO user_files (user_id, file_name, file_type, upload_date) VALUES (?, ?, ?, ?)',
                          (user_id, file_name, file_ext[1:], now))
        await conn.execute('UPDATE bot_stats SET stat_value = stat_value + 1 WHERE stat_name = ?', ('total_uploads',))
        await conn.commit()

        bot_stats['total_uploads'] = bot_stats.get('total_uploads', 0) + 1
        
        await status_msg.edit_text(
            f"✅ <b>Finalizing...</b>\n\n"
            f"📄 File: <code>{file_name}</code>\n"
            f"💾 Size: {file_size_kb:.2f} KB\n\n"
            f"▓▓▓▓▓▓▓▓▓▓ 100%",
            parse_mode="HTML"
        )
        
        await asyncio.sleep(0.5)
        
        if file_ext == '.zip':
            keyboard = InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="📦 Extract ZIP", callback_data=f"extract_zip:{file_name}"),
                 InlineKeyboardButton(text="⭐ Add Favorite", callback_data=f"toggle_fav:{file_name}")],
                [InlineKeyboardButton(text="ℹ️ File Info", callback_data=f"file_info:{file_name}"),
                 InlineKeyboardButton(text="🗑️ Delete", callback_data=f"delete_file:{file_name}")],
                [InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
                 InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
            ])
        else:
            keyboard = InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="▶️ Run Now", callback_data=f"run_script:{file_name}"),
                 InlineKeyboardButton(text="⭐ Add Favorite", callback_data=f"toggle_fav:{file_name}")],
                [InlineKeyboardButton(text="ℹ️ File Info", callback_data=f"file_info:{file_name}"),
                 InlineKeyboardButton(text="🗑️ Delete", callback_data=f"delete_file:{file_name}")],
                [InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
                 InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
            ])
        
        await status_msg.edit_text(
            f"""
╔═══════════════════════╗
    ✅ <b>UPLOAD SUCCESS!</b> ✅
╚═══════════════════════╝

📄 <b>File:</b> <code>{file_name}</code>
📦 <b>Type:</b> {file_ext[1:].upper()}
💾 <b>Size:</b> {document.file_size / 1024:.2f} KB
📊 <b>Usage:</b> {current_files + 1}/{_format_limit(limit)}

🎉 File uploaded successfully!
""",
            reply_markup=keyboard,
            parse_mode="HTML"
        )
    except Exception as e:
        logger.error(f"Error uploading file: {e}", exc_info=True)
        try:
            if file_path.exists():
                file_path.unlink()
        except OSError:
            pass
        if user_id in user_files:
            user_files[user_id] = [f for f in user_files[user_id] if f[0] != file_name]
        await message.answer("❌ Upload failed. Please try again.")

def _terminate_process_tree(process: subprocess.Popen) -> None:
    """Terminate a process and its children without raising on stale PIDs."""
    try:
        parent = psutil.Process(process.pid)
        children = parent.children(recursive=True)
        for child in children:
            try:
                child.terminate()
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                pass
        try:
            parent.terminate()
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            pass
    except (psutil.NoSuchProcess, psutil.AccessDenied):
        pass


async def _watch_script(script_key: str, process: subprocess.Popen, log_file) -> None:
    """FIX_OPT_3: close log FD and release semaphore when a script exits naturally."""
    try:
        while process.poll() is None and not _shutdown_started:
            await asyncio.sleep(2)
    finally:
        if not log_file.closed:
            try:
                log_file.close()
            except Exception:
                pass
        info = bot_scripts.pop(script_key, None)
        if info is not None:
            script_owner_id = info.get('script_owner_id')
            conn = await get_db()
            await conn.execute('DELETE FROM running_scripts WHERE script_key = ?', (script_key,))
            await conn.commit()
            script_semaphore.release()
            logger.info("Script exited naturally: %s (user=%s, rc=%s)", script_key, script_owner_id, process.returncode)
        _script_watch_tasks.pop(script_key, None)


@dp.callback_query(F.data.startswith("run_script:"))
@user_access_guard
async def callback_run_script(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    try:
        file_name = _safe_filename(callback.data.split(":", 1)[1])
    except ValueError:
        await callback.answer("❌ Invalid filename!", show_alert=True)
        return

    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    file_path = user_folder / file_name

    if not file_path.exists():
        await callback.answer("❌ File not found!", show_alert=True)
        return

    script_key = f"{user_id}_{file_name}"
    if script_key in bot_scripts:
        await callback.answer("⚠️ Script is already running!", show_alert=True)
        return

    file_ext = file_path.suffix.lower()
    if file_ext not in {'.py', '.js'}:
        await callback.answer("❌ Cannot run this file type!", show_alert=True)
        return

    log_file = None
    process = None
    acquired = False
    try:
        log_file_path = user_folder / f"{file_path.stem}.log"
        log_file = open(log_file_path, 'w', encoding='utf-8', buffering=1)

        # FIX_OPT_2.2: release only if THIS invocation acquired the semaphore.
        await script_semaphore.acquire()
        acquired = True

        command = [sys.executable, str(file_path)] if file_ext == '.py' else ['node', str(file_path)]
        popen_kwargs = {
            'cwd': str(user_folder),
            'stdout': log_file,
            'stderr': subprocess.STDOUT,
        }
        if os.name != 'nt':
            popen_kwargs['start_new_session'] = True
        process = subprocess.Popen(command, **popen_kwargs)

        bot_scripts[script_key] = {
            'process': process,
            'file_name': file_name,
            'script_owner_id': user_id,
            'start_time': datetime.now(),
            'user_folder': str(user_folder),
            'type': file_ext[1:],
            'log_file': log_file,
        }

        conn = await get_db()
        await conn.execute(
            'INSERT OR REPLACE INTO running_scripts (script_key, pid, user_id, file_name, started_at) VALUES (?, ?, ?, ?, ?)',
            (script_key, process.pid, user_id, file_name, datetime.now().isoformat()),
        )
        await conn.execute('UPDATE bot_stats SET stat_value = stat_value + 1 WHERE stat_name = ?', ('total_runs',))
        await conn.commit()
        bot_stats['total_runs'] = bot_stats.get('total_runs', 0) + 1

        _script_watch_tasks[script_key] = asyncio.create_task(_watch_script(script_key, process, log_file))

        await callback.answer(f"✅ Script started! (PID: {process.pid})", show_alert=True)
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🛑 Stop Script", callback_data=f"stop_script:{script_key}")],
            [InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
             InlineKeyboardButton(text="🏠 Home", callback_data="back_to_main")]
        ])
        await callback.message.edit_reply_markup(reply_markup=keyboard)

    except Exception as e:
        logger.error(f"Error running script: {e}", exc_info=True)
        if process is not None:
            try:
                process.terminate()
            except Exception:
                pass
        bot_scripts.pop(script_key, None)
        if log_file is not None and not log_file.closed:
            log_file.close()
        if acquired:
            script_semaphore.release()
        try:
            conn = await get_db()
            await conn.execute('DELETE FROM running_scripts WHERE script_key = ?', (script_key,))
            await conn.commit()
        except Exception:
            logger.exception("Failed to remove failed script registry entry")
        await callback.answer("❌ Error starting script. Please try again.", show_alert=True)

async def _stop_script_now(script_key: str) -> bool:
    script_info = bot_scripts.pop(script_key, None)
    if script_info is None:
        return False
    process = script_info['process']
    log_file = script_info.get('log_file')
    _terminate_process_tree(process)
    try:
        await asyncio.to_thread(process.wait, 5)
    except Exception:
        pass
    watch_task = _script_watch_tasks.pop(script_key, None)
    if watch_task is not None and watch_task is not asyncio.current_task():
        watch_task.cancel()
    if log_file and not log_file.closed:
        log_file.close()
    conn = await get_db()
    await conn.execute('DELETE FROM running_scripts WHERE script_key = ?', (script_key,))
    await conn.commit()
    script_semaphore.release()
    return True


@dp.callback_query(F.data.startswith("stop_script:"))
@user_access_guard
async def callback_stop_script(callback: types.CallbackQuery):
    # FIX_BUG_1: allow admins or the script owner to request stopping a running script.
    user_id = callback.from_user.id
    script_key = callback.data.split(":", 1)[1]
    script_info = bot_scripts.get(script_key)
    if script_info is None:
        await callback.answer("❌ Script not found or already stopped!", show_alert=True)
        return
    owner_id = script_info.get("script_owner_id")
    if user_id not in admin_ids and owner_id != user_id:
        await callback.answer("❌ You can only stop your own scripts.", show_alert=True)
        return
    back_data = "admin_running_scripts" if user_id in admin_ids else "check_files"
    _set_pending_confirmation(user_id, {"action": "stop_script", "script_key": script_key})
    await show_confirmation(
        callback,
        "🛑 Stop Script",
        f"Stop <code>{script_key}</code>? The running process will be terminated.",
        "🛑 Stop",
        "stop_script_confirm",
        "🔙 Back",
        back_data,
    )
    await callback.answer()


@dp.callback_query(F.data == "stop_script_confirm")
@user_access_guard
async def callback_stop_script_confirm(callback: types.CallbackQuery):
    # FIX_BUG_1: allow admins OR the script owner to stop a script.
    user_id = callback.from_user.id
    pending = _take_pending_confirmation(user_id, "stop_script")
    if pending is None:
        await callback.answer("❌ No pending stop action.", show_alert=True)
        return
    script_key = str(pending["script_key"])
    script_info = bot_scripts.get(script_key)
    if script_info is None:
        await callback.answer("❌ Script not found or already stopped.", show_alert=True)
        return
    owner_id = script_info.get("script_owner_id")
    if user_id not in admin_ids and owner_id != user_id:
        await callback.answer("❌ You can only stop your own scripts.", show_alert=True)
        return
    try:
        stopped = await _stop_script_now(script_key)
        if not stopped:
            await callback.answer("❌ Script not found or already stopped.", show_alert=True)
            return
        await callback.answer("✅ Script stopped successfully!", show_alert=True)
        if user_id in admin_ids:
            await callback_admin_panel(callback)
        else:
            await callback_check_files(callback)
    except Exception:
        logger.exception("Error stopping script")
        await callback.answer("❌ Error stopping script.", show_alert=True)


@dp.callback_query(F.data.startswith("extract_zip:"))
@user_access_guard
async def callback_extract_zip(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    try:
        file_name = _safe_filename(callback.data.split(":", 1)[1])
    except ValueError:
        await callback.answer("❌ Invalid filename!", show_alert=True)
        return

    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    zip_path = user_folder / file_name

    if not zip_path.exists():
        await callback.answer("❌ ZIP file not found!", show_alert=True)
        return

    if not zipfile.is_zipfile(zip_path):
        await callback.answer("❌ Invalid ZIP file!", show_alert=True)
        return

    extracted_paths = []
    try:
        status_text = f"""
╔═══════════════════════╗
    📦 <b>EXTRACTING ZIP</b> 📦
╚═══════════════════════╝

📄 File: <code>{file_name}</code>
⏳ Status: <b>Extracting...</b>

Please wait...
"""
        await callback.message.edit_text(status_text, parse_mode="HTML")

        # FIX_OPT_1.2: safe member-by-member extraction; no bulk extraction helper.
        with zipfile.ZipFile(zip_path, 'r') as zip_ref:
            members = zip_ref.infolist()
            total_uncompressed = sum(max(0, int(member.file_size)) for member in members)
            if total_uncompressed > MAX_EXTRACTED_BYTES:
                raise ValueError(
                    f"ZIP expands beyond the {MAX_EXTRACTED_BYTES // (1024 * 1024)} MB extraction limit"
                )

            root = user_folder.resolve()
            safe_members = []
            for member in members:
                member_path = PurePosixPath(member.filename)
                if member_path.is_absolute() or '..' in member_path.parts:
                    raise ValueError("unsafe path in ZIP")
                mode = (member.external_attr >> 16) & 0o170000
                if mode == 0o120000:
                    raise ValueError("symlink entries are not allowed in ZIP")
                target = (user_folder / Path(*member_path.parts)).resolve()
                try:
                    target.relative_to(root)
                except ValueError as exc:
                    raise ValueError("unsafe path in ZIP") from exc
                safe_members.append((member, target))

            for member, target in safe_members:
                if member.is_dir():
                    target.mkdir(parents=True, exist_ok=True)
                    continue
                target.parent.mkdir(parents=True, exist_ok=True)
                with zip_ref.open(member, 'r') as src_file, open(target, 'wb') as dst_file:
                    while True:
                        chunk = src_file.read(1024 * 1024)
                        if not chunk:
                            break
                        dst_file.write(chunk)
                extracted_paths.append(target)

        # FIX_BUG_2: the ZIP itself is removed after extraction, so it does not consume a final slot.
        runnable_paths = [
            path for path in extracted_paths
            if path.suffix.lower() in {'.py', '.js'}
        ]
        current_effective = len([
            f for f in user_files.get(user_id, [])
            if f[0] != file_name
        ])
        limit = get_user_file_limit(user_id)
        if current_effective + len(runnable_paths) > limit:
            if limit == float('inf'):
                remaining_label = "unlimited"
            else:
                remaining_label = str(max(0, int(limit - current_effective)))
            raise ValueError(
                f"ZIP contains {len(runnable_paths)} runnable file(s), but "
                f"only {remaining_label} slot(s) remain under your "
                f"{_format_limit(limit)}-file limit. Please delete some files or upgrade "
                f"to premium."
            )

        # FIX_BUG_3: register all-or-nothing; roll back DB and in-memory state on any failure.
        existing = {name for name, _ in user_files.get(user_id, [])}
        existing.discard(file_name)
        registered_files: list[str] = []
        moved_paths: list[tuple[Path, Path]] = []
        original_user_files = list(user_files.get(user_id, []))
        now = datetime.now().isoformat()
        conn = await get_db()
        try:
            for extracted_path in runnable_paths:
                base_name = extracted_path.name
                just_name = _unique_filename(base_name, existing)
                destination = user_folder / just_name
                if extracted_path.resolve() != destination.resolve():
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    extracted_path.replace(destination)
                    moved_paths.append((extracted_path, destination))
                existing.add(just_name)

                file_ext = destination.suffix.lower()[1:]
                user_files.setdefault(user_id, []).append((just_name, file_ext))
                await conn.execute(
                    'INSERT OR REPLACE INTO user_files (user_id, file_name, file_type, upload_date) VALUES (?, ?, ?, ?)',
                    (user_id, just_name, file_ext, now)
                )
                registered_files.append(just_name)

            # Remove the source ZIP from the DB in the same transaction.
            if user_id in user_files:
                user_files[user_id] = [f for f in user_files[user_id] if f[0] != file_name]
            await conn.execute(
                'DELETE FROM user_files WHERE user_id = ? AND file_name = ?', (user_id, file_name)
            )
            await conn.execute(
                'DELETE FROM favorites WHERE user_id = ? AND file_name = ?', (user_id, file_name)
            )
            await conn.commit()
        except Exception:
            try:
                await conn.rollback()
            except Exception:
                logger.exception("Rollback failed during ZIP extraction")
            # FIX_BUG_3: restore the exact pre-extraction in-memory file state, including the ZIP.
            user_files[user_id] = original_user_files
            for source, destination in reversed(moved_paths):
                try:
                    if destination.exists():
                        destination.replace(source)
                except Exception:
                    logger.debug(
                        "Failed to undo move %s -> %s", destination, source, exc_info=True
                    )
            raise

        try:
            zip_path.unlink()
        except OSError:
            pass

        for path in extracted_paths:
            if path.exists() and path.is_file():
                try:
                    path.unlink()
                except OSError:
                    pass
        # Remove now-empty nested directories, but never the user's root folder.
        for directory in sorted(
            {path.parent for path in extracted_paths if path.parent != user_folder},
            key=lambda item: len(item.parts),
            reverse=True,
        ):
            try:
                directory.rmdir()
            except OSError:
                pass

        registered_text = "\n".join([f"  • <code>{f}</code>" for f in registered_files[:10]])
        if len(registered_files) > 10:
            registered_text += f"\n  ... and {len(registered_files) - 10} more files"
        elif len(registered_files) == 0:
            registered_text = "  <i>No .py or .js files found</i>"

        current_count = len(user_files.get(user_id, []))
        success_text = f"""
╔═══════════════════════╗
    ✅ <b>EXTRACTION SUCCESS!</b> ✅
╚═══════════════════════╝

📄 <b>ZIP File:</b> <code>{file_name}</code>
📊 <b>Total Extracted:</b> {len(extracted_paths)} files
✅ <b>Registered:</b> {len(registered_files)} files (.py, .js)
🗑️ <b>ZIP Deleted:</b> Automatically

<b>📋 Registered Files:</b>
{registered_text}

📦 <b>Your Files:</b> {current_count}/{_format_limit(limit)}

✨ Extraction completed successfully!
"""

        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
             InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
        ])
        await callback.message.edit_text(success_text, reply_markup=keyboard, parse_mode="HTML")
        await callback.answer("✅ ZIP extracted & registered!")

    except zipfile.BadZipFile:
        await callback.answer("❌ Corrupted ZIP file!", show_alert=True)
    except Exception as e:
        # FIX_UI_LIMIT: rejection/failure removes extracted output but preserves the original ZIP.
        for path in extracted_paths:
            try:
                if path.exists() and path.is_file():
                    path.unlink()
            except OSError:
                pass
        for directory in sorted(
            {path.parent for path in extracted_paths if path.parent != user_folder},
            key=lambda item: len(item.parts),
            reverse=True,
        ):
            try:
                directory.rmdir()
            except OSError:
                pass
        logger.error(f"Error extracting ZIP: {e}", exc_info=True)
        await callback.answer(f"❌ Extraction failed: {str(e)}", show_alert=True)

async def _delete_file_now(user_id: int, file_name: str) -> None:
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    file_path = user_folder / file_name
    script_key = f"{user_id}_{file_name}"

    if script_key in bot_scripts:
        script_info = bot_scripts.pop(script_key)
        process = script_info.get("process")
        log_file = script_info.get("log_file")
        if process is not None:
            _terminate_process_tree(process)
            try:
                await asyncio.to_thread(process.wait, 5)
            except Exception:
                pass
        watch_task = _script_watch_tasks.pop(script_key, None)
        if watch_task is not None and watch_task is not asyncio.current_task():
            watch_task.cancel()
        if log_file and not log_file.closed:
            log_file.close()
        conn = await get_db()
        await conn.execute('DELETE FROM running_scripts WHERE script_key = ?', (script_key,))
        await conn.commit()
        script_semaphore.release()

    if file_path.exists():
        file_path.unlink()
    user_files[user_id] = [f for f in user_files.get(user_id, []) if f[0] != file_name]
    if file_name in user_favorites.get(user_id, []):
        user_favorites[user_id].remove(file_name)
    conn = await get_db()
    await conn.execute('DELETE FROM user_files WHERE user_id = ? AND file_name = ?', (user_id, file_name))
    await conn.execute('DELETE FROM favorites WHERE user_id = ? AND file_name = ?', (user_id, file_name))
    await conn.commit()


@dp.callback_query(F.data.startswith("delete_file:"))
@user_access_guard
async def callback_delete_file(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    try:
        file_name = _safe_filename(callback.data.split(":", 1)[1])
    except ValueError:
        await callback.answer("❌ Invalid filename!", show_alert=True)
        return
    file_path = UPLOAD_BOTS_DIR / str(user_id) / file_name
    if not file_path.exists():
        await callback.answer("❌ File not found!", show_alert=True)
        return

    _set_pending_confirmation(user_id, {"action": "delete_file", "file_name": file_name})
    await show_confirmation(
        callback,
        "🗑️ Delete File",
        f"Delete <code>{file_name}</code>? A running script will also be stopped.",
        "🗑️ Delete",
        "delete_file_confirm",
        "🔙 Back",
        "check_files",
    )
    await callback.answer()


@dp.callback_query(F.data == "delete_file_confirm")
@user_access_guard
async def callback_delete_file_confirm(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    pending = _take_pending_confirmation(user_id, "delete_file")
    file_name = pending.get("file_name") if pending else None
    if pending is None or not file_name:
        await callback.answer("❌ No pending delete action.", show_alert=True)
        return
    try:
        file_name = _safe_filename(file_name)
        await _delete_file_now(user_id, file_name)
        await callback.answer("✅ File deleted successfully!", show_alert=True)
        await callback_check_files(callback)
    except Exception as e:
        logger.error(f"Error deleting file: {e}", exc_info=True)
        await callback.answer("❌ Error deleting file.", show_alert=True)


@dp.callback_query(F.data == "admin_total_users")
@user_access_guard
async def callback_admin_total_users(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    user_list = "\n".join([f"• <code>{uid}</code>" for uid in list(active_users)[:15]])
    text = f"""
╔═══════════════════════╗
    👥 <b>USER STATISTICS</b> 👥
╚═══════════════════════╝

📊 <b>Total Users:</b> {len(active_users)}
🚫 <b>Banned:</b> {len(banned_users)}
✅ <b>Active:</b> {len(active_users) - len(banned_users)}

<b>📝 Recent Users (15):</b>
{user_list}

{'...' if len(active_users) > 15 else ''}
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_total_files")
@user_access_guard
async def callback_admin_total_files(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    total_files = sum(len(files) for files in user_files.values())
    py_files = sum(1 for files in user_files.values() for f in files if f[1] == 'py')
    js_files = sum(1 for files in user_files.values() for f in files if f[1] == 'js')
    zip_files = sum(1 for files in user_files.values() for f in files if f[1] == 'zip')
    
    text = f"""
╔═══════════════════════╗
    📁 <b>FILE STATISTICS</b> 📁
╚═══════════════════════╝

📊 <b>Total Files:</b> {total_files}

<b>📦 By Type:</b>
🐍 Python: {py_files}
🟨 JavaScript: {js_files}
📦 ZIP: {zip_files}

<b>📈 Top Users:</b>
"""
    
    top_users = sorted(user_files.items(), key=lambda x: len(x[1]), reverse=True)[:5]
    for user_id, files in top_users:
        text += f"• User <code>{user_id}</code>: {len(files)} files\n"
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_running_scripts")
@user_access_guard
async def callback_admin_running_scripts(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    if not bot_scripts:
        text = """
╔═══════════════════════╗
    🚀 <b>RUNNING SCRIPTS</b> 🚀
╚═══════════════════════╝

💤 No scripts running currently
"""
        buttons = []
    else:
        text = f"""
╔═══════════════════════╗
    🚀 <b>RUNNING ({len(bot_scripts)})</b> 🚀
╚═══════════════════════╝

"""
        buttons = []
        for script_key, info in bot_scripts.items():
            runtime = (datetime.now() - info['start_time']).total_seconds()
            text += f"🔸 <code>{info['file_name']}</code>\n"
            text += f"   PID: {info['process'].pid} | User: {info['script_owner_id']}\n"
            text += f"   Runtime: {int(runtime)}s\n\n"
            buttons.append([InlineKeyboardButton(
                text=f"🛑 Stop {info['file_name'][:15]}", 
                callback_data=f"stop_script:{script_key}"
            )])
    
    buttons.append([InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")])
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_premium_users")
@user_access_guard
async def callback_admin_premium_users(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    premium_users = [(u, data) for u, data in user_subscriptions.items() if data['expiry'] > datetime.now()]
    
    if not premium_users:
        text = """
╔═══════════════════════╗
    💎 <b>PREMIUM USERS</b> 💎
╚═══════════════════════╝

No active premium subscriptions.
"""
    else:
        text = f"""
╔═══════════════════════╗
    💎 <b>PREMIUM ({len(premium_users)})</b> 💎
╚═══════════════════════╝

"""
        for user_id, data in premium_users:
            expiry_date = data['expiry'].strftime('%Y-%m-%d')
            text += f"💎 User <code>{user_id}</code>\n   Expires: {expiry_date}\n\n"
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Add Premium", callback_data="add_premium")],
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_analytics")
@user_access_guard
async def callback_admin_analytics(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = f"""
╔═══════════════════════╗
    📊 <b>BOT ANALYTICS</b> 📊
╚═══════════════════════╝

<b>📈 GLOBAL STATS:</b>

📤 Total Uploads: {bot_stats.get('total_uploads', 0)}
📥 Total Downloads: {bot_stats.get('total_downloads', 0)}
▶️ Script Runs: {bot_stats.get('total_runs', 0)}
👥 Total Users: {len(active_users)}
📁 Total Files: {sum(len(files) for files in user_files.values())}
🚀 Running Now: {len(bot_scripts)}
⭐ Total Favorites: {sum(len(favs) for favs in user_favorites.values())}

<b>💎 PREMIUM:</b>
Active: {len([u for u in user_subscriptions if user_subscriptions[u]['expiry'] > datetime.now()])}
Expired: {len([u for u in user_subscriptions if user_subscriptions[u]['expiry'] <= datetime.now()])}

<b>🛡️ SECURITY:</b>
Banned Users: {len(banned_users)}
Admins: {len(admin_ids)}
Bot Status: {'🔒 Locked' if bot_locked else '✅ Active'}
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_system_status")
@user_access_guard
async def callback_admin_system_status(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    cpu = psutil.cpu_percent(interval=1)
    memory = psutil.virtual_memory()
    disk = psutil.disk_usage('/')
    
    text = f"""
╔═══════════════════════╗
    ⚙️ <b>SYSTEM STATUS</b> ⚙️
╚═══════════════════════╝

<b>💻 CPU:</b>
Usage: {cpu}%
{'🟢 Normal' if cpu < 70 else '🟡 High' if cpu < 90 else '🔴 Critical'}

<b>🧠 MEMORY:</b>
Used: {memory.percent}%
Free: {memory.available / (1024**3):.1f} GB
Total: {memory.total / (1024**3):.1f} GB

<b>💾 DISK:</b>
Used: {disk.percent}%
Free: {disk.free / (1024**3):.1f} GB
Total: {disk.total / (1024**3):.1f} GB

<b>🤖 BOT STATUS:</b>
Status: {'🔒 Locked' if bot_locked else '✅ Running'}
Scripts: {len(bot_scripts)} active
Uptime: ✅ Online
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Refresh", callback_data="admin_system_status")],
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_add_admin")
@user_access_guard
async def callback_admin_add_admin(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    ➕ <b>ADD ADMIN</b> ➕
╚═══════════════════════╝

To add a new admin, use:
<code>/addadmin USER_ID</code>

<b>Example:</b>
<code>/addadmin 123456789</code>

The user will get full admin privileges!
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_remove_admin")
@user_access_guard
async def callback_admin_remove_admin(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = f"""
╔═══════════════════════╗
    ➖ <b>REMOVE ADMIN</b> ➖
╚═══════════════════════╝

<b>Current Admins ({len(admin_ids)}):</b>

"""
    
    for admin_id in admin_ids:
        text += f"👑 <code>{admin_id}</code>\n"
    
    text += "\n<b>To remove:</b>\n<code>/removeadmin USER_ID</code>"
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_ban_user")
@user_access_guard
async def callback_admin_ban_user(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = f"""
╔═══════════════════════╗
    🚫 <b>BAN USER</b> 🚫
╚═══════════════════════╝

<b>Currently Banned:</b> {len(banned_users)} users

To ban a user, use:
<code>/ban USER_ID REASON</code>

<b>Example:</b>
<code>/ban 123456789 Spam</code>

Banned users cannot use the bot!
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_unban_user")
@user_access_guard
async def callback_admin_unban_user(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = f"""
╔═══════════════════════╗
    ✅ <b>UNBAN USER</b> ✅
╚═══════════════════════╝

<b>Banned Users:</b> {len(banned_users)}

"""
    
    if banned_users:
        text += "<b>List:</b>\n"
        for ban_id in list(banned_users)[:10]:
            text += f"🚫 <code>{ban_id}</code>\n"
    
    text += "\n<b>To unban:</b>\n<code>/unban USER_ID</code>"
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "lock_bot")
@user_access_guard
async def callback_lock_bot(callback: types.CallbackQuery):
    global bot_locked
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    if bot_locked:
        bot_locked = False
        conn = await get_db()
        await conn.execute(
            'INSERT OR REPLACE INTO bot_stats (stat_name, stat_value) VALUES (?, ?)',
            ('bot_locked', 0),
        )
        await conn.commit()
        await callback.answer("🔓 Bot unlocked!", show_alert=True)
        await callback_admin_panel(callback)
        return
    _set_pending_confirmation(callback.from_user.id, {"action": "lock_bot"})
    await show_confirmation(
        callback,
        "🔒 Lock Bot",
        "Lock the bot for non-admin users? User-facing actions will be blocked until you unlock it.",
        "🔒 Lock",
        "lock_bot_confirm",
        "🔙 Back",
        "admin_panel",
    )
    await callback.answer()


@dp.callback_query(F.data == "lock_bot_confirm")
@user_access_guard
async def callback_lock_bot_confirm(callback: types.CallbackQuery):
    global bot_locked
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    pending = _take_pending_confirmation(callback.from_user.id, "lock_bot")
    if pending is None:
        await callback.answer("❌ No pending lock action.", show_alert=True)
        return
    bot_locked = True
    conn = await get_db()
    await conn.execute(
        'INSERT OR REPLACE INTO bot_stats (stat_name, stat_value) VALUES (?, ?)',
        ('bot_locked', 1),
    )
    await conn.commit()
    await callback.answer("🔒 Bot locked!", show_alert=True)
    await callback_admin_panel(callback)


@dp.callback_query(F.data == "broadcast")
@user_access_guard
async def callback_broadcast(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = f"""
╔═══════════════════════╗
    📢 <b>BROADCAST</b> 📢
╚═══════════════════════╝

Send a message to all users!

<b>Total Recipients:</b> {len(active_users)}

<b>Command:</b>
<code>/broadcast Your message here</code>

⚠️ Use this feature responsibly!
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "add_premium")
@user_access_guard
async def callback_add_premium(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    💎 <b>ADD PREMIUM</b> 💎
╚═══════════════════════╝

Give premium access to users!

<b>Command:</b>
<code>/addpremium USER_ID DAYS</code>

<b>Examples:</b>
<code>/addpremium 123456789 30</code> (30 days)
<code>/addpremium 987654321 7</code> (7 days)

Premium benefits:
• 50 file limit (vs 20)
• Priority support
• Premium badge
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_clean_files")
@user_access_guard
async def callback_admin_clean_files(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    🗑️ <b>CLEAN FILES</b> 🗑️
╚═══════════════════════╝

Clean old or unused files from the system.

<b>Options:</b>
• Delete files older than 30 days
• Remove files from banned users
• Clean temp/log files

<b>Command:</b>
<code>/clean OPTION</code>

⚠️ This action cannot be undone!
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_backup_db")
@user_access_guard
async def callback_admin_backup_db(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    try:
        backup_path = IROTECH_DIR / f"backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.db"
        
        conn = await get_db()
        backup_conn = await aiosqlite.connect(backup_path)
        await conn.backup(backup_conn)
        await backup_conn.close()
        
        await callback.answer("✅ Database backed up!", show_alert=True)
        
        await callback.message.answer_document(
            FSInputFile(backup_path),
            caption="💾 <b>Database Backup</b>\n\nCreated: " + datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            parse_mode="HTML"
        )
        
        backup_path.unlink()
        
    except Exception as e:
        logger.error(f"Backup error: {e}")
        await callback.answer(f"❌ Backup failed: {str(e)}", show_alert=True)

@dp.callback_query(F.data == "admin_view_logs")
@user_access_guard
async def callback_admin_view_logs(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    📝 <b>SYSTEM LOGS</b> 📝
╚═══════════════════════╝

View bot logs and activity.

<b>Available Logs:</b>
• Error logs
• User activity
• Script executions
• Admin actions

Logs are stored in the system directory.
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_restart_bot")
@user_access_guard
async def callback_admin_restart_bot(callback: types.CallbackQuery):
    if callback.from_user.id != OWNER_ID:
        await callback.answer("❌ Owner only!", show_alert=True)
        return
    _set_pending_confirmation(callback.from_user.id, {"action": "restart"})
    await show_confirmation(
        callback,
        "🔄 Restart Bot",
        "Restart the entire bot. All running scripts will be stopped and users may see brief downtime.",
        "🔄 Restart",
        "restart_confirm",
        "🔙 Back",
        "admin_panel",
    )
    await callback.answer()


@dp.callback_query(F.data == "restart_confirm")
@user_access_guard
async def callback_restart_confirm(callback: types.CallbackQuery):
    if callback.from_user.id != OWNER_ID:
        await callback.answer("❌ Owner only!", show_alert=True)
        return
    pending = _take_pending_confirmation(callback.from_user.id, "restart")
    if pending is None:
        await callback.answer("❌ No pending restart action.", show_alert=True)
        return
    await callback.answer("🔄 Restarting bot...")
    await shutdown()
    if os.name == "nt":
        subprocess.Popen([sys.executable] + sys.argv)
        os._exit(0)
    os.execv(sys.executable, [sys.executable] + sys.argv)


@dp.message(Command("addadmin"))
@user_access_guard
async def cmd_add_admin(message: types.Message):
    if message.from_user.id not in admin_ids:
        await message.answer("❌ Permission denied!")
        return
    
    try:
        args = message.text.split()
        if len(args) != 2:
            await message.answer("Usage: /addadmin USER_ID")
            return
        
        new_admin_id = int(args[1])
        
        if new_admin_id in admin_ids:
            await message.answer(f"✅ User {new_admin_id} is already an admin!")
            return
        
        admin_ids.add(new_admin_id)
        
        conn = await get_db()
        await conn.execute('INSERT OR IGNORE INTO admins (user_id) VALUES (?)', (new_admin_id,))
        await conn.commit()
        
        await message.answer(f"✅ User <code>{new_admin_id}</code> added as admin!", parse_mode="HTML")
        
    except ValueError:
        await message.answer("❌ Invalid USER_ID!")
    except Exception as e:
        logger.error(f"Error adding admin: {e}")
        await message.answer(f"❌ Error: {str(e)}")

@dp.message(Command("removeadmin"))
@user_access_guard
async def cmd_remove_admin(message: types.Message):
    if message.from_user.id != OWNER_ID:
        await message.answer("❌ Only owner can remove admins!")
        return
    try:
        args = message.text.split()
        if len(args) != 2:
            await message.answer("Usage: /removeadmin USER_ID")
            return
        remove_admin_id = int(args[1])
        if remove_admin_id == OWNER_ID:
            await message.answer("❌ Cannot remove owner!")
            return
        if remove_admin_id not in admin_ids:
            await message.answer(f"❌ User {remove_admin_id} is not an admin!")
            return
        _set_pending_confirmation(message.from_user.id, {
            "action": "remove_admin", "user_id": remove_admin_id
        })
        await show_confirmation(
            message,
            "➖ Confirm Admin Removal",
            f"Remove <code>{remove_admin_id}</code> from administrators?",
            "➖ Remove Admin",
            "remove_admin_confirm",
            "❌ Cancel",
            "admin_panel",
        )
    except ValueError:
        await message.answer("❌ Invalid USER_ID!")


@dp.callback_query(F.data == "remove_admin_confirm")
@user_access_guard
async def callback_remove_admin_confirm(callback: types.CallbackQuery):
    if callback.from_user.id != OWNER_ID:
        await callback.answer("❌ Owner only!", show_alert=True)
        return
    pending = _take_pending_confirmation(callback.from_user.id, "remove_admin")
    if pending is None:
        await callback.answer("❌ No pending removal action.", show_alert=True)
        return
    remove_admin_id = int(pending["user_id"])
    if remove_admin_id == OWNER_ID:
        await callback.answer("❌ Cannot remove owner!", show_alert=True)
        return
    admin_ids.discard(remove_admin_id)
    conn = await get_db()
    await conn.execute('DELETE FROM admins WHERE user_id = ?', (remove_admin_id,))
    await conn.commit()
    await callback.answer("✅ Admin removed.", show_alert=True)
    await callback_admin_panel(callback)


@dp.message(Command("addpremium"))
@user_access_guard
async def cmd_add_premium(message: types.Message):
    if message.from_user.id not in admin_ids:
        await message.answer("❌ Permission denied!")
        return
    
    try:
        args = message.text.split()
        if len(args) != 3:
            await message.answer("Usage: /addpremium USER_ID DAYS")
            return
        
        user_id = int(args[1])
        days = int(args[2])
        
        if days <= 0:
            await message.answer("❌ Days must be greater than 0!")
            return
        
        expiry = datetime.now() + timedelta(days=days)
        user_subscriptions[user_id] = {'expiry': expiry}
        
        conn = await get_db()
        await conn.execute('INSERT OR REPLACE INTO subscriptions (user_id, expiry) VALUES (?, ?)',
                          (user_id, expiry.isoformat()))
        await conn.commit()
        
        await message.answer(
            f"✅ <b>Premium Added!</b>\n\n"
            f"User: <code>{user_id}</code>\n"
            f"Duration: {days} days\n"
            f"Expires: {expiry.strftime('%Y-%m-%d %H:%M')}",
            parse_mode="HTML"
        )
        
    except ValueError:
        await message.answer("❌ Invalid input!")
    except Exception as e:
        logger.error(f"Error adding premium: {e}")
        await message.answer(f"❌ Error: {str(e)}")

@dp.message(Command("ban"))
@user_access_guard
async def cmd_ban_user(message: types.Message):
    if message.from_user.id not in admin_ids:
        await message.answer("❌ Permission denied!")
        return
    try:
        args = message.text.split(maxsplit=2)
        if len(args) < 2:
            await message.answer("Usage: /ban USER_ID [REASON]")
            return
        ban_user_id = int(args[1])
        reason = args[2] if len(args) > 2 else "No reason provided"
        if ban_user_id in admin_ids:
            await message.answer("❌ Cannot ban an admin!")
            return
        _set_pending_confirmation(message.from_user.id, {
            "action": "ban", "user_id": ban_user_id, "reason": reason
        })
        await show_confirmation(
            message,
            "🚫 Confirm Ban",
            f"Ban user <code>{ban_user_id}</code>?\nReason: {reason}",
            "🚫 Ban User",
            "ban_confirm",
            "❌ Cancel",
            "back_to_main",
        )
    except ValueError:
        await message.answer("❌ Invalid USER_ID!")


@dp.callback_query(F.data == "ban_confirm")
@user_access_guard
async def callback_ban_confirm(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    pending = _take_pending_confirmation(callback.from_user.id, "ban")
    if pending is None:
        await callback.answer("❌ No pending ban action.", show_alert=True)
        return
    ban_user_id = int(pending["user_id"])
    if ban_user_id in admin_ids:
        await callback.answer("❌ Cannot ban an admin!", show_alert=True)
        return
    reason = str(pending.get("reason") or "No reason provided")
    banned_users.add(ban_user_id)
    conn = await get_db()
    await conn.execute(
        'INSERT OR REPLACE INTO banned_users (user_id, banned_date, reason) VALUES (?, ?, ?)',
        (ban_user_id, datetime.now().isoformat(), reason)
    )
    await conn.commit()
    await callback.answer("🚫 User banned.", show_alert=True)
    await callback_admin_panel(callback)


@dp.message(Command("unban"))
@user_access_guard
async def cmd_unban_user(message: types.Message):
    if message.from_user.id not in admin_ids:
        await message.answer("❌ Permission denied!")
        return
    
    try:
        args = message.text.split()
        if len(args) != 2:
            await message.answer("Usage: /unban USER_ID")
            return
        
        unban_user_id = int(args[1])
        
        if unban_user_id not in banned_users:
            await message.answer(f"❌ User {unban_user_id} is not banned!")
            return
        
        banned_users.remove(unban_user_id)
        
        conn = await get_db()
        await conn.execute('DELETE FROM banned_users WHERE user_id = ?', (unban_user_id,))
        await conn.commit()
        
        await message.answer(f"✅ User <code>{unban_user_id}</code> has been unbanned!", parse_mode="HTML")
        
    except ValueError:
        await message.answer("❌ Invalid USER_ID!")
    except Exception as e:
        logger.error(f"Error unbanning user: {e}")
        await message.answer(f"❌ Error: {str(e)}")

@dp.message(Command("broadcast"))
@user_access_guard
async def cmd_broadcast(message: types.Message):
    if message.from_user.id not in admin_ids:
        await message.answer("❌ Permission denied!")
        return
    
    try:
        broadcast_text = message.text.replace("/broadcast", "", 1).strip()
        
        if not broadcast_text:
            await message.answer("Usage: /broadcast Your message here")
            return
        
        sent_count = 0
        failed_count = 0
        
        status_msg = await message.answer(f"📢 Broadcasting to {len(active_users)} users...")
        
        for user_id in active_users:
            if user_id in banned_users:
                continue
            
            try:
                await bot.send_message(user_id, f"📢 <b>Announcement:</b>\n\n{broadcast_text}", parse_mode="HTML")
                sent_count += 1
                await asyncio.sleep(0.05)
            except Exception as e:
                logger.error(f"Failed to send to {user_id}: {e}")
                failed_count += 1
        
        await status_msg.edit_text(
            f"✅ <b>Broadcast Complete!</b>\n\n"
            f"✅ Sent: {sent_count}\n"
            f"❌ Failed: {failed_count}",
            parse_mode="HTML"
        )
        
    except Exception as e:
        logger.error(f"Error broadcasting: {e}")
        await message.answer(f"❌ Error: {str(e)}")

# FIX_OPT_2.7: implement commands referenced by the UI.
@dp.message(Command("premium"))
@user_access_guard
async def cmd_premium(message: types.Message):
    """FIX_OPT_7: provide the /premium command referenced by the help UI."""
    text = (
        "💎 <b>PREMIUM PLAN</b> 💎\n\n"
        "📦 20-file premium limit\n"
        "⚡ Priority processing\n"
        "📊 Advanced analytics\n"
        "💬 Priority support\n\n"
        f'Contact <a href="https://t.me/{YOUR_USERNAME.replace("@", "")}">owner</a> to upgrade.' 
    )
    await message.answer(text, parse_mode="HTML")


@dp.message(Command("restart"))
@user_access_guard
async def cmd_restart(message: types.Message):
    """FIX_OPT_7: owner-only restart command with an explicit confirmation."""
    if message.from_user.id != OWNER_ID:
        await message.answer("❌ Owner only!")
        return
    _set_pending_confirmation(message.from_user.id, {"action": "restart"})
    await show_confirmation(
        message,
        "🔄 Restart Bot",
        "Restart the entire bot. All running scripts will be stopped and users may see brief downtime.",
        "🔄 Restart",
        "restart_confirm",
        "❌ Cancel",
        "back_to_main",
    )


@dp.message(Command("clean"))
@user_access_guard
async def cmd_clean(message: types.Message):
    """FIX_OPT_7: cleanup command requires confirmation before deletion."""
    if message.from_user.id not in admin_ids:
        await message.answer("❌ Permission denied!")
        return
    args = message.text.split(maxsplit=1)
    option = args[1].strip().lower() if len(args) > 1 else ""
    if option not in {"old", "banned", "logs", "all"}:
        await message.answer("Usage: /clean old | banned | logs | all")
        return
    _set_pending_confirmation(message.from_user.id, {"action": "clean", "option": option})
    await show_confirmation(
        message,
        "🗑️ Confirm Cleanup",
        f"Run cleanup option <code>{option}</code>? This may permanently remove files or logs.",
        "🗑️ Clean",
        "clean_confirm",
        "❌ Cancel",
        "back_to_main",
    )


@dp.callback_query(F.data == "clean_confirm")
@user_access_guard
async def callback_clean_confirm(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    pending = _take_pending_confirmation(callback.from_user.id, "clean")
    if pending is None:
        await callback.answer("❌ No pending cleanup action.", show_alert=True)
        return
    option = pending.get("option")
    removed = 0
    now = datetime.now()
    try:
        if option in {"old", "all"}:
            cutoff = now - timedelta(days=30)
            conn = await get_db()
            cursor = await conn.execute('SELECT user_id, file_name, upload_date FROM user_files')
            rows = await cursor.fetchall()
            for row in rows:
                upload_date = row[2]
                try:
                    old_enough = bool(upload_date) and datetime.fromisoformat(upload_date) < cutoff
                except (TypeError, ValueError):
                    old_enough = False
                if not old_enough:
                    continue
                file_path = UPLOAD_BOTS_DIR / str(row[0]) / row[1]
                if file_path.exists():
                    file_path.unlink()
                    removed += 1
                await conn.execute('DELETE FROM user_files WHERE user_id = ? AND file_name = ?', (row[0], row[1]))
                await conn.execute('DELETE FROM favorites WHERE user_id = ? AND file_name = ?', (row[0], row[1]))
                user_files[row[0]] = [f for f in user_files.get(row[0], []) if f[0] != row[1]]

        if option in {"banned", "all"}:
            conn = await get_db()
            for banned_id in list(banned_users):
                folder = UPLOAD_BOTS_DIR / str(banned_id)
                if folder.exists():
                    for child in folder.iterdir():
                        if child.is_file():
                            child.unlink()
                            removed += 1
                    try:
                        folder.rmdir()
                    except OSError:
                        pass
                user_files.pop(banned_id, None)
                user_favorites.pop(banned_id, None)
            await conn.executemany('DELETE FROM user_files WHERE user_id = ?', [(u,) for u in banned_users])
            await conn.executemany('DELETE FROM favorites WHERE user_id = ?', [(u,) for u in banned_users])

        if option in {"logs", "all"}:
            for folder in UPLOAD_BOTS_DIR.iterdir():
                if not folder.is_dir():
                    continue
                for log_path in folder.glob('*.log'):
                    owner_id = int(folder.name) if folder.name.isdigit() else None
                    running = any(
                        info.get('script_owner_id') == owner_id
                        and info.get('log_file')
                        and Path(info['log_file'].name).name == log_path.name
                        for info in bot_scripts.values()
                    )
                    if not running:
                        try:
                            log_path.unlink()
                            removed += 1
                        except OSError:
                            pass

        conn = await get_db()
        await conn.commit()
        await callback.message.edit_text(
            f"✅ <b>Cleanup complete.</b>\n\nOption: <code>{option}</code>\nRemoved: {removed} item(s).",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
                InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel"),
                InlineKeyboardButton(text="🏠 Home", callback_data="back_to_main"),
            ]]),
        )
        await callback.answer("✅ Cleanup complete.")
    except Exception as exc:
        logger.error("Cleanup failed: %s", exc, exc_info=True)
        await callback.answer("❌ Cleanup failed. Check the bot logs.", show_alert=True)


@dp.message(Command("search"))
@user_access_guard
async def cmd_search_files(message: types.Message):
    user_id = message.from_user.id
    
    try:
        args = message.text.split(maxsplit=1)
        if len(args) < 2:
            await message.answer("Usage: /search filename")
            return
        
        search_term = args[1].lower()
        user_file_list = user_files.get(user_id, [])
        
        matches = [f for f in user_file_list if search_term in f[0].lower()]
        
        if not matches:
            await message.answer(f"🔍 No files found matching '<code>{search_term}</code>'", parse_mode="HTML")
            return
        
        text = f"🔍 <b>Search Results ({len(matches)}):</b>\n\n"
        
        for file_name, file_type in matches:
            icon = "🐍" if file_type == "py" else "🟨" if file_type == "js" else "📦"
            text += f"{icon} <code>{file_name}</code>\n"
        
        await message.answer(text, parse_mode="HTML")
        
    except Exception as e:
        logger.error(f"Search error: {e}")
        await message.answer(f"❌ Error: {str(e)}")

@dp.message(Command("help"))
@user_access_guard
async def cmd_help(message: types.Message):
    text = """
╔═══════════════════════╗
    ℹ️ <b>HELP & INFO</b> ℹ️
╚═══════════════════════╝

<b>🎯 HOW TO USE:</b>

1️⃣ <b>Upload Files:</b>
   • Click 'Upload File'
   • Send your .py, .js, or .zip file
   • File will be saved automatically

2️⃣ <b>Run Scripts:</b>
   • Go to 'My Files'
   • Click 'Run' on any file
   • Monitor script execution

3️⃣ <b>Manage Files:</b>
   • View all files in 'My Files'
   • Add to favorites with ⭐
   • Delete unwanted files (will stop running script)

4️⃣ <b>Search:</b>
   • Use /search [filename]
   • Quick file lookup

5️⃣ <b>Logs:</b>
   • Click '📄 Logs' to view script output
   • Click '📋 Copy Logs' to download full log

━━━━━━━━━━━━━━━━━━━━
<b>💡 COMMANDS:</b>

/start - Start the bot
/help - Show this help
/search - Search files
/stats - Your statistics
/premium - Premium info

<b>Need help? Contact owner! 💬</b>
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎯 Features", callback_data="all_features")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await message.answer(text, reply_markup=back_keyboard, parse_mode="HTML")

@dp.message(Command("stats"))
@user_access_guard
async def cmd_stats(message: types.Message):
    user_id = message.from_user.id
    user_file_count = len(user_files.get(user_id, []))
    user_fav_count = len(user_favorites.get(user_id, []))
    is_premium = user_id in user_subscriptions and user_subscriptions[user_id]['expiry'] > datetime.now()
    
    text = f"""
╔═══════════════════════╗
    📊 <b>YOUR STATISTICS</b> 📊
╚═══════════════════════╝

<b>👤 USER INFO:</b>

🆔 User ID: <code>{user_id}</code>
👤 Name: {message.from_user.full_name}
📦 Files Uploaded: {user_file_count}/{_format_limit(get_user_file_limit(user_id))}
⭐ Favorites: {user_fav_count}
💎 Account: {'Premium ✨' if is_premium else 'Free 🆓'}
🚀 Running: {sum(1 for k in bot_scripts if k.startswith(f"{user_id}_"))}

━━━━━━━━━━━━━━━━━━━━
📈 <b>USAGE:</b>

📤 Uploads: {bot_stats.get('total_uploads', 0)}
📥 Downloads: {bot_stats.get('total_downloads', 0)}
▶️ Script Runs: {bot_stats.get('total_runs', 0)}

{'✅ Bot Status: Active' if not bot_locked else '🔒 Bot: Maintenance'}
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await message.answer(text, reply_markup=back_keyboard, parse_mode="HTML")

# FIX_OPT_4.4 / FIX_OPT_8: web server lifecycle and graceful shutdown.
_web_runner = None
_web_task = None


async def web_server():
    # FIX_OPT_2.8: bind failures are logged and do not crash the bot.
    global _web_runner
    app = web.Application()

    async def handle(request):
        return web.Response(text="🚀 Advanced File Host Bot - Powered by Aiogram & Aiohttp!")

    app.router.add_get('/', handle)

    runner = web.AppRunner(app)
    try:
        await runner.setup()
        site = web.TCPSite(runner, '0.0.0.0', PORT)
        await site.start()
        _web_runner = runner
        logger.info("🌐 Web server started on port %s", PORT)
        while not _shutdown_started:
            await asyncio.sleep(3600)
    except OSError as exc:
        logger.error("Web server failed to bind on port %s: %s", PORT, exc)
    except asyncio.CancelledError:
        raise
    except Exception as exc:
        logger.error("Web server error: %s", exc, exc_info=True)
    finally:
        if _web_runner is runner:
            _web_runner = None
        try:
            await runner.cleanup()
        except Exception:
            logger.debug("Web runner cleanup failed", exc_info=True)


async def shutdown():
    # FIX_OPT_4.1: graceful shutdown terminates scripts and closes resources.
    global _shutdown_started, _web_task
    if _shutdown_started:
        return
    _shutdown_started = True
    logger.info("Shutting down...")

    # Stop web server first so no new work is accepted during teardown.
    if _web_task is not None and _web_task is not asyncio.current_task():
        _web_task.cancel()
        try:
            await _web_task
        except asyncio.CancelledError:
            pass

    # FIX_OPT_3 / FIX_OPT_4: terminate all child processes and cancel watchers.
    for key, info in list(bot_scripts.items()):
        process = info.get('process')
        if process is not None:
            _terminate_process_tree(process)
        watch_task = _script_watch_tasks.get(key)
        if watch_task is not None and watch_task is not asyncio.current_task():
            watch_task.cancel()

    watch_tasks = [task for task in _script_watch_tasks.values() if task is not asyncio.current_task()]
    if watch_tasks:
        await asyncio.gather(*watch_tasks, return_exceptions=True)
    _script_watch_tasks.clear()

    for info in list(bot_scripts.values()):
        log_file = info.get('log_file')
        if log_file is not None and not log_file.closed:
            try:
                log_file.close()
            except Exception:
                pass
    bot_scripts.clear()

    try:
        conn = await get_db()
        await conn.execute('DELETE FROM running_scripts')
        await conn.commit()
    except Exception:
        logger.exception("Failed to clear running script registry during shutdown")

    await close_db()
    try:
        await bot.session.close()
    except Exception:
        logger.debug("Bot session close failed", exc_info=True)
    logger.info("Shutdown complete.")


def _install_signal_handlers():
    """Install SIGINT/SIGTERM handlers on the active asyncio loop."""
    loop = asyncio.get_running_loop()
    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            loop.add_signal_handler(sig, lambda sig=sig: asyncio.create_task(shutdown()))
        except (NotImplementedError, RuntimeError):
            logger.debug("Signal handler unavailable for %s", sig)


# FIX_OPT_4.5: global aiogram error handler.
@dp.errors()
async def on_error(event: types.ErrorEvent):
    """FIX_OPT_4.5: global aiogram error handler."""
    logger.exception("Unhandled aiogram error: %s", event.exception)
    try:
        update = event.update
        if getattr(update, 'message', None):
            await update.message.answer("❌ Something went wrong. Try again.")
        elif getattr(update, 'callback_query', None):
            await update.callback_query.answer("❌ Error", show_alert=True)
    except Exception:
        pass


async def main():
    global _web_task
    logger.info("🚀 Starting Advanced File Host Bot...")
    await init_db()
    await migrate_db()
    await load_data()
    _install_signal_handlers()
    _web_task = asyncio.create_task(web_server())
    try:
        await dp.start_polling(bot)
    finally:
        await shutdown()


if __name__ == "__main__":
    asyncio.run(main())
