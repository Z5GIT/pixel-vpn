# telegram_bot.py
# ══════════════════════════════════════════════════════════════════════════════
# ربات مدیریت تلگرام — ساخت/حذف/فعال‌غیرفعال/مشاهده‌ی کانفیگ‌ها، فقط برای ادمین‌های
# مجاز (TELEGRAM_ADMIN_IDS). با long polling کار می‌کنه، نیازی به دامنه/webhook نداره.
# ══════════════════════════════════════════════════════════════════════════════

import asyncio
import os
import re
import json
from pathlib import Path
from zoneinfo import ZoneInfo

import httpx

from datetime import datetime, timedelta

from main import (
    LINKS,
    make_link,
    remove_link,
    set_link_active,
    vless_link_for_link,
    get_host,
    fmt_bytes,
    is_link_allowed,
    logger,
    PROTOCOLS,
    DEFAULT_PROTOCOL,
    FINGERPRINTS,
    DEFAULT_FINGERPRINT,
    DEFAULT_ALPN_BY_PROTOCOL,
    DEFAULT_PORT,
    DEFAULT_SPEED_LIMIT,
    MIN_PORT,
    MAX_PORT,
    parse_size_to_bytes,
    parse_speed_to_bytes,
    SUBS,
    create_sub_group,
    set_link_sub,
    remove_sub_group,
)

BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
_admin_ids_raw = os.environ.get("TELEGRAM_ADMIN_IDS", "").strip()
ADMIN_IDS = {int(x) for x in _admin_ids_raw.replace(" ", "").split(",") if x.isdigit()} if _admin_ids_raw else set()

# امکانات عمومی ربات
TELEGRAM_CHANNEL_ID = os.environ.get("TELEGRAM_CHANNEL_ID", "").strip()
DATA_DIR = Path(os.environ.get("DATA_DIR", "/data"))
BOT_STATE_FILE = DATA_DIR / "telegram_bot_state.json"
BOT_STATE = {"channel_id": TELEGRAM_CHANNEL_ID, "daily_claims": {}}
IRAN_TZ = ZoneInfo("Asia/Tehran")
FREE_VOLUME_BYTES = parse_size_to_bytes(1, "GB")

API_BASE = f"https://api.telegram.org/bot{BOT_TOKEN}"
PAGE_SIZE = 6

_client: httpx.AsyncClient | None = None
_poll_task: asyncio.Task | None = None
_running = False
_pending: dict = {}   # chat_id -> {"action": "wizard", "step": "...", "data": {...}}


def _load_bot_state():
    global BOT_STATE
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        if BOT_STATE_FILE.exists():
            raw = json.loads(BOT_STATE_FILE.read_text(encoding="utf-8"))
            if isinstance(raw, dict):
                BOT_STATE["channel_id"] = str(raw.get("channel_id") or TELEGRAM_CHANNEL_ID).strip()
                claims = raw.get("daily_claims", {})
                BOT_STATE["daily_claims"] = claims if isinstance(claims, dict) else {}
    except Exception as e:
        logger.warning(f"Telegram bot state load failed: {e}")


def _save_bot_state():
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        tmp = BOT_STATE_FILE.with_suffix(".tmp")
        tmp.write_text(json.dumps(BOT_STATE, ensure_ascii=False, indent=2), encoding="utf-8")
        tmp.replace(BOT_STATE_FILE)
    except Exception as e:
        logger.warning(f"Telegram bot state save failed: {e}")


def _channel_id() -> str:
    return str(BOT_STATE.get("channel_id") or "").strip()


def _today_key() -> str:
    return datetime.now(IRAN_TZ).date().isoformat()


def _user_has_claimed_today(user_id: int) -> bool:
    return BOT_STATE.get("daily_claims", {}).get(str(user_id)) == _today_key()


def _mark_user_claimed_today(user_id: int):
    BOT_STATE.setdefault("daily_claims", {})[str(user_id)] = _today_key()
    _save_bot_state()


def _is_admin(chat_id: int) -> bool:
    return chat_id in ADMIN_IDS


# ── Config creation wizard ────────────────────────────────────────────────────
# مراحل ساخت کانفیگ جدید، دقیقاً هم‌راستا با فیلدهایی که پنل وب موقع ساخت کاربر می‌گیره:
# برچسب، پروتکل، fingerprint، ALPN، پورت، محدودیت حجم، محدودیت سرعت، محدودیت آی‌پی، روز انقضا.
WIZARD_STEPS = ["label", "protocol", "fingerprint", "alpn", "port", "volume", "speed", "iplimit", "days"]

PROTOCOL_LABELS = {
    "vless-ws": "VLESS + WebSocket",
    "xhttp-packet-up": "XHTTP (packet-up)",
    "xhttp-stream-up": "XHTTP (stream-up)",
    "xhttp-stream-one": "XHTTP (stream-one)",
}

def _protocol_label(p: str) -> str:
    return PROTOCOL_LABELS.get(p, p)

def _fp_label(fp: str) -> str:
    return fp.capitalize()

_VOLUME_RE = re.compile(r"^([\d.]+)\s*(GB|MB|KB)?$", re.IGNORECASE)
_SPEED_RE = re.compile(r"^([\d.]+)\s*(MBIT|MBPS|MB|KB)?$", re.IGNORECASE)

def _parse_volume_text(text: str):
    """ورودی مثل '10GB' یا '500 MB' رو به بایت تبدیل می‌کنه. اگه نامعتبر بود None برمی‌گردونه."""
    m = _VOLUME_RE.match(text.strip())
    if not m:
        return None
    try:
        value = float(m.group(1))
    except ValueError:
        return None
    if value <= 0:
        return 0
    unit = (m.group(2) or "GB").upper()
    return parse_size_to_bytes(value, unit)

def _parse_speed_text(text: str):
    """ورودی مثل '20' یا '20Mbit' رو به بایت‌بر‌ثانیه تبدیل می‌کنه (پیش‌فرض واحد Mbit)."""
    m = _SPEED_RE.match(text.strip())
    if not m:
        return None
    try:
        value = float(m.group(1))
    except ValueError:
        return None
    if value <= 0:
        return 0
    unit_raw = (m.group(2) or "MBIT").upper()
    unit = "MBIT" if unit_raw in ("MBIT", "MBPS") else unit_raw
    return parse_speed_to_bytes(value, unit)

def _parse_nonneg_int(text: str):
    try:
        n = int(text.strip())
    except ValueError:
        return None
    return max(0, n)

# ── Telegram API helpers ────────────────────────────────────────────────────
async def _call(method: str, **params):
    if _client is None:
        return None
    try:
        r = await _client.post(f"{API_BASE}/{method}", json=params, timeout=40)
        data = r.json()
        if not data.get("ok"):
            logger.warning(f"Telegram API {method} failed: {data}")
        return data
    except Exception as e:
        logger.warning(f"Telegram API {method} error: {e}")
        return None

async def _send(chat_id: int, text: str, kb: dict | None = None):
    payload = {"chat_id": chat_id, "text": text, "parse_mode": "HTML", "disable_web_page_preview": True}
    if kb:
        payload["reply_markup"] = kb
    return await _call("sendMessage", **payload)

async def _edit(chat_id: int, message_id: int, text: str, kb: dict | None = None):
    payload = {"chat_id": chat_id, "message_id": message_id, "text": text, "parse_mode": "HTML", "disable_web_page_preview": True}
    if kb:
        payload["reply_markup"] = kb
    res = await _call("editMessageText", **payload)
    if res is None or not res.get("ok"):
        # اگه ادیت به هر دلیلی نشد (مثلاً پیام قدیمی/حذف‌شده)، پیام جدید بفرست
        await _send(chat_id, text, kb)

async def _answer_cb(cb_id: str, text: str = ""):
    await _call("answerCallbackQuery", callback_query_id=cb_id, text=text)

# ── Keyboards ────────────────────────────────────────────────────────────────
def _main_menu_kb():
    rows = [
        [{"text": "📋 لیست کانفیگ‌ها", "callback_data": "list:0"}],
        [{"text": "➕ ساخت کانفیگ جدید", "callback_data": "newcfg"}],
        [{"text": "📣 ارسال کانفیگ به کانال", "callback_data": "channel:menu"}],
        [{"text": "🗂 گروه‌های ساب (لینک حرفه‌ای)", "callback_data": "subs:0"}],
        [{"text": "🔄 رفرش", "callback_data": "menu"}],
    ]
    return {"inline_keyboard": rows}

def _links_list_kb(page: int):
    items = sorted(LINKS.items(), key=lambda kv: kv[1].get("created_at", ""), reverse=True)
    total = len(items)
    start = page * PAGE_SIZE
    chunk = items[start:start + PAGE_SIZE]
    rows = []
    for uid, l in chunk:
        dot = "🟢" if is_link_allowed(l) else "🔴"
        rows.append([{"text": f"{dot} {l.get('label','?')[:28]}", "callback_data": f"view:{uid}"}])
    nav = []
    if start > 0:
        nav.append({"text": "◀ قبلی", "callback_data": f"list:{page-1}"})
    if start + PAGE_SIZE < total:
        nav.append({"text": "بعدی ▶", "callback_data": f"list:{page+1}"})
    if nav:
        rows.append(nav)
    rows.append([{"text": "➕ ساخت کانفیگ جدید", "callback_data": "newcfg"}])
    rows.append([{"text": "⬅ منوی اصلی", "callback_data": "menu"}])
    return {"inline_keyboard": rows}

def _link_detail_kb(uid: str, active: bool):
    return {"inline_keyboard": [
        [{"text": "🔗 نمایش لینک اتصال", "callback_data": f"link:{uid}"}],
        [{"text": "🗂 گروه ساب (لینک حرفه‌ای)", "callback_data": f"cfggroup:{uid}"}],
        [{"text": ("⛔ غیرفعال‌سازی" if active else "✅ فعال‌سازی"), "callback_data": f"toggle:{uid}"}],
        [{"text": "🗑 حذف کانفیگ", "callback_data": f"del:{uid}"}],
        [{"text": "⬅ بازگشت به لیست", "callback_data": "list:0"}],
    ]}

def _confirm_delete_kb(uid: str):
    return {"inline_keyboard": [
        [{"text": "✅ بله، حذف کن", "callback_data": f"delok:{uid}"},
         {"text": "❌ انصراف", "callback_data": f"view:{uid}"}],
    ]}

# ── Wizard keyboards ─────────────────────────────────────────────────────────
def _wizard_cancel_kb():
    return {"inline_keyboard": [[{"text": "❌ انصراف", "callback_data": "w:cancel"}]]}

def _wizard_protocol_kb():
    rows = [[{"text": _protocol_label(p), "callback_data": f"w:proto:{p}"}] for p in PROTOCOLS]
    rows.append([{"text": "❌ انصراف", "callback_data": "w:cancel"}])
    return {"inline_keyboard": rows}

def _wizard_fp_kb():
    rows, row = [], []
    for fp in FINGERPRINTS:
        row.append({"text": _fp_label(fp), "callback_data": f"w:fp:{fp}"})
        if len(row) == 3:
            rows.append(row); row = []
    if row:
        rows.append(row)
    rows.append([{"text": "❌ انصراف", "callback_data": "w:cancel"}])
    return {"inline_keyboard": rows}

def _wizard_skip_kb(step_key: str, label: str):
    return {"inline_keyboard": [
        [{"text": label, "callback_data": f"w:skip:{step_key}"}],
        [{"text": "❌ انصراف", "callback_data": "w:cancel"}],
    ]}

ALPN_PRESET_MAP = {"p1": "http/1.1", "p2": "h2,http/1.1", "p3": "h2"}

def _wizard_alpn_kb():
    return {"inline_keyboard": [
        [{"text": "🔤 http/1.1 (پیشنهادی)", "callback_data": "w:alpnpreset:p1"}],
        [{"text": "🔤 h2,http/1.1", "callback_data": "w:alpnpreset:p2"}],
        [{"text": "🔤 h2", "callback_data": "w:alpnpreset:p3"}],
        [{"text": "⏭ پیش‌فرض پروتکل", "callback_data": "w:skip:alpn"}],
        [{"text": "❌ انصراف", "callback_data": "w:cancel"}],
    ]}

def _wizard_unlimited_kb(step_key: str):
    return _wizard_skip_kb(step_key, "♾ نامحدود")

def _wizard_confirm_kb():
    return {"inline_keyboard": [
        [{"text": "✅ ساخت کانفیگ", "callback_data": "w:confirm"}],
        [{"text": "❌ انصراف", "callback_data": "w:cancel"}],
    ]}

def _wizard_prompt(step: str, data: dict) -> str:
    n = WIZARD_STEPS.index(step) + 1 if step in WIZARD_STEPS else len(WIZARD_STEPS)
    head = f"🧩 ساخت کانفیگ جدید — مرحله {n}/{len(WIZARD_STEPS)}\n\n"
    if step == "label":
        return head + "✏️ اسم/برچسب کانفیگ رو بفرست:"
    if step == "protocol":
        return head + "🌐 پروتکل رو از دکمه‌های زیر انتخاب کن:"
    if step == "fingerprint":
        return head + "🖐 Fingerprint (uTLS) رو انتخاب کن:"
    if step == "alpn":
        return head + ("🔤 ALPN رو از دکمه‌های زیر انتخاب کن (پیشنهادی: <code>http/1.1</code>)\n"
                        "یا خودت هر مقدار دلخواهی رو تایپ و ارسال کن (مثلاً h2,http/1.1):")
    if step == "port":
        return head + f"🔌 شماره پورت (بین {MIN_PORT} تا {MAX_PORT}) رو بفرست\nیا پیش‌فرض ({DEFAULT_PORT}) رو انتخاب کن:"
    if step == "volume":
        return head + "📦 محدودیت حجم مصرفی رو بفرست، مثلاً:\n<code>10GB</code> یا <code>500MB</code>\nیا دکمه‌ی نامحدود رو بزن:"
    if step == "speed":
        return head + "🚀 محدودیت سرعت رو به مگابیت‌بر‌ثانیه بفرست، مثلاً <code>20</code>\nیا دکمه‌ی نامحدود رو بزن:"
    if step == "iplimit":
        return head + "👥 حداکثر تعداد آی‌پی/کاربر هم‌زمان مجاز رو بفرست\nیا دکمه‌ی نامحدود رو بزن:"
    if step == "days":
        return head + "📅 تعداد روزهای اعتبار کانفیگ رو بفرست\nیا دکمه‌ی نامحدود (بدون انقضا) رو بزن:"
    return head

def _wizard_summary(data: dict) -> str:
    limit = "نامحدود" if not data.get("limit_bytes") else fmt_bytes(data["limit_bytes"])
    speed = "نامحدود" if not data.get("speed_limit_bytes") else f"{data['speed_limit_bytes']*8/1024/1024:.1f} Mbps"
    iplim = data.get("ip_limit", 0) or "نامحدود"
    days = data.get("expires_days", 0)
    days_txt = "بدون انقضا" if not days else f"{days} روز"
    proto = data.get("protocol", DEFAULT_PROTOCOL)
    alpn = data.get("alpn") or f"پیش‌فرض ({DEFAULT_ALPN_BY_PROTOCOL.get(proto, 'http/1.1')})"
    return (
        "🧩 خلاصه‌ی کانفیگ جدید — تایید کن:\n\n"
        f"برچسب: <b>{data.get('label','?')}</b>\n"
        f"پروتکل: {_protocol_label(proto)}\n"
        f"Fingerprint: {_fp_label(data.get('fingerprint', DEFAULT_FINGERPRINT))}\n"
        f"ALPN: {alpn}\n"
        f"پورت: {data.get('port', DEFAULT_PORT)}\n"
        f"محدودیت حجم: {limit}\n"
        f"محدودیت سرعت: {speed}\n"
        f"محدودیت آی‌پی: {iplim}\n"
        f"انقضا: {days_txt}"
    )

# ── View builders ────────────────────────────────────────────────────────────
def _format_detail(uid: str, l: dict) -> str:
    status = "🟢 فعال" if is_link_allowed(l) else "🔴 غیرفعال/منقضی"
    limit = "نامحدود" if not l.get("limit_bytes") else fmt_bytes(l["limit_bytes"])
    speed = "نامحدود" if not l.get("speed_limit_bytes") else f"{l['speed_limit_bytes']*8/1024/1024:.1f} Mbps"
    exp = l.get("expires_at")
    exp_txt = exp.split("T")[0] if exp else "بدون انقضا"
    proto = l.get("protocol", DEFAULT_PROTOCOL)
    alpn = l.get("alpn") or f"پیش‌فرض ({DEFAULT_ALPN_BY_PROTOCOL.get(proto, 'http/1.1')})"
    return (
        f"<b>{l.get('label','?')}</b>\n"
        f"وضعیت: {status}\n"
        f"مصرف: {fmt_bytes(l.get('used_bytes',0))} / {limit}\n"
        f"محدودیت سرعت: {speed}\n"
        f"محدودیت آی‌پی: {l.get('ip_limit',0) or 'نامحدود'}\n"
        f"پروتکل: {_protocol_label(proto)}\n"
        f"Fingerprint: {_fp_label(l.get('fingerprint', DEFAULT_FINGERPRINT))}\n"
        f"ALPN: {alpn}\n"
        f"پورت: {l.get('port', DEFAULT_PORT)}\n"
        f"انقضا: {exp_txt}\n"
        f"UUID: <code>{uid}</code>"
    )

# ── Sub-group (لینک ساب حرفه‌ای) view builders ────────────────────────────────
def _group_public_url(s: dict) -> str:
    host = get_host()
    return f"https://{host}/p/{s.get('uuid_key','')}"

def _subs_list_kb(page: int):
    items = sorted(SUBS.items(), key=lambda kv: kv[1].get("created_at", ""), reverse=True)
    total = len(items)
    start = page * PAGE_SIZE
    chunk = items[start:start + PAGE_SIZE]
    rows = []
    for sid, s in chunk:
        cnt = len(s.get("link_ids", []))
        rows.append([{"text": f"🗂 {s.get('name','?')[:26]} ({cnt})", "callback_data": f"subview:{sid}"}])
    nav = []
    if start > 0:
        nav.append({"text": "◀ قبلی", "callback_data": f"subs:{page-1}"})
    if start + PAGE_SIZE < total:
        nav.append({"text": "بعدی ▶", "callback_data": f"subs:{page+1}"})
    if nav:
        rows.append(nav)
    rows.append([{"text": "➕ ساخت گروه جدید", "callback_data": "newsub"}])
    rows.append([{"text": "⬅ منوی اصلی", "callback_data": "menu"}])
    return {"inline_keyboard": rows}

def _format_sub_detail(sid: str, s: dict) -> str:
    cnt = len(s.get("link_ids", []))
    pw = "🔒 دارد" if s.get("password_hash") else "بدون رمز"
    desc = s.get("desc") or "—"
    return (
        f"🗂 <b>{s.get('name','?')}</b>\n"
        f"توضیحات: {desc}\n"
        f"تعداد کانفیگ‌های داخل گروه: {cnt}\n"
        f"رمز عبور: {pw}\n\n"
        f"🔗 لینک ساب حرفه‌ای این گروه:\n<code>{_group_public_url(s)}</code>"
    )

def _sub_detail_kb(sid: str):
    return {"inline_keyboard": [
        [{"text": "➕ افزودن کانفیگ به این گروه", "callback_data": f"subaddlink:{sid}:0"}],
        [{"text": "🗑 حذف گروه", "callback_data": f"subdel:{sid}"}],
        [{"text": "⬅ بازگشت به لیست گروه‌ها", "callback_data": "subs:0"}],
    ]}

def _confirm_subdel_kb(sid: str):
    return {"inline_keyboard": [
        [{"text": "✅ بله، حذف کن", "callback_data": f"subdelok:{sid}"},
         {"text": "❌ انصراف", "callback_data": f"subview:{sid}"}],
    ]}

def _pick_link_for_group_kb(sid: str, page: int):
    """لیست همه‌ی کانفیگ‌ها برای انتخاب و افزودن به یک گروه ساب مشخص."""
    items = sorted(LINKS.items(), key=lambda kv: kv[1].get("created_at", ""), reverse=True)
    total = len(items)
    start = page * PAGE_SIZE
    chunk = items[start:start + PAGE_SIZE]
    rows = []
    for uid, l in chunk:
        in_this = "✅ " if l.get("sub_id") == sid else ""
        rows.append([{"text": f"{in_this}{l.get('label','?')[:28]}", "callback_data": f"subaddlinkdo:{uid}"}])
    nav = []
    if start > 0:
        nav.append({"text": "◀ قبلی", "callback_data": f"subaddlink:{sid}:{page-1}"})
    if start + PAGE_SIZE < total:
        nav.append({"text": "بعدی ▶", "callback_data": f"subaddlink:{sid}:{page+1}"})
    if nav:
        rows.append(nav)
    rows.append([{"text": "⬅ بازگشت به گروه", "callback_data": f"subview:{sid}"}])
    return {"inline_keyboard": rows}

# ── Per-config "group" (ساب لینک حرفه‌ای) view builders ───────────────────────
def _cfg_group_kb(uid: str):
    link = LINKS.get(uid, {})
    sid = link.get("sub_id")
    if sid and sid in SUBS:
        return {"inline_keyboard": [
            [{"text": "➖ خارج کردن از گروه", "callback_data": f"cfgungroup:{uid}"}],
            [{"text": "⬅ بازگشت", "callback_data": f"view:{uid}"}],
        ]}
    rows = []
    for sid2, s in sorted(SUBS.items(), key=lambda kv: kv[1].get("created_at", ""), reverse=True)[:8]:
        rows.append([{"text": f"➕ افزودن به «{s.get('name','?')[:24]}»", "callback_data": f"cfgaddgroup:{sid2}"}])
    rows.append([{"text": "🆕 ساخت گروه جدید و افزودن", "callback_data": f"cfgnewgroup:{uid}"}])
    rows.append([{"text": "⬅ بازگشت", "callback_data": f"view:{uid}"}])
    return {"inline_keyboard": rows}

def _format_cfg_group(uid: str) -> str:
    link = LINKS.get(uid, {})
    sid = link.get("sub_id")
    if sid and sid in SUBS:
        s = SUBS[sid]
        return (
            f"🗂 کانفیگ «{link.get('label','?')}» توی گروه «{s.get('name','?')}» هست.\n\n"
            f"🔗 لینک ساب حرفه‌ای این گروه:\n<code>{_group_public_url(s)}</code>"
        )
    return (
        f"کانفیگ «{link.get('label','?')}» توی هیچ گروهی نیست، یعنی فقط لینک ساب ساده داره.\n\n"
        "برای گرفتن لینک ساب حرفه‌ای (صفحه‌ی زیبا)، این کانفیگ رو به یک گروه اضافه کن یا یه گروه جدید بساز:"
    )

# ── Public/free + channel helpers ───────────────────────────────────────────
def _free_menu_kb():
    return {"inline_keyboard": [[{"text": "🎁 دریافت کانفیگ رایگان ۱ گیگ", "callback_data": "free:1gb"}]]}


def _channel_menu_kb():
    return {"inline_keyboard": [
        [{"text": "📤 ارسال کانفیگ با حجم دلخواه", "callback_data": "channel:post"}],
        [{"text": "⚙️ تنظیم کانال", "callback_data": "channel:set"}],
        [{"text": "⬅ منوی اصلی", "callback_data": "menu"}],
    ]}


def _channel_posted_text(label: str, vless: str, volume_gb: int, uid: str, host: str) -> str:
    sub_url = f"https://{host}/sub/{uid}"
    return (
        f"📡 <b>کانفیگ {volume_gb} گیگ</b>\n\n"
        f"🏷 {label}\n\n"
        f"🔗 <code>{vless}</code>\n\n"
        f"📥 لینک ساب: <code>{sub_url}</code>\n"
        f"🛠 پشتیبانی: @pixelgit"
    )


async def _send_link_to_channel(uid: str, volume_gb: int | None = None):
    channel = _channel_id()
    if not channel:
        return False, "کانال تنظیم نشده است. ابتدا /setchannel <channel_id> را اجرا کن."
    link = LINKS.get(uid)
    if not link:
        return False, "کانفیگ پیدا نشد."
    host = get_host()
    vless = vless_link_for_link(link, uid, host)
    shown_volume = volume_gb
    if shown_volume is None:
        limit = int(link.get("limit_bytes", 0) or 0)
        shown_volume = max(0, round(limit / (1024 ** 3))) if limit else 0
    res = await _send(channel, _channel_posted_text(link.get("label", "کانفیگ"), vless, shown_volume, uid, host))
    if not res or not res.get("ok"):
        return False, "ارسال به کانال انجام نشد؛ مطمئن شو ربات عضو کانال است و اجازه ارسال پیام دارد."
    return True, f"✅ کانفیگ «{link.get('label','?')}» در کانال ارسال شد."


async def _create_and_send_channel_config(volume_gb: int, admin_chat_id: int):
    label = f"کانفیگ {volume_gb}GB"
    uid, link = await make_link(
        label=label,
        limit_bytes=parse_size_to_bytes(volume_gb, "GB"),
        protocol=DEFAULT_PROTOCOL,
        fingerprint=DEFAULT_FINGERPRINT,
        alpn="",
        port=DEFAULT_PORT,
        ip_limit=0,
        speed_limit_bytes=0,
    )
    ok, msg = await _send_link_to_channel(uid, volume_gb)
    if ok:
        await _send(admin_chat_id, msg + f"\n\n🔗 لینک اتصال: <code>{vless_link_for_link(link, uid, get_host())}</code>")
    else:
        await _send(admin_chat_id, msg + f"\n\n⚠️ کانفیگ ساخته شد ولی ارسال نشد.\n🔗 <code>{vless_link_for_link(link, uid, get_host())}</code>")


async def _claim_free_config(chat_id: int, user_id: int | None = None):
    claim_id = int(user_id or chat_id)
    if _user_has_claimed_today(claim_id):
        await _send(chat_id, "⏳ سهمیه‌ی رایگان ۱ گیگ امروز را قبلاً دریافت کرده‌ای. فردا دوباره می‌توانی دریافت کنی.")
        return
    uid, link = await make_link(
        label=f"رایگان 1GB - {chat_id}",
        limit_bytes=FREE_VOLUME_BYTES,
        protocol=DEFAULT_PROTOCOL,
        fingerprint=DEFAULT_FINGERPRINT,
        alpn="",
        port=DEFAULT_PORT,
        ip_limit=0,
        speed_limit_bytes=0,
    )
    _mark_user_claimed_today(claim_id)
    host = get_host()
    vless = vless_link_for_link(link, uid, host)
    sub_url = f"https://{host}/sub/{uid}"
    await _send(
        chat_id,
        "🎁 <b>کانفیگ رایگان ۱ گیگ امروز</b>\n\n"
        f"🔗 <code>{vless}</code>\n\n"
        f"📥 لینک ساب: <code>{sub_url}</code>\n\n"
        "✅ سهمیه‌ی امروز مصرف شد؛ فردا دوباره ۱ گیگ می‌توانی دریافت کنی.\n"
        "🛠 پشتیبانی: @pixelgit",
    )


# ── Update handling ──────────────────────────────────────────────────────────
async def _handle_message(msg: dict):
    chat_id = msg.get("chat", {}).get("id")
    text = (msg.get("text") or "").strip()
    if chat_id is None:
        return
    is_admin = _is_admin(chat_id)
    user_id = msg.get("from", {}).get("id") or chat_id

    if text in ("/free", "/free1gb", "🎁 دریافت کانفیگ رایگان ۱ گیگ"):
        await _claim_free_config(chat_id, user_id)
        return

    if text in ("/start", "/menu") and not is_admin:
        _pending.pop(chat_id, None)
        await _send(chat_id, "👋 خوش اومدی!\nهر روز می‌تونی یک کانفیگ رایگان ۱ گیگ دریافت کنی.", _free_menu_kb())
        return

    if not is_admin:
        await _send(chat_id, "⛔ این بخش فقط برای مدیرهاست.\nبرای کانفیگ رایگان امروز روی دکمه‌ی زیر بزن.", _free_menu_kb())
        return

    if text in ("/start", "/menu"):
        _pending.pop(chat_id, None)
        await _send(chat_id, "👋 به ربات مدیریت X4G خوش اومدی.\nاز دکمه‌های زیر برای مدیریت کانفیگ‌ها استفاده کن:", _main_menu_kb())
        return

    # تنظیم کانال و ارسال کانفیگ ۱ تا ۱۰۰ گیگ؛ محدودیتی برای تعداد ارسال‌ها وجود ندارد.
    if text.startswith("/setchannel"):
        arg = text[len("/setchannel"):].strip()
        if not arg:
            await _send(chat_id, f"کانال فعلی: <code>{_channel_id() or 'تنظیم نشده'}</code>\n\nنمونه: <code>/setchannel -1001234567890</code>")
            return
        BOT_STATE["channel_id"] = arg
        _save_bot_state()
        await _send(chat_id, f"✅ کانال روی <code>{arg}</code> تنظیم شد.\nمطمئن شو ربات داخل کانال عضو و مجاز به ارسال پیام است.", _channel_menu_kb())
        return

    if text == "/channel":
        await _send(chat_id, f"📣 کانال فعلی: <code>{_channel_id() or 'تنظیم نشده'}</code>", _channel_menu_kb())
        return

    if text.startswith("/post"):
        raw = text[len("/post"):].strip().upper().replace("GB", "")
        try:
            volume_gb = int(raw)
        except ValueError:
            volume_gb = 0
        if not (1 <= volume_gb <= 100):
            await _send(chat_id, "❗️ حجم باید بین ۱ تا ۱۰۰ گیگ باشد.\nنمونه: <code>/post 10GB</code>")
            return
        await _create_and_send_channel_config(volume_gb, chat_id)
        return

    if text == "/cancel":
        _pending.pop(chat_id, None)
        await _send(chat_id, "لغو شد.", _main_menu_kb())
        return

    pending = _pending.get(chat_id)

    if pending and pending.get("action") == "setchannel" and text:
        BOT_STATE["channel_id"] = text.strip()
        _save_bot_state()
        _pending.pop(chat_id, None)
        await _send(chat_id, f"✅ کانال روی <code>{_channel_id()}</code> تنظیم شد.\nمطمئن شو ربات عضو کانال و مجاز به ارسال پیام است.", _channel_menu_kb())
        return

    if pending and pending.get("action") == "channel_post" and text:
        raw = text.upper().replace("GB", "").strip()
        try:
            volume_gb = int(raw)
        except ValueError:
            volume_gb = 0
        if not (1 <= volume_gb <= 100):
            await _send(chat_id, "❗️ حجم باید بین ۱ تا ۱۰۰ گیگ باشد:", _wizard_cancel_kb())
            return
        _pending.pop(chat_id, None)
        await _create_and_send_channel_config(volume_gb, chat_id)
        return

    if pending and pending.get("action") == "newsub" and pending.get("step") == "name" and text:
        name = text[:60]
        sid, s = await create_sub_group(name=name)
        link_uid = pending.get("link_uid")
        _pending.pop(chat_id, None)
        if link_uid and link_uid in LINKS:
            await set_link_sub(link_uid, sid)
            await _send(chat_id, f"✅ گروه ساخته شد و کانفیگ به اون اضافه شد.\n\n{_format_cfg_group(link_uid)}", _cfg_group_kb(link_uid))
        else:
            await _send(chat_id, f"✅ گروه ساخته شد.\n\n{_format_sub_detail(sid, s)}", _sub_detail_kb(sid))
        return

    if pending and pending.get("action") == "wizard" and text:
        step = pending["step"]
        data = pending["data"]

        if step == "label":
            data["label"] = text[:60] or "کانفیگ جدید"
            pending["step"] = "protocol"
            await _send(chat_id, _wizard_prompt("protocol", data), _wizard_protocol_kb())
            return

        if step in ("protocol", "fingerprint"):
            # این دو مرحله فقط با دکمه انتخاب می‌شن
            kb = _wizard_protocol_kb() if step == "protocol" else _wizard_fp_kb()
            await _send(chat_id, "لطفاً از دکمه‌های بالا یکی رو انتخاب کن 👆", kb)
            return

        if step == "alpn":
            data["alpn"] = text.strip()[:100]
            pending["step"] = "port"
            await _send(chat_id, _wizard_prompt("port", data), _wizard_skip_kb("port", f"⏭ پیش‌فرض ({DEFAULT_PORT})"))
            return

        if step == "port":
            try:
                p = int(text.strip())
            except ValueError:
                p = None
            if p is None or not (MIN_PORT <= p <= MAX_PORT):
                await _send(chat_id, f"❗️ عدد پورت نامعتبره. یه عدد بین {MIN_PORT} تا {MAX_PORT} بفرست:", _wizard_skip_kb("port", f"⏭ پیش‌فرض ({DEFAULT_PORT})"))
                return
            data["port"] = p
            pending["step"] = "volume"
            await _send(chat_id, _wizard_prompt("volume", data), _wizard_unlimited_kb("volume"))
            return

        if step == "volume":
            parsed = _parse_volume_text(text)
            if parsed is None:
                await _send(chat_id, "❗️ فرمت درست نیست. مثلاً بفرست: <code>10GB</code> یا <code>500MB</code>", _wizard_unlimited_kb("volume"))
                return
            data["limit_bytes"] = parsed
            pending["step"] = "speed"
            await _send(chat_id, _wizard_prompt("speed", data), _wizard_unlimited_kb("speed"))
            return

        if step == "speed":
            parsed = _parse_speed_text(text)
            if parsed is None:
                await _send(chat_id, "❗️ فرمت درست نیست. یه عدد بفرست، مثلاً <code>20</code> (Mbps)", _wizard_unlimited_kb("speed"))
                return
            data["speed_limit_bytes"] = parsed
            pending["step"] = "iplimit"
            await _send(chat_id, _wizard_prompt("iplimit", data), _wizard_unlimited_kb("iplimit"))
            return

        if step == "iplimit":
            n = _parse_nonneg_int(text)
            if n is None:
                await _send(chat_id, "❗️ یه عدد صحیح بفرست:", _wizard_unlimited_kb("iplimit"))
                return
            data["ip_limit"] = n
            pending["step"] = "days"
            await _send(chat_id, _wizard_prompt("days", data), _wizard_unlimited_kb("days"))
            return

        if step == "days":
            n = _parse_nonneg_int(text)
            if n is None:
                await _send(chat_id, "❗️ یه عدد صحیح بفرست (تعداد روز):", _wizard_unlimited_kb("days"))
                return
            data["expires_days"] = n
            pending["step"] = "confirm"
            await _send(chat_id, _wizard_summary(data), _wizard_confirm_kb())
            return

    # پیام ناشناخته → منو رو نشون بده
    await _send(chat_id, "از دکمه‌های زیر استفاده کن:", _main_menu_kb())

async def _handle_callback(cb: dict):
    chat_id = cb.get("message", {}).get("chat", {}).get("id")
    message_id = cb.get("message", {}).get("message_id")
    data = cb.get("data", "")
    cb_id = cb.get("id")

    if chat_id is None:
        await _answer_cb(cb_id, "⛔ درخواست نامعتبر")
        return
    user_id = cb.get("from", {}).get("id") or chat_id
    if data == "free:1gb" and not _is_admin(chat_id):
        await _answer_cb(cb_id)
        await _claim_free_config(chat_id, user_id)
        return
    if not _is_admin(chat_id):
        await _answer_cb(cb_id, "⛔ دسترسی نداری")
        return
    await _answer_cb(cb_id)

    if data == "menu":
        _pending.pop(chat_id, None)
        await _edit(chat_id, message_id, "منوی مدیریت X4G:", _main_menu_kb())
        return

    if data.startswith("list:"):
        page = int(data.split(":", 1)[1] or 0)
        if not LINKS:
            await _edit(chat_id, message_id, "هنوز هیچ کانفیگی ساخته نشده.", _main_menu_kb())
            return
        await _edit(chat_id, message_id, f"📋 لیست کانفیگ‌ها ({len(LINKS)} مورد):", _links_list_kb(page))
        return

    if data == "free:1gb":
        await _claim_free_config(chat_id, user_id)
        return

    if data == "channel:menu":
        await _edit(chat_id, message_id, f"📣 مدیریت ارسال به کانال\n\nکانال فعلی: <code>{_channel_id() or 'تنظیم نشده'}</code>", _channel_menu_kb())
        return

    if data == "channel:set":
        _pending[chat_id] = {"action": "setchannel"}
        await _edit(chat_id, message_id, "🆔 شناسه یا @username کانال را بفرست:", _wizard_cancel_kb())
        return

    if data == "channel:post":
        _pending[chat_id] = {"action": "channel_post"}
        await _edit(chat_id, message_id, "📦 حجم کانفیگ را بین ۱ تا ۱۰۰ گیگ بفرست.\nمثلاً <code>10GB</code>", _wizard_cancel_kb())
        return

    if data == "channel:test":
        channel = _channel_id()
        if not channel:
            await _answer_cb(cb_id, "ابتدا کانال را تنظیم کن.")
            return
        res = await _send(channel, "✅ تست ارسال ربات به کانال موفق بود.")
        await _send(chat_id, "✅ پیام تست ارسال شد." if res and res.get("ok") else "❌ ارسال تست ناموفق بود؛ دسترسی ربات به کانال را بررسی کن.")
        return

    # ── گروه‌های ساب (لینک حرفه‌ای) ────────────────────────────────────────────
    if data.startswith("subs:"):
        page = int(data.split(":", 1)[1] or 0)
        if not SUBS:
            await _edit(chat_id, message_id, "هنوز هیچ گروهی ساخته نشده.\n\nبرای گرفتن لینک ساب حرفه‌ای (صفحه‌ی زیبا)، اول یه گروه بساز و کانفیگ مورد نظرت رو داخلش بذار.", _subs_list_kb(0))
            return
        await _edit(chat_id, message_id, f"🗂 گروه‌های ساب ({len(SUBS)} مورد):", _subs_list_kb(page))
        return

    if data == "newsub":
        _pending[chat_id] = {"action": "newsub", "step": "name", "link_uid": None}
        await _edit(chat_id, message_id, "✏️ اسم گروه رو بفرست (این اسم فقط برای خودت توی مدیریت گروه‌هاست):", _wizard_cancel_kb())
        return

    if data.startswith("subview:"):
        sid = data.split(":", 1)[1]
        s = SUBS.get(sid)
        if not s:
            await _edit(chat_id, message_id, "این گروه دیگه وجود نداره.", _main_menu_kb())
            return
        await _edit(chat_id, message_id, _format_sub_detail(sid, s), _sub_detail_kb(sid))
        return

    if data.startswith("subaddlink:"):
        _, sid, page_s = data.split(":", 2)
        if sid not in SUBS:
            await _edit(chat_id, message_id, "این گروه دیگه وجود نداره.", _main_menu_kb())
            return
        if not LINKS:
            await _edit(chat_id, message_id, "هنوز هیچ کانفیگی نداری که به گروه اضافه کنی.", _sub_detail_kb(sid))
            return
        _pending[chat_id] = {"action": "subaddlink_ctx", "sid": sid}
        await _edit(chat_id, message_id, "کدوم کانفیگ رو به این گروه اضافه کنم؟\n(کانفیگ‌هایی که علامت ✅ دارن همین الان توی این گروهن)", _pick_link_for_group_kb(sid, int(page_s or 0)))
        return

    if data.startswith("subaddlinkdo:"):
        uid = data.split(":", 1)[1]
        ctx = _pending.get(chat_id) or {}
        sid = ctx.get("sid") if ctx.get("action") == "subaddlink_ctx" else None
        if not sid or sid not in SUBS:
            await _answer_cb(cb_id, "این عملیات منقضی شده، از منوی گروه‌ها دوباره امتحان کن.")
            return
        ok = await set_link_sub(uid, sid)
        if not ok:
            await _answer_cb(cb_id, "این کانفیگ دیگه وجود نداره")
            return
        _pending.pop(chat_id, None)
        s = SUBS.get(sid)
        await _edit(chat_id, message_id, f"✅ کانفیگ به گروه اضافه شد.\n\n{_format_sub_detail(sid, s)}", _sub_detail_kb(sid))
        return

    if data.startswith("subdel:"):
        sid = data.split(":", 1)[1]
        s = SUBS.get(sid)
        if not s:
            await _edit(chat_id, message_id, "این گروه دیگه وجود نداره.", _main_menu_kb())
            return
        await _edit(chat_id, message_id, f"❗️ از حذف گروه «{s.get('name')}» مطمئنی؟ لینک ساب حرفه‌ای‌اش دیگه کار نمی‌کنه (کانفیگ‌ها حذف نمی‌شن، فقط از گروه خارج می‌شن).", _confirm_subdel_kb(sid))
        return

    if data.startswith("subdelok:"):
        sid = data.split(":", 1)[1]
        name = await remove_sub_group(sid)
        if name is None:
            await _edit(chat_id, message_id, "این گروه قبلاً حذف شده بود.", _main_menu_kb())
        else:
            await _edit(chat_id, message_id, f"🗑 گروه «{name}» حذف شد.", _main_menu_kb())
        return

    # ── گروه یک کانفیگ خاص (از صفحه‌ی جزئیات کانفیگ) ───────────────────────────
    if data.startswith("cfggroup:"):
        uid = data.split(":", 1)[1]
        if uid not in LINKS:
            await _edit(chat_id, message_id, "این کانفیگ دیگه وجود نداره.", _main_menu_kb())
            return
        _pending[chat_id] = {"action": "cfg_group_ctx", "uid": uid}
        await _edit(chat_id, message_id, _format_cfg_group(uid), _cfg_group_kb(uid))
        return

    if data.startswith("cfgungroup:"):
        uid = data.split(":", 1)[1]
        await set_link_sub(uid, None)
        l = LINKS.get(uid)
        if not l:
            await _edit(chat_id, message_id, "این کانفیگ دیگه وجود نداره.", _main_menu_kb())
            return
        await _edit(chat_id, message_id, _format_detail(uid, l), _link_detail_kb(uid, l["active"]))
        return

    if data.startswith("cfgaddgroup:"):
        sid = data.split(":", 1)[1]
        ctx = _pending.get(chat_id) or {}
        uid = ctx.get("uid") if ctx.get("action") == "cfg_group_ctx" else None
        if not uid or uid not in LINKS:
            await _answer_cb(cb_id, "این عملیات منقضی شده، از روی کانفیگ دوباره وارد این بخش شو.")
            return
        ok = await set_link_sub(uid, sid)
        if not ok:
            await _answer_cb(cb_id, "این گروه دیگه وجود نداره")
            return
        _pending.pop(chat_id, None)
        await _edit(chat_id, message_id, f"✅ کانفیگ به گروه اضافه شد.\n\n{_format_cfg_group(uid)}", _cfg_group_kb(uid))
        return

    if data.startswith("cfgnewgroup:"):
        uid = data.split(":", 1)[1]
        if uid not in LINKS:
            await _edit(chat_id, message_id, "این کانفیگ دیگه وجود نداره.", _main_menu_kb())
            return
        _pending[chat_id] = {"action": "newsub", "step": "name", "link_uid": uid}
        await _edit(chat_id, message_id, "✏️ اسم گروه جدید رو بفرست؛ بعد از ساخته شدن، همین کانفیگ خودکار داخلش قرار می‌گیره:", _wizard_cancel_kb())
        return

    if data == "newcfg":
        _pending[chat_id] = {"action": "wizard", "step": "label", "data": {}}
        await _edit(chat_id, message_id, _wizard_prompt("label", {}), _wizard_cancel_kb())
        return

    if data == "w:cancel":
        _pending.pop(chat_id, None)
        await _edit(chat_id, message_id, "ساخت کانفیگ لغو شد.", _main_menu_kb())
        return

    if data.startswith("w:"):
        pending = _pending.get(chat_id)
        if not pending or pending.get("action") != "wizard":
            await _edit(chat_id, message_id, "این مرحله دیگه معتبر نیست، از منوی زیر دوباره شروع کن.", _main_menu_kb())
            return

        step = pending["step"]
        wdata = pending["data"]

        if data.startswith("w:proto:") and step == "protocol":
            proto = data.split(":", 2)[2]
            wdata["protocol"] = proto if proto in PROTOCOLS else DEFAULT_PROTOCOL
            pending["step"] = "fingerprint"
            await _edit(chat_id, message_id, _wizard_prompt("fingerprint", wdata), _wizard_fp_kb())
            return

        if data.startswith("w:fp:") and step == "fingerprint":
            fp = data.split(":", 2)[2]
            wdata["fingerprint"] = fp if fp in FINGERPRINTS else DEFAULT_FINGERPRINT
            pending["step"] = "alpn"
            await _edit(chat_id, message_id, _wizard_prompt("alpn", wdata), _wizard_alpn_kb())
            return

        if data.startswith("w:alpnpreset:") and step == "alpn":
            code = data.split(":", 2)[2]
            wdata["alpn"] = ALPN_PRESET_MAP.get(code, "")
            pending["step"] = "port"
            await _edit(chat_id, message_id, _wizard_prompt("port", wdata), _wizard_skip_kb("port", f"⏭ پیش‌فرض ({DEFAULT_PORT})"))
            return

        if data == "w:skip:alpn" and step == "alpn":
            wdata["alpn"] = ""
            pending["step"] = "port"
            await _edit(chat_id, message_id, _wizard_prompt("port", wdata), _wizard_skip_kb("port", f"⏭ پیش‌فرض ({DEFAULT_PORT})"))
            return

        if data == "w:skip:port" and step == "port":
            wdata["port"] = DEFAULT_PORT
            pending["step"] = "volume"
            await _edit(chat_id, message_id, _wizard_prompt("volume", wdata), _wizard_unlimited_kb("volume"))
            return

        if data == "w:skip:volume" and step == "volume":
            wdata["limit_bytes"] = 0
            pending["step"] = "speed"
            await _edit(chat_id, message_id, _wizard_prompt("speed", wdata), _wizard_unlimited_kb("speed"))
            return

        if data == "w:skip:speed" and step == "speed":
            wdata["speed_limit_bytes"] = 0
            pending["step"] = "iplimit"
            await _edit(chat_id, message_id, _wizard_prompt("iplimit", wdata), _wizard_unlimited_kb("iplimit"))
            return

        if data == "w:skip:iplimit" and step == "iplimit":
            wdata["ip_limit"] = 0
            pending["step"] = "days"
            await _edit(chat_id, message_id, _wizard_prompt("days", wdata), _wizard_unlimited_kb("days"))
            return

        if data == "w:skip:days" and step == "days":
            wdata["expires_days"] = 0
            pending["step"] = "confirm"
            await _edit(chat_id, message_id, _wizard_summary(wdata), _wizard_confirm_kb())
            return

        if data == "w:confirm" and step == "confirm":
            expires_days = wdata.get("expires_days", 0)
            expires_at = (datetime.now() + timedelta(days=expires_days)).isoformat() if expires_days > 0 else None
            uid, link = await make_link(
                label=wdata.get("label") or "کانفیگ جدید",
                limit_bytes=wdata.get("limit_bytes", 0),
                expires_at=expires_at,
                protocol=wdata.get("protocol", DEFAULT_PROTOCOL),
                fingerprint=wdata.get("fingerprint", DEFAULT_FINGERPRINT),
                alpn=wdata.get("alpn", ""),
                port=wdata.get("port", DEFAULT_PORT),
                ip_limit=wdata.get("ip_limit", 0),
                speed_limit_bytes=wdata.get("speed_limit_bytes", 0),
            )
            _pending.pop(chat_id, None)
            await _edit(chat_id, message_id, f"✅ کانفیگ ساخته شد.\n\n{_format_detail(uid, link)}", _link_detail_kb(uid, link["active"]))
            return

        # هیچ‌کدوم از حالت‌های بالا مچ نشد (مثلاً روی دکمه‌ی مرحله‌ی قبلی که دیگه معتبر نیست زده)
        await _answer_cb(cb_id, "این دکمه دیگه معتبر نیست.")
        return

    if data.startswith("view:"):
        uid = data.split(":", 1)[1]
        l = LINKS.get(uid)
        if not l:
            await _edit(chat_id, message_id, "این کانفیگ دیگه وجود نداره.", _main_menu_kb())
            return
        await _edit(chat_id, message_id, _format_detail(uid, l), _link_detail_kb(uid, l["active"]))
        return

    if data.startswith("toggle:"):
        uid = data.split(":", 1)[1]
        l = await set_link_active(uid, not LINKS.get(uid, {}).get("active", True))
        if not l:
            await _edit(chat_id, message_id, "این کانفیگ دیگه وجود نداره.", _main_menu_kb())
            return
        await _edit(chat_id, message_id, _format_detail(uid, l), _link_detail_kb(uid, l["active"]))
        return

    if data.startswith("link:"):
        uid = data.split(":", 1)[1]
        l = LINKS.get(uid)
        if not l:
            await _answer_cb(cb_id, "کانفیگ پیدا نشد")
            return
        host = get_host()
        vless = vless_link_for_link(l, uid, host)
        sub_url = f"https://{host}/sub/{uid}"
        msg = f"🔗 لینک اتصال «{l.get('label')}»:\n\n<code>{vless}</code>\n\nلینک ساب ساده (فقط متن کانفیگ):\n<code>{sub_url}</code>"
        sid = l.get("sub_id")
        if sid and sid in SUBS:
            msg += f"\n\n✨ لینک ساب حرفه‌ای گروه «{SUBS[sid].get('name','?')}»:\n<code>{_group_public_url(SUBS[sid])}</code>"
        else:
            msg += "\n\nℹ️ این کانفیگ توی هیچ گروهی نیست. برای گرفتن لینک ساب حرفه‌ای، از دکمه‌ی «🗂 گروه ساب» توی صفحه‌ی کانفیگ استفاده کن."
        await _send(chat_id, msg)
        return

    if data.startswith("del:"):
        uid = data.split(":", 1)[1]
        l = LINKS.get(uid)
        if not l:
            await _edit(chat_id, message_id, "این کانفیگ دیگه وجود نداره.", _main_menu_kb())
            return
        await _edit(chat_id, message_id, f"❗️ از حذف «{l.get('label')}» مطمئنی؟ این عمل برگشت‌ناپذیره.", _confirm_delete_kb(uid))
        return

    if data.startswith("delok:"):
        uid = data.split(":", 1)[1]
        label = await remove_link(uid)
        if label is None:
            await _edit(chat_id, message_id, "این کانفیگ قبلاً حذف شده بود.", _main_menu_kb())
        else:
            await _edit(chat_id, message_id, f"🗑 کانفیگ «{label}» حذف شد.", _main_menu_kb())
        return

# ── Polling loop ─────────────────────────────────────────────────────────────
async def _poll_loop():
    global _running
    offset = 0
    logger.info(f"🤖 Telegram bot polling started (admins: {len(ADMIN_IDS)})")
    while _running:
        try:
            res = await _call("getUpdates", offset=offset, timeout=30, allowed_updates=["message", "callback_query"])
            if not res or not res.get("ok"):
                await asyncio.sleep(3)
                continue
            for upd in res.get("result", []):
                offset = upd["update_id"] + 1
                try:
                    if "message" in upd:
                        await _handle_message(upd["message"])
                    elif "callback_query" in upd:
                        await _handle_callback(upd["callback_query"])
                except Exception as e:
                    logger.warning(f"Telegram update handling error: {e}")
        except asyncio.CancelledError:
            break
        except Exception as e:
            logger.warning(f"Telegram poll loop error: {e}")
            await asyncio.sleep(3)

# ── Lifecycle ────────────────────────────────────────────────────────────────
async def start_bot():
    global _client, _poll_task, _running
    _load_bot_state()
    if not BOT_TOKEN:
        logger.info("Telegram bot: TELEGRAM_BOT_TOKEN تنظیم نشده، ربات غیرفعاله.")
        return
    if not ADMIN_IDS:
        logger.warning("Telegram bot: TELEGRAM_ADMIN_IDS تنظیم نشده، هیچ‌کس اجازه‌ی مدیریت نداره (ربات روشنه ولی همه رد می‌شن).")
    _client = httpx.AsyncClient(timeout=httpx.Timeout(40.0, connect=10.0))
    _running = True
    _poll_task = asyncio.create_task(_poll_loop())

async def stop_bot():
    global _running, _client
    _running = False
    if _poll_task:
        _poll_task.cancel()
    if _client:
        await _client.aclose()
        _client = None
