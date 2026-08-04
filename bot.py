import asyncio
import html
import json
import logging
import os
import random
import re
import shutil
import struct
import threading
import time
import zlib
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from io import BytesIO

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, Update
from telegram.error import BadRequest, RetryAfter, TelegramError
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, MessageHandler, filters
from treys import Card, Evaluator

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger(__name__)

# ---------- 全局配置中心 ----------
STARTING_CHIPS = 20000
ENTERTAINMENT_CHIPS = 20000
MIN_ENTRY_CHIPS = 200
EMERGENCY_CHIPS = 2000
EMERGENCY_MAX_USES = 3

# 游戏时间配置 (秒)
TURN_TIMEOUT = 60          # 德州/21点单回合思考时间
AUTO_START_TIMEOUT = 30    # 21点/百家乐自动开牌/解散时间
RACE_AUTO_START = 120      # 赛马自动开赛时间
RACE_ANIMATION_INTERVAL = 1.5
SLOT_COOLDOWN = 3          # 老虎机冷却

# 游戏金额配置
SLOT_BET = 300             # 老虎机单次金额
BJ_MIN_BET = 100           # 21点最低打字下注
BACCARAT_FIXED_BET = 500   # 百家乐按钮单次下注
FIXED_MIN_RAISE = 100      # 德州最低加注额

# 其他配置
DEFAULT_ADMIN = 5431975432
ADMIN_USER_ID = int(os.environ.get("ADMIN_USER_ID", DEFAULT_ADMIN))
SMALL_BLIND, BIG_BLIND, ANTE = 0, 0, 200
STALE_TEXT_COMMAND_SECONDS = 120
DATA_FILE = os.environ.get("DATA_FILE", "bot_data.json")
# --------------------------------

# ---------- 赛马/德州常量 ----------
HORSE_COUNT = 4
HORSE_NAMES = ["金猪", "投喂", "柳一", "龟龟"]
HORSE_EMOJI = ["🐖", "🐩", "🦍", "🐢"]
FIXED_BET_AMOUNTS = [100, 200, 500, 1000]
RACE_UPDATE_INTERVAL = 5
RACE_TRACK_LENGTH = 14
DATA_BACKUP_FILE, DATA_TEMP_FILE = f"{DATA_FILE}.bak", f"{DATA_FILE}.tmp"
BEIJING_TZ = timezone(timedelta(hours=8))
HAND_NAME_CN = {"High Card":"高牌", "Pair":"一对", "One Pair":"一对", "Two Pair":"两对", "Three of a Kind":"三条", "Straight":"顺子", "Flush":"同花", "Full House":"葫芦", "Four of a Kind":"四条", "Straight Flush":"同花顺", "Royal Flush":"皇家同花顺"}
RANK_ICONS = ["🥇", "🥈", "🥉", "4️⃣", "5️⃣", "6️⃣", "7️⃣", "8️⃣", "9️⃣", "🔟"]


def rank_marker(index):
    return RANK_ICONS[index - 1] if 1 <= index <= len(RANK_ICONS) else f"🔸{index}"


# ---------- 数据 ----------
group_chips = defaultdict(lambda: defaultdict(lambda: STARTING_CHIPS))
entertainment_chips = defaultdict(lambda: defaultdict(lambda: ENTERTAINMENT_CHIPS))
AUTHORIZED_GROUPS = set()
race_history = defaultdict(list)
baccarat_history = defaultdict(list)
blackjack_history = defaultdict(list) # 新增 21点历史
race_daily_stats = defaultdict(lambda: [0] * HORSE_COUNT)
baccarat_daily_stats = defaultdict(lambda: {"player": 0, "banker": 0, "tie": 0})
# profit_by_date[业务日期][群ID][用户ID] = 德州 + 赛马合并盈亏（供 /cx 与每日综合榜使用）
profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
# 以下几份统计仅供各自游戏的局内“当日累计盈利榜”使用。
poker_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
race_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
blackjack_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
baccarat_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
slot_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
race_jackpot = defaultdict(int)
hourly_race_enabled = defaultdict(lambda: False)
daily_emergency_used = defaultdict(lambda: defaultdict(bool))
# 已实扣的游戏下注，用于全系游戏在重启时自动退款。
# 按游戏类型分条存储，避免多游戏并发时记录互相覆盖：
# pending_game_bets[群ID][用户ID]["21"/"baccarat"/"horse"] = {"amount": 100, "mode": "official"}
pending_game_bets = defaultdict(lambda: defaultdict(dict))
# 旧版赛马下注记录（仅兼容结算代码中的 pop 清理，实际退款以 pending_game_bets 为准）
pending_horse_bets = defaultdict(dict)
pending_horse_bet_modes = defaultdict(str)
last_business_date = ""
active_poker_games, active_horse_races, active_gomoku_games, active_minesweeper_games = {}, {}, {}, {}
active_blackjack_games, active_baccarat_games = {}, {}
# 用于老虎机等功能的冷却时间限制。
user_cooldowns = defaultdict(float)
# 高性能保存逻辑变量
data_dirty = False
save_event = None # 延迟初始化
data_save_lock = threading.Lock()
background_tasks = set()


def now_bj(): return datetime.now(BEIJING_TZ)

def race_id(ts): return datetime.fromtimestamp(ts, timezone.utc).astimezone(BEIJING_TZ).strftime("%Y%m%d-%H%M")
def business_date(now=None):
    now = now or now_bj()
    return (now + timedelta(days=1) if (now.hour, now.minute) >= (23, 50) else now).strftime("%Y-%m-%d")


def is_entertainment_time(now=None):
    now = now or now_bj()
    # 23:00:00 到 23:59:59 之间
    return now.hour == 23


def current_game_mode():
    """23:00-23:59 为娱乐模式，其余时间为正式积分模式。"""
    return "entertainment" if is_entertainment_time() else "official"


def restore_nested(target, source):

    for cid, users in source.items():
        for uid, value in users.items(): target[int(cid)][int(uid)] = int(value)


def save_data():
    """高性能脏标记保存：确保安全初始化。"""
    global data_dirty
    data_dirty = True
    # 彻底解决 save_event 未初始化导致的挂死问题
    try:
        if save_event is not None:
            save_event.set()
    except Exception:
        pass


def force_save_now():
    """强制立刻执行物理写盘，用于关机等场景。"""
    try:
        with data_save_lock:
            data = {
                "group_chips": {str(cid): dict(users) for cid, users in group_chips.items()},
                "entertainment_chips": {str(cid): dict(users) for cid, users in entertainment_chips.items()},
                "profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in profit_by_date.items()},
                "poker_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in poker_profit_by_date.items()},
                "race_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in race_profit_by_date.items()},
                "blackjack_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in blackjack_profit_by_date.items()},
                "baccarat_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in baccarat_profit_by_date.items()},
                "slot_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in slot_profit_by_date.items()},
                "authorized_groups": list(AUTHORIZED_GROUPS),
                "race_jackpot": {str(cid): value for cid, value in race_jackpot.items()},
                "hourly_race_enabled": {str(cid): value for cid, value in hourly_race_enabled.items()},
                "race_history": {str(cid): value[-10:] for cid, value in race_history.items()},
                "baccarat_history": {str(cid): value[-10:] for cid, value in baccarat_history.items()},
                "blackjack_history": {str(cid): value[-10:] for cid, value in blackjack_history.items()},
                "race_daily_stats": {str(cid): value for cid, value in race_daily_stats.items()},
                "baccarat_daily_stats": {str(cid): dict(value) for cid, value in baccarat_daily_stats.items()},
                "daily_emergency_used": {str(cid): {str(uid): used for uid, used in users.items()} for cid, users in daily_emergency_used.items()},
                "last_business_date": last_business_date,
                "pending_game_bets": {str(cid): {str(uid): val for uid, val in users.items()} for cid, users in pending_game_bets.items()},
                "user_cooldowns": {str(uid): ts for uid, ts in user_cooldowns.items()},
            }
            os.makedirs(os.path.dirname(os.path.abspath(DATA_FILE)), exist_ok=True)
            with open(DATA_TEMP_FILE, "w", encoding="utf-8") as file:
                json.dump(data, file, ensure_ascii=False, indent=2)
                file.flush(); os.fsync(file.fileno())
            if os.path.exists(DATA_FILE): shutil.copy2(DATA_FILE, DATA_BACKUP_FILE)
            os.replace(DATA_TEMP_FILE, DATA_FILE)
        return True
    except Exception:
        logger.exception("物理写盘失败")
        return False


async def data_save_worker():
    """后台高性能保存任务：每 5 秒合并保存一次。"""
    global data_dirty
    while True:
        await save_event.wait()
        save_event.clear()
        if data_dirty:
            # 在单独的线程中执行写盘，不阻塞主循环
            await asyncio.to_thread(force_save_now)
            data_dirty = False
        await asyncio.sleep(5)


def load_data():
    global last_business_date
    source = DATA_FILE if os.path.exists(DATA_FILE) else DATA_BACKUP_FILE
    if not os.path.exists(source): return
    try:
        with open(source, "r", encoding="utf-8") as file: data = json.load(file)
    except Exception:
        if source != DATA_FILE or not os.path.exists(DATA_BACKUP_FILE):
            logger.exception("数据读取失败"); return
        try:
            with open(DATA_BACKUP_FILE, "r", encoding="utf-8") as file: data = json.load(file)
            logger.warning("主数据文件损坏，已从备份恢复")
        except Exception:
            logger.exception("备份读取失败"); return
    try:
        restore_nested(group_chips, data.get("group_chips", {}))
        restore_nested(entertainment_chips, data.get("entertainment_chips", {}))
        for date, chats in data.get("profit_by_date", {}).items(): restore_nested(profit_by_date[date], chats)
        for date, chats in data.get("poker_profit_by_date", {}).items(): restore_nested(poker_profit_by_date[date], chats)
        for date, chats in data.get("race_profit_by_date", {}).items(): restore_nested(race_profit_by_date[date], chats)
        for date, chats in data.get("blackjack_profit_by_date", {}).items(): restore_nested(blackjack_profit_by_date[date], chats)
        for date, chats in data.get("baccarat_profit_by_date", {}).items(): restore_nested(baccarat_profit_by_date[date], chats)
        for date, chats in data.get("slot_profit_by_date", {}).items(): restore_nested(slot_profit_by_date[date], chats)
        AUTHORIZED_GROUPS.update(int(cid) for cid in data.get("authorized_groups", []))
        for cid, value in data.get("race_jackpot", {}).items(): race_jackpot[int(cid)] = int(value)
        for cid, value in data.get("hourly_race_enabled", {}).items(): hourly_race_enabled[int(cid)] = bool(value)
        for cid, value in data.get("race_history", {}).items(): race_history[int(cid)] = list(value)[-10:]
        for cid, value in data.get("race_daily_stats", {}).items(): race_daily_stats[int(cid)] = list(value)[:HORSE_COUNT]
        for cid, users in data.get("daily_emergency_used", {}).items():
            for uid, used in users.items(): daily_emergency_used[int(cid)][int(uid)] = min(int(used), EMERGENCY_MAX_USES)
        last_business_date = data.get("last_business_date", "")
        # 全系游戏退款恢复逻辑
        for cid, users in data.get("pending_game_bets", {}).items():
            for uid, info in users.items():
                # 兼容旧格式（单条记录）与新格式（按游戏类型分条）
                entries = [info] if "amount" in info else list(info.values())
                for ginfo in entries:
                    wallet = entertainment_chips if ginfo.get("mode") == "entertainment" else group_chips
                    wallet[int(cid)][int(uid)] += int(ginfo.get("amount", 0))
        # 老虎机冷却恢复
        for uid, ts in data.get("user_cooldowns", {}).items(): user_cooldowns[int(uid)] = float(ts)
        force_save_now()
    except Exception:
        logger.exception("恢复数据失败")


load_data()

# ---------- Telegram 工具 ----------
async def get_name(app, uid):
    try:
        chat = await app.bot.get_chat(uid)
        name = " ".join(part for part in (chat.first_name, chat.last_name) if part)
        raw_name = name or (f"@{chat.username}" if chat.username else f"玩家{uid}")
        # 安全转义：防止名字带 < > & 导致 HTML 消息发送失败
        return html.escape(raw_name)
    except TelegramError:
        return f"玩家{uid}"
    except Exception:
        logger.warning("获取玩家名称失败: %s", uid, exc_info=True)
        return f"玩家{uid}"


async def safe_send(bot, cid, text, **kwargs):
    for attempt in range(2):
        try: return await bot.send_message(chat_id=cid, text=text, **kwargs)
        except RetryAfter as exc:
            if attempt == 0: await asyncio.sleep(exc.retry_after); continue
        except TelegramError:
            logger.exception("发送消息失败: %s", cid); break
    return None


def split_telegram_text(text, max_bytes=4000):
    """按 UTF-8 字节切分，避免中文结算消息超过 Telegram 的 4096 字节限制。"""
    parts, remaining = [], text
    while len(remaining.encode("utf-8")) > max_bytes:
        size, cut = 0, 0
        for index, char in enumerate(remaining):
            char_size = len(char.encode("utf-8"))
            if size + char_size > max_bytes: break
            size += char_size; cut = index + 1
        newline = remaining.rfind("\n", 0, cut)
        cut = newline if newline > 0 else cut
        parts.append(remaining[:cut]); remaining = remaining[cut:].lstrip("\n")
    if remaining: parts.append(remaining)
    return parts


async def safe_send_long(bot, cid, text, **kwargs):
    last = None
    for index, part in enumerate(split_telegram_text(text)):
        last = await safe_send(bot, cid, part, **(kwargs if index == 0 else {}))
        if last is None:
            logger.error("长消息发送失败，群 %s，第 %s 段未送达", cid, index + 1)
            return None
    return last


async def safe_edit(bot, cid, msg_id, text, **kwargs):
    if not msg_id: return None
    try: return await bot.edit_message_text(chat_id=cid, message_id=msg_id, text=text, **kwargs)
    except BadRequest as exc:
        if "Message is not modified" not in str(exc): logger.warning("编辑消息失败: %s", exc)
    except RetryAfter as exc:
        await asyncio.sleep(exc.retry_after)
        return await safe_edit(bot, cid, msg_id, text, **kwargs)
    except TelegramError: logger.exception("编辑消息失败")
    return None


async def safe_edit_photo(bot, cid, msg_id, photo, caption, **kwargs):
    if not msg_id: return None
    try:
        return await bot.edit_message_media(
            chat_id=cid,
            message_id=msg_id,
            media=InputMediaPhoto(media=photo, caption=caption),
            **kwargs,
        )
    except BadRequest as exc:
        logger.warning("编辑五子棋图片失败: %s", exc)
    except RetryAfter as exc:
        await asyncio.sleep(exc.retry_after)
        return await safe_edit_photo(bot, cid, msg_id, photo, caption, **kwargs)
    except TelegramError:
        logger.exception("编辑五子棋图片失败")
    return None


async def safe_send_photo(bot, cid, photo, caption, **kwargs):
    for attempt in range(2):
        try: return await bot.send_photo(chat_id=cid, photo=photo, caption=caption, **kwargs)
        except RetryAfter as exc:
            if attempt == 0: await asyncio.sleep(exc.retry_after); continue
        except TelegramError:
            logger.exception("发送图片失败: %s", cid); break
    return None


async def update_gomoku_board(game, app, names, selecting_row=None, remove_keyboard=False, custom_caption=None):
    caption = custom_caption if custom_caption else game.caption(names, selecting_row)
    # 方案二：直接编辑文本消息，不再发送/删除图片
    return await safe_edit(
        app.bot,
        game.chat_id,
        game.game_msg_id,
        caption,
        reply_markup=None if remove_keyboard else game.buttons(selecting_row),
    )


async def safe_delete(bot, cid, msg_id):
    if msg_id:
        try: await bot.delete_message(chat_id=cid, message_id=msg_id)
        except TelegramError: pass


def card_str(card):
    raw = Card.int_to_pretty_str(card).strip("[]")
    suit = {"♠":"♠️", "♥":"♥️", "♦":"♦️", "♣":"♣️"}.get(raw[-1], raw[-1])
    return f"{suit}{raw[:-1].replace('T', '10')}"


async def action_notice(cid, app, uid, desc):
    message = await safe_send(app.bot, cid, f"🎲 {await get_name(app, uid)} {desc}")
    if message:
        async def delete_later():
            await asyncio.sleep(10); await safe_delete(app.bot, cid, message.message_id)
        asyncio.create_task(delete_later())


async def emergency_if_needed(cid, uid, app, poker=None):
    used = daily_emergency_used[cid][uid]
    if group_chips[cid][uid] != 0 or used >= EMERGENCY_MAX_USES: return False
    group_chips[cid][uid] = EMERGENCY_CHIPS
    if poker and uid in poker.chips: poker.chips[uid] += EMERGENCY_CHIPS
    daily_emergency_used[cid][uid] = used + 1; save_data()
    remaining = EMERGENCY_MAX_USES - daily_emergency_used[cid][uid]
    await safe_send(app.bot, cid, f"🆘 {await get_name(app, uid)} 筹码归零，已赠送 {EMERGENCY_CHIPS} 应急筹码（今日已补充 {daily_emergency_used[cid][uid]}/{EMERGENCY_MAX_USES} 次，剩余 {remaining} 次）。")
    return True


# ==================== 五子棋 ====================
def png_chunk(kind, data):
    return struct.pack(">I", len(data)) + kind + data + struct.pack(">I", zlib.crc32(kind + data) & 0xFFFFFFFF)


def gomoku_board_image(board):
    """仅用标准库绘制木色 11×11 棋盘 PNG，避免 emoji 棋盘在手机端变形。"""
    size, margin, grid = 11, 46, 48
    canvas = margin * 2 + grid * (size - 1)
    pixels = bytearray(canvas * canvas * 3)
    wood, line, black, white, shadow = (211, 165, 95), (78, 50, 25), (30, 30, 30), (244, 240, 228), (132, 96, 52)

    def set_pixel(x, y, color):
        if 0 <= x < canvas and 0 <= y < canvas:
            offset = (y * canvas + x) * 3
            pixels[offset:offset + 3] = bytes(color)

    # 木色底板与细微横向纹理。
    for y in range(canvas):
        grain = ((y * 17) % 11) - 5
        color = tuple(max(0, min(255, value + grain)) for value in wood)
        for x in range(canvas):
            set_pixel(x, y, color)
    # 网格线。
    for index in range(size):
        pos = margin + index * grid
        for delta in (-1, 0, 1):
            for xy in range(margin, canvas - margin + 1):
                set_pixel(pos + delta, xy, line)
                set_pixel(xy, pos + delta, line)
    # 用内置像素字绘制 1–11 坐标，不依赖字体文件或第三方图像库。
    digits = {
        "0": ("111", "101", "101", "101", "111"), "1": ("010", "110", "010", "010", "111"),
        "2": ("111", "001", "111", "100", "111"), "3": ("111", "001", "111", "001", "111"),
        "4": ("101", "101", "111", "001", "001"), "5": ("111", "100", "111", "001", "111"),
        "6": ("111", "100", "111", "101", "111"), "7": ("111", "001", "010", "010", "010"),
        "8": ("111", "101", "111", "101", "111"), "9": ("111", "101", "111", "001", "111"),
    }

    def draw_number(text, left, top, scale=2):
        for char_index, char in enumerate(text):
            for dy, pattern in enumerate(digits[char]):
                for dx, enabled in enumerate(pattern):
                    if enabled == "1":
                        for py in range(scale):
                            for px in range(scale):
                                set_pixel(left + char_index * 8 + dx * scale + px, top + dy * scale + py, line)

    for index in range(size):
        label = str(index + 1)
        draw_number(label, margin + index * grid - (3 if index < 9 else 7), 16)
        draw_number(label, 16 if index < 9 else 10, margin + index * grid - 5)
    # 五子棋星位。
    for row, col in ((3, 3), (3, 7), (5, 5), (7, 3), (7, 7)):
        cx, cy = margin + col * grid, margin + row * grid
        for y in range(cy - 4, cy + 5):
            for x in range(cx - 4, cx + 5):
                if (x - cx) ** 2 + (y - cy) ** 2 <= 16:
                    set_pixel(x, y, line)
    # 棋子以实心圆绘制，白棋保留深色边缘，不会和棋盘混淆。
    for row, values in enumerate(board):
        for col, stone in enumerate(values):
            if stone == GomokuGame.EMPTY:
                continue
            cx, cy = margin + col * grid, margin + row * grid
            radius = 19
            fill = black if stone == GomokuGame.BLACK else white
            for y in range(cy - radius - 2, cy + radius + 3):
                for x in range(cx - radius - 2, cx + radius + 3):
                    distance = (x - cx) ** 2 + (y - cy) ** 2
                    if distance <= (radius + 2) ** 2:
                        set_pixel(x, y, shadow)
                    if distance <= radius ** 2:
                        set_pixel(x, y, fill)
    raw = b"".join(b"\x00" + bytes(pixels[row * canvas * 3:(row + 1) * canvas * 3]) for row in range(canvas))
    image = b"\x89PNG\r\n\x1a\n" + png_chunk(b"IHDR", struct.pack(">IIBBBBB", canvas, canvas, 8, 2, 0, 0, 0)) + png_chunk(b"IDAT", zlib.compress(raw, 9)) + png_chunk(b"IEND", b"")
    data = BytesIO(image)
    data.name = "gomoku_board.png"
    return data


class GomokuGame:
    SIZE = 9
    EMPTY, BLACK, WHITE = "empty", "black", "white"

    def __init__(self, chat_id, owner_id):
        self.chat_id, self.owner_id = chat_id, owner_id
        self.players = []
        self.board = [[self.EMPTY for _ in range(self.SIZE)] for _ in range(self.SIZE)]
        self.turn = 0
        self.phase = "waiting"
        self.game_msg_id = None
        self.wait_task = None
        self.winner = None
        self.draw = False

    def add(self, uid):
        if self.phase != "waiting" or uid in self.players or len(self.players) >= 2:
            return False
        self.players.append(uid)
        if len(self.players) == 2:
            self.phase = "playing"
        return True

    def current_uid(self):
        return self.players[self.turn] if self.phase == "playing" and len(self.players) == 2 else None

    def place(self, uid, row, col):
        if self.phase != "playing":
            return False, "当前不是落子阶段"
        if uid != self.current_uid():
            return False, "还没轮到你"
        if not (0 <= row < self.SIZE and 0 <= col < self.SIZE):
            return False, "坐标越界"
        if self.board[row][col] != self.EMPTY:
            return False, "这个位置已经有棋子了"
        stone = self.BLACK if self.turn == 0 else self.WHITE
        self.board[row][col] = stone
        if self.has_five(row, col, stone):
            self.phase, self.winner = "finished", uid
            return True, "win"
        if all(cell != self.EMPTY for line in self.board for cell in line):
            self.phase, self.draw = "finished", True
            return True, "draw"
        self.turn = 1 - self.turn
        return True, "ok"

    def has_five(self, row, col, stone):
        for dr, dc in ((0, 1), (1, 0), (1, 1), (1, -1)):
            count = 1
            for direction in (1, -1):
                r, c = row + dr * direction, col + dc * direction
                while 0 <= r < self.SIZE and 0 <= c < self.SIZE and self.board[r][c] == stone:
                    count += 1; r += dr * direction; c += dc * direction
            if count >= 5:
                return True
        return False

    def caption(self, names=None, selecting_row=None):
        names = names or {}
        header = ["🎯 9×9 五子棋", "⚫ 黑：" + (names.get(self.players[0], str(self.players[0])) if self.players else "等待玩家")]
        if len(self.players) > 1:
            header.append("⚪ 白：" + names.get(self.players[1], str(self.players[1])))
        if self.phase == "waiting":
            header.append("\n等待第二位玩家点击加入。发起人可用 /end 取消。")
        elif self.phase == "playing":
            current = names.get(self.current_uid(), str(self.current_uid()))
            header.append(f"\n当前回合：{current}\n直接点击格子落子｜/end 终止")
        elif self.draw:
            header.append("\n本局和棋")
        else:
            header.append(f"\n胜者：{names.get(self.winner, str(self.winner))}")
        return "\n".join(header)

    def buttons(self, selecting_row=None):
        if self.phase == "waiting":
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("➕ 加入五子棋", callback_data="gomoku_join")],
                [InlineKeyboardButton("🛑 终止本局", callback_data="gomoku_end")],
            ])
        if self.phase != "playing":
            return None
        
        kb = []
        for r in range(self.SIZE):
            row_btns = []
            for c in range(self.SIZE):
                stone = self.board[r][c]
                # 使用最窄的字符来尝试缩减按钮宽度
                label = "●" if stone == self.BLACK else "○" if stone == self.WHITE else "."
                row_btns.append(InlineKeyboardButton(label, callback_data=f"gomoku_place_{r}_{c}"))
            kb.append(row_btns)
        kb.append([InlineKeyboardButton("🛑 终止本局", callback_data="gomoku_end")])
        return InlineKeyboardMarkup(kb)


class MinesweeperGame:
    WIDTH, HEIGHT = 8, 8  # 8x8 适配手机屏幕
    MINE_COUNT = 10

    def __init__(self, chat_id, owner_id):
        self.chat_id, self.owner_id = chat_id, owner_id
        self.players = []
        self.board = [[0 for _ in range(self.WIDTH)] for _ in range(self.HEIGHT)]
        self.mines = set()
        self.revealed = [[False for _ in range(self.WIDTH)] for _ in range(self.HEIGHT)]
        self.phase = "waiting" # waiting, playing, finished
        self.game_msg_id = None
        self.first_click = True
        self.loser = None

    def add(self, uid):
        if self.phase != "waiting" or uid in self.players:
            return False
        self.players.append(uid)
        return True

    def start(self):
        if len(self.players) < 1: return False
        self.phase = "playing"
        return True

    def _place_mines(self, safe_r, safe_c):
        """第一下必不踩雷，且周围 3x3 尽量不埋雷以优化开局体验。"""
        candidates = [(r, c) for r in range(self.HEIGHT) for c in range(self.WIDTH) 
                      if abs(r - safe_r) > 1 or abs(c - safe_c) > 1]
        self.mines = set(random.sample(candidates, self.MINE_COUNT))
        for r, c in self.mines:
            self.board[r][c] = -1 # -1 代表雷
        
        # 计算周边数字
        for r in range(self.HEIGHT):
            for c in range(self.WIDTH):
                if self.board[r][c] == -1: continue
                count = 0
                for dr in (-1, 0, 1):
                    for dc in (-1, 0, 1):
                        nr, nc = r + dr, c + dc
                        if 0 <= nr < self.HEIGHT and 0 <= nc < self.WIDTH and self.board[nr][nc] == -1:
                            count += 1
                self.board[r][c] = count

    def reveal(self, uid, r, c):
        if self.phase != "playing" or self.revealed[r][c]:
            return False, "invalid"
        
        if self.first_click:
            self._place_mines(r, c)
            self.first_click = False
        
        self.revealed[r][c] = True
        
        if self.board[r][c] == -1:
            self.phase = "finished"
            self.loser = uid
            return True, "mine"
        
        # 如果是 0，递归自动翻开周围
        if self.board[r][c] == 0:
            self._auto_reveal(r, c)
            
        # 检查是否清空所有非雷格
        safe_count = sum(not val for row in self.revealed for val in row)
        if safe_count == self.MINE_COUNT:
            self.phase = "finished"
            return True, "win"
            
        return True, "ok"

    def _auto_reveal(self, r, c):
        for dr in (-1, 0, 1):
            for dc in (-1, 0, 1):
                nr, nc = r + dr, c + dc
                if 0 <= nr < self.HEIGHT and 0 <= nc < self.WIDTH and not self.revealed[nr][nc]:
                    self.revealed[nr][nc] = True
                    if self.board[nr][nc] == 0:
                        self._auto_reveal(nr, nc)

    def caption(self, names=None):
        names = names or {}
        header = [f"💣 扫雷大作战 ({self.WIDTH}x{self.HEIGHT})"]
        if self.phase == "waiting":
            header.append(f"\n🎮 纯娱乐模式（无筹码）\n等待加入... (当前 {len(self.players)} 人)\n发起人点击开始。")
        elif self.phase == "playing":
            header.append("\n游戏进行中！大家轮流点，踩雷即炸！")
        elif self.loser:
            header.append(f"\n💥 轰！{names.get(self.loser, '玩家')} 踩到了雷！游戏结束。")
        else:
            header.append("\n🎉 奇迹！所有安全区已清空，扫雷成功！")
        return "\n".join(header)

    def buttons(self):
        if self.phase == "waiting":
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("➕ 加入游戏", callback_data="mine_join")],
                [InlineKeyboardButton("🎮 开始游戏", callback_data="mine_start")],
                [InlineKeyboardButton("🛑 终止", callback_data="mine_end")]
            ])
        
        kb = []
        for r in range(self.HEIGHT):
            row_btns = []
            for c in range(self.WIDTH):
                if not self.revealed[r][c] and self.phase == "playing":
                    label = "·"
                    row_btns.append(InlineKeyboardButton(label, callback_data=f"mine_rev_{r}_{c}"))
                else:
                    val = self.board[r][c]
                    if val == -1: label = "💣"
                    elif val == 0: label = " "
                    else: label = str(val)
                    row_btns.append(InlineKeyboardButton(label, callback_data="mine_noop"))
            kb.append(row_btns)
        
        if self.phase == "playing":
            kb.append([InlineKeyboardButton("🛑 终止游戏", callback_data="mine_end")])
        else:
            kb.append([InlineKeyboardButton("♻️ 重新开始", callback_data="mine_rematch")])
            
        return InlineKeyboardMarkup(kb)


class BlackjackGame:
    def __init__(self, cid, owner, mode="official"):
        self.chat_id, self.owner_id, self.mode = cid, owner, mode
        self.phase = "waiting" # waiting, playing, dealer_turn, finished
        self.players = [] # uid list
        self.bets = {} # uid -> amount
        self.hands = defaultdict(list) # uid -> cards
        self.dealer_hand = []
        self.deck = []
        self.current_player_idx = 0
        self.game_msg_id = None
        self.action_msg_id = None # 用于置底的动态按钮消息 ID
        self.name_cache = {}
        self.timer_task = None
        self.wait_task = None # 新增等待解散任务变量

    def cancel_timer(self):
        if self.timer_task and not self.timer_task.done():
            self.timer_task.cancel()
            
    def cancel_wait(self):
        if self.wait_task and not self.wait_task.done():
            self.wait_task.cancel()

    def add_player(self, uid, bet):
        if self.phase != "waiting" or uid in self.players: return False
        self.players.append(uid)
        self.bets[uid] = bet
        
        # 记录退款保护
        pending_game_bets[self.chat_id][uid]["21"] = {"amount": bet, "mode": self.mode}
        return True

    def start(self):
        if not self.players: return False
        self.phase = "playing"
        self.deck = [r + s for r in "23456789TJQKA" for s in "shdc"]
        random.shuffle(self.deck)
        # 发初始牌
        for _ in range(2):
            for p in self.players: self.hands[p].append(self.deck.pop())
            self.dealer_hand.append(self.deck.pop())
        return True

    def get_score(self, cards):
        score, aces = 0, 0
        val_map = {**{str(i): i for i in range(2, 10)}, "T": 10, "J": 10, "Q": 10, "K": 10, "A": 11}
        for c in cards:
            score += val_map[c[0]]
            if c[0] == "A": aces += 1
        while score > 21 and aces:
            score -= 10; aces -= 1
        return score

    def is_blackjack(self, cards):
        return len(cards) == 2 and self.get_score(cards) == 21

    def hit(self, uid):
        if self.phase != "playing" or self.players[self.current_player_idx] != uid: return None
        card = self.deck.pop()
        self.hands[uid].append(card)
        score = self.get_score(self.hands[uid])
        if score >= 21: self.next_player()
        return card

    def double_down(self, uid):
        if self.phase != "playing" or self.players[self.current_player_idx] != uid: return False
        # 翻倍：再扣一份钱
        bet = self.bets[uid]
        self.bets[uid] += bet
        
        # 记录退款保护 (更新)
        pending_game_bets[self.chat_id][uid]["21"] = {"amount": self.bets[uid], "mode": self.mode}
        
        # 强制摸一张
        self.hands[uid].append(self.deck.pop())
        # 强制停牌
        self.next_player()
        return True

    def next_player(self):
        self.current_player_idx += 1
        if self.current_player_idx >= len(self.players):
            self.phase = "dealer_turn"

    def dealer_play(self):
        while self.get_score(self.dealer_hand) < 17:
            self.dealer_hand.append(self.deck.pop())
        self.phase = "finished"

    def get_card_str(self, cards, hide_first=False):
        res = []
        for i, c in enumerate(cards):
            if i == 0 and hide_first: res.append("❓")
            else:
                raw = c.replace("T", "10")
                suit = {"s":"♠️", "h":"♥️", "d":"♦️", "c":"♣️"}.get(raw[1], raw[1])
                res.append(f"{suit}{raw[0]}")
        return " ".join(res)


class BaccaratGame:
    def __init__(self, cid, owner, mode="official"):
        self.chat_id, self.owner_id, self.mode = cid, owner, mode
        self.phase = "betting" # betting, finished
        self.bets = defaultdict(lambda: {"player": 0, "banker": 0, "tie": 0})
        self.game_msg_id = None
        self.create_time = time.time()
        self.timer_task = None

    def cancel_timer(self):
        if self.timer_task and not self.timer_task.done():
            self.timer_task.cancel()

    def place_bet(self, uid, side, amount):
        if self.phase != "betting": return False
        self.bets[uid][side] += amount
        
        # 记录退款保护 (累加)
        curr = pending_game_bets[self.chat_id][uid].get("baccarat", {}).get("amount", 0)
        pending_game_bets[self.chat_id][uid]["baccarat"] = {"amount": curr + amount, "mode": self.mode}
        return True

    def draw_card(self, deck):
        c = deck.pop()
        val = 0
        if c[0] in "TJQK": val = 0
        elif c[0] == "A": val = 1
        else: val = int(c[0])
        return c, val

    def play(self):
        deck = [r + s for r in "23456789TJQKA" for s in "shdc"]
        random.shuffle(deck)
        
        p_cards, b_cards = [], []
        p_val, b_val = 0, 0
        
        # 初始两张
        for _ in range(2):
            c, v = self.draw_card(deck); p_cards.append(c); p_val = (p_val + v) % 10
            c, v = self.draw_card(deck); b_cards.append(c); b_val = (b_val + v) % 10
            
        # 补牌规则 (Natural)
        if p_val < 8 and b_val < 8:
            # 闲家补牌
            p_third_val = -1
            if p_val <= 5:
                c, v = self.draw_card(deck); p_cards.append(c); p_val = (p_val + v) % 10
                p_third_val = v
            
            # 庄家补牌
            draw_b = False
            if p_third_val == -1: # 闲家没补
                if b_val <= 5: draw_b = True
            else: # 闲家补了第三张
                if b_val <= 2: draw_b = True
                elif b_val == 3 and p_third_val != 8: draw_b = True
                elif b_val == 4 and p_third_val in [2,3,4,5,6,7]: draw_b = True
                elif b_val == 5 and p_third_val in [4,5,6,7]: draw_b = True
                elif b_val == 6 and p_third_val in [6,7]: draw_b = True
            
            if draw_b:
                c, v = self.draw_card(deck); b_cards.append(c); b_val = (b_val + v) % 10
        
        self.phase = "finished"
        result = "tie" if p_val == b_val else ("player" if p_val > b_val else "banker")
        return p_cards, b_cards, p_val, b_val, result

    def card_to_str(self, cards):
        res = []
        for c in cards:
            raw = c.replace("T", "10")
            suit = {"s":"♠️", "h":"♥️", "d":"♦️", "c":"♣️"}.get(raw[1], raw[1])
            res.append(f"{suit}{raw[0]}")
        return " ".join(res)


# ==================== 德州扑克 ====================
def side_pots(total_bets):
    # 必须按投入金额升序构造主池和边池；按用户 ID 排序会跳过部分底池。
    ordered = sorted(
        ((uid, value) for uid, value in total_bets.items() if value > 0),
        key=lambda item: item[1],
    )
    result, previous = [], 0
    for _, level in ordered:
        if level <= previous: continue
        contributors = [uid for uid, amount in ordered if amount >= level]
        result.append(((level - previous) * len(contributors), contributors)); previous = level
    return result


def distribute_side_pots(total_bets, scores):
    payouts = defaultdict(lambda: {"amount": 0, "details": []})
    total_pot = sum(total_bets.values())
    for index, (amount, contributors) in enumerate(side_pots(total_bets)):
        eligible = {uid: scores[uid] for uid in contributors if uid in scores}
        if not eligible: continue
        best = min(eligible.values()); winners = sorted(uid for uid, score in eligible.items() if score == best)
        share, remainder = divmod(amount, len(winners))
        for position, uid in enumerate(winners):
            won = share + (1 if position < remainder else 0)
            payouts[uid]["amount"] += won
            payouts[uid]["details"].append(("主池" if index == 0 else f"边池{index}", won))
    # 守恒兜底：任何因异常边池资格导致的剩余底池，归入当前最佳存活玩家，禁止筹码凭空消失。
    allocated = sum(item["amount"] for item in payouts.values())
    unallocated = total_pot - allocated
    if unallocated > 0 and scores:
        best_score = min(scores.values())
        winners = sorted(uid for uid, score in scores.items() if score == best_score)
        share, remainder = divmod(unallocated, len(winners))
        for position, uid in enumerate(winners):
            won = share + (1 if position < remainder else 0)
            payouts[uid]["amount"] += won
            payouts[uid]["details"].append(("底池兜底", won))
    return payouts


class PokerGame:
    def __init__(self, cid, owner, mode=None):
        self.chat_id, self.owner_id, self.mode, self.phase = cid, owner, mode or current_game_mode(), "waiting"
        self.players, self.chips, self.initial_chips = [], {}, {}
        self.total_bet, self.round_bets, self.hands = {}, {}, {}
        self.folded, self.all_in, self.acted = set(), set(), set()
        # 短全下抬高下注额时，已行动者必须补齐或弃牌，但不能再次加注。
        self.raise_locked = set()
        self.board, self.deck, self.active = [], [], []
        self.pot = self.current_bet = self.actor_idx = self.dealer_idx = 0
        self.game_msg_id = self.action_msg_id = None
        self.turn_task = self.auto_task = self.wait_task = None
        self.evaluator, self.settled, self.showdown_order = Evaluator(), False, []

    def add(self, uid):
        if self.phase != "waiting" or uid in self.players: return False
        wallet = entertainment_chips if self.mode == "entertainment" else group_chips
        if wallet[self.chat_id][uid] < MIN_ENTRY_CHIPS: return False
        self.players.append(uid); self.chips[uid] = wallet[self.chat_id][uid]; self.total_bet[uid] = 0
        return True

    def start(self):
        if len(self.players) < 2: return False
        random.shuffle(self.players)
        self.cancel_auto(); self.cancel_wait(); self.folded.clear(); self.all_in.clear(); self.acted.clear(); self.raise_locked.clear(); self.board = []; self.pot = 0; self.settled = False
        wallet = entertainment_chips if self.mode == "entertainment" else group_chips
        for uid in self.players:
            self.chips[uid] = wallet[self.chat_id][uid]; self.initial_chips[uid] = self.chips[uid]
            self.total_bet[uid] = self.round_bets[uid] = 0
            ante = min(ANTE, self.chips[uid]); self.chips[uid] -= ante; self.total_bet[uid] += ante; self.pot += ante
            if not self.chips[uid]: self.all_in.add(uid)
        self.deck = [Card.new(rank + suit) for rank in "23456789TJQKA" for suit in "shdc"]
        random.shuffle(self.deck); self.hands = {uid: [self.deck.pop(), self.deck.pop()] for uid in self.players}
        self.dealer_idx = len(self.players) - 1; self.active = self.players.copy()
        self._blind(self.players[(self.dealer_idx + 1) % len(self.players)], SMALL_BLIND)
        bb = (self.dealer_idx + 2) % len(self.players); self._blind(self.players[bb], BIG_BLIND)
        self.current_bet, self.phase, self.actor_idx = max(self.round_bets.values()), "preflop", (bb + 1) % len(self.active)
        if self._next(self.actor_idx) is None: self.phase = "showdown"
        return True

    def _blind(self, uid, value):
        paid = min(value, self.chips[uid])
        self.chips[uid] -= paid; self.round_bets[uid] += paid; self.total_bet[uid] += paid; self.pot += paid
        if not self.chips[uid]: self.all_in.add(uid)

    def current(self):
        if not self.active or self.actor_idx >= len(self.active): return None
        uid = self.active[self.actor_idx]
        return uid if uid not in self.folded and uid not in self.all_in and uid not in self.acted else None

    def _next(self, start):
        for offset in range(len(self.active)):
            idx = (start + offset) % len(self.active); uid = self.active[idx]
            if uid not in self.folded and uid not in self.all_in and uid not in self.acted:
                self.actor_idx = idx; return uid
        return None

    def _round_done(self): return all(uid in self.folded or uid in self.all_in or uid in self.acted for uid in self.active)

    def action(self, uid, kind, extra=0):
        if uid != self.current(): return False, "还没轮到你"
        if kind == "fold":
            old = self.active.index(uid); self.folded.add(uid); self.active.remove(uid)
            if self.active: self.actor_idx = (old - 1) % len(self.active)
            desc = "弃牌"
        elif kind == "check":
            if self.round_bets[uid] != self.current_bet: return False, "必须跟注或加注"
            self.acted.add(uid); desc = "过牌"
        elif kind == "call":
            paid = min(self.current_bet - self.round_bets[uid], self.chips[uid])
            self.chips[uid] -= paid; self.round_bets[uid] += paid; self.total_bet[uid] += paid; self.pot += paid
            if not self.chips[uid]: self.all_in.add(uid)
            self.acted.add(uid); desc = f"跟注 {paid}"
        elif kind == "allin":
            paid, old_bet = self.chips[uid], self.current_bet; new_total = self.round_bets[uid] + paid
            self.chips[uid] = 0; self.round_bets[uid] = new_total; self.total_bet[uid] += paid; self.pot += paid; self.all_in.add(uid)
            if new_total > old_bet:
                raise_size = new_total - old_bet
                prior_actors = self.acted.copy()
                self.current_bet = new_total
                # 任意抬高下注额的全下都要求其余玩家重新响应。
                self.acted = {uid}
                if raise_size < FIXED_MIN_RAISE:
                    # 短全下不重新开放加注：之前已经行动的玩家只能跟注或弃牌。
                    self.raise_locked.update(prior_actors - {uid})
                else:
                    self.raise_locked.clear()
            else: self.acted.add(uid)
            desc = f"全下 {paid}"
        elif kind == "raise":
            try: extra = int(extra)
            except (TypeError, ValueError): return False, "无效加注额"
            to_call = self.current_bet - self.round_bets[uid]; paid = to_call + extra; new_total = self.round_bets[uid] + paid
            if extra < FIXED_MIN_RAISE: return False, f"最低加注为 {FIXED_MIN_RAISE}"
            if paid > self.chips[uid]: return False, f"筹码不足：本次需要跟注 {to_call} + 加注 {extra}，共 {paid}，你只有 {self.chips[uid]}"
            if new_total <= self.current_bet: return False, "加注后总下注必须高于当前下注"
            if uid in self.raise_locked: return False, "短全下后已行动玩家只能跟注或弃牌"
            self.chips[uid] -= paid; self.round_bets[uid] = new_total; self.total_bet[uid] += paid; self.pot += paid; self.current_bet = new_total; self.acted = {uid}; self.raise_locked.clear()
            if not self.chips[uid]: self.all_in.add(uid)
            desc = f"加注 {extra}"
        else: return False, "未知操作"
        alive = [p for p in self.active if p not in self.folded]
        if len(alive) <= 1 or all(p in self.all_in for p in alive): self.phase = "showdown"
        elif self._round_done(): self._end_round()
        else: self._next(self.actor_idx + 1)
        return True, desc

    def _end_round(self):
        self.round_bets = {uid: 0 for uid in self.players}; self.current_bet = 0; self.acted.clear(); self.raise_locked.clear()
        if self.phase == "preflop": self.deck.pop(); self.board.extend([self.deck.pop() for _ in range(3)]); self.phase = "flop"
        elif self.phase == "flop": self.deck.pop(); self.board.append(self.deck.pop()); self.phase = "turn"
        elif self.phase == "turn": self.deck.pop(); self.board.append(self.deck.pop()); self.phase = "river"
        else: self.phase = "showdown"; return
        if self._next((self.dealer_idx + 1) % len(self.players)) is None: self.phase = "showdown"

    def showdown(self):
        alive = [uid for uid in self.players if uid not in self.folded]
        self.showdown_order = alive.copy()

        # 只剩一名未弃牌玩家：直接获得底池。
        # 不继续发公牌，也不进入摊牌亮牌。
        if len(alive) == 1:
            winner = alive[0]
            self.chips[winner] += self.pot
            wallet = entertainment_chips if self.mode == "entertainment" else group_chips
            for uid in self.players:
                wallet[self.chat_id][uid] = self.chips[uid]
            save_data()
            return [(winner, "最后赢家", self.pot, [("全部底池", self.pot)], {})]

        # 至少两人仍在局内，才补齐五张公牌并进行正常摊牌。
        while len(self.board) < 5:
            self.deck.pop()
            if not self.board:
                self.board.extend([self.deck.pop() for _ in range(3)])
            else:
                self.board.append(self.deck.pop())
        scores = {uid: self.evaluator.evaluate(self.hands[uid], self.board) for uid in alive}
        names = {uid: HAND_NAME_CN.get(self.evaluator.class_to_string(self.evaluator.get_rank_class(score)), "未知") for uid, score in scores.items()}
        payouts = distribute_side_pots(self.total_bet, scores)
        for uid, item in payouts.items(): self.chips[uid] += item["amount"]
        wallet = entertainment_chips if self.mode == "entertainment" else group_chips
        for uid in self.players: wallet[self.chat_id][uid] = self.chips[uid]
        save_data(); return [(uid, names[uid], item["amount"], item["details"], names) for uid, item in payouts.items()]

    def cancel_timer(self):
        task, self.turn_task = self.turn_task, None
        if task and task is not asyncio.current_task() and not task.done(): task.cancel()

    def cancel_auto(self):
        task, self.auto_task = self.auto_task, None
        if task and task is not asyncio.current_task() and not task.done(): task.cancel()

    def cancel_wait(self):
        task, self.wait_task = self.wait_task, None
        if task and task is not asyncio.current_task() and not task.done(): task.cancel()


# ---------- 德州界面 / 流程 ----------
async def poker_waiting_text(game, app):
    players = [f"{i}. {await get_name(app, uid)}" for i, uid in enumerate(game.players, 1)]
    return f"🃏 新一局积分德州扑克\n发起人：{await get_name(app, game.owner_id)}\n\n已加入：\n" + "\n".join(players) + "\n\n点击加入，发起人可开始。"


async def update_poker_waiting(game, app):
    rows = [[InlineKeyboardButton("加入游戏", callback_data="texas_join")]]
    if len(game.players) >= 2: rows.append([InlineKeyboardButton("开始游戏", callback_data="texas_start")])
    rows.append([InlineKeyboardButton("🛑 终止房间", callback_data="texas_end")])
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await poker_waiting_text(game, app), reply_markup=InlineKeyboardMarkup(rows))


async def poker_table_text(game, app):
    phase = {"preflop":"翻牌前", "flop":"翻牌圈", "turn":"转牌圈", "river":"河牌圈"}.get(game.phase, game.phase)
    lines = [
        f"🃏 积分德州｜{phase}",
        "",
        "━━━━━━━━━━━━━━━━━",
        f"🃏 公牌：{'  '.join(card_str(card) for card in game.board) or '未发牌'}",
        "",
        f"💰 奖池：{game.pot}｜当前下注：{game.current_bet}",
        "━━━━━━━━━━━━━━━━━",
    ]
    current = game.current()
    if current:
        lines.append(f"⏳ 当前行动：{await get_name(app, current)}｜需跟：{max(0, game.current_bet - game.round_bets[current])}")
    lines.append("")
    lines.append("👥 玩家状态")
    lines.append("")
    for index, uid in enumerate(game.players, 1):
        status = "❌ 弃牌" if uid in game.folded else "🔥 全下" if uid in game.all_in else "🟢 在局"
        lines.extend([f"{index}. {await get_name(app, uid)}", f"   {status}｜投入 {game.total_bet[uid]}｜余筹 {game.chips[uid]}", ""])
    return "\n".join(lines)


def poker_buttons(game, uid):
    rows = [[InlineKeyboardButton("🂠 查看手牌", callback_data="texas_hand")]]
    if uid != game.current() or uid in game.folded or uid in game.all_in:
        rows.append([InlineKeyboardButton("🛑 终止本局", callback_data="texas_end")])
        return InlineKeyboardMarkup(rows)
    to_call = max(0, game.current_bet - game.round_bets[uid])
    rows.append([InlineKeyboardButton("❌ 弃牌", callback_data="texas_fold"), InlineKeyboardButton("✅ 过牌" if not to_call else f"✅ 跟注 {to_call}", callback_data="texas_check" if not to_call else "texas_call")])
    if uid not in game.raise_locked and game.chips[uid] >= to_call + FIXED_MIN_RAISE:
        rows.append([InlineKeyboardButton(f"🔼 加注 {FIXED_MIN_RAISE}", callback_data=f"texas_raise_{FIXED_MIN_RAISE}")])
    if game.chips[uid] > 0: rows.append([InlineKeyboardButton(f"🔥 全下 {game.chips[uid]}", callback_data="texas_allin")])
    rows.append([InlineKeyboardButton("🛑 终止本局", callback_data="texas_end")])
    return InlineKeyboardMarkup(rows)


async def update_poker_table(game, app):
    # 回归原地编辑逻辑
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await poker_table_text(game, app))


async def start_turn_timer(game, app):
    game.cancel_timer()
    uid = game.current()
    if uid is None:
        if game.phase == "showdown": await settle_poker(game, app)
        return
    # 原地更新主表文字
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await poker_table_text(game, app))
    # 仅操作按钮区做必要的删发以保证置底
    await safe_delete(app.bot, game.chat_id, game.action_msg_id)
    text = f"⏰ <b>{await get_name(app, uid)}</b> 请在 {TURN_TIMEOUT} 秒内行动。"
    msg = await safe_send(app.bot, game.chat_id, text, reply_markup=poker_buttons(game, uid), parse_mode="HTML")
    game.action_msg_id = msg.message_id if msg else None


async def settle_poker(game, app):
    if game.settled: return
    game.settled = True; game.cancel_timer(); game.cancel_auto(); game.cancel_wait()
    try:
        result = game.showdown()
        if not result: raise RuntimeError("德州摊牌未生成结算结果")
        date, hand_types = business_date(), result[0][4]
        name_ids = set(game.players) | set(game.showdown_order)
        names = {uid: await get_name(app, uid) for uid in name_ids}
        board_text = "  ".join(card_str(card) for card in game.board) or "未发牌"
        lines = ["🃏 <b>德州结算</b>", "━━━━━━━━━━━━━━━━━", f"🃏 公牌：{board_text}", ""]

        if len(game.showdown_order) > 1:
            lines.append("亮牌：")
            for uid in game.players:
                if uid in game.folded: lines.extend([f"{names[uid]}：弃牌", ""])
                else: lines.extend([f"{names[uid]}：{'  '.join(card_str(card) for card in game.hands[uid])}｜{hand_types.get(uid, '')}", ""])
        else:
            lines.append("亮牌牌型：")
            for uid in game.players:
                if uid not in game.folded: lines.append(f"{names[uid]}：未亮牌")
                else: lines.append(f"{names[uid]}：弃牌")
            lines.append("")
        
        lines.append("派奖：")
        for uid, hand, amount, details, _ in sorted(result, key=lambda item: item[2], reverse=True):
            lines.extend([f"{names[uid]}：{hand}｜+{amount}（{'，'.join(f'{pool}+{value}' for pool, value in details)}）", ""])
        
        lines.append("投入 / 盈亏：")
        for uid in game.players:
            net = game.chips[uid] - game.initial_chips[uid]
            if game.mode == "official":
                profit_by_date[date][game.chat_id][uid] += net
                poker_profit_by_date[date][game.chat_id][uid] += net
            lines.extend([f"{names[uid]}：投入 {game.total_bet[uid]}｜盈亏 {net:+d}", ""])
            
        if game.mode == "official":
            rank = sorted(poker_profit_by_date[date][game.chat_id].items(), key=lambda item: item[1], reverse=True)[:50]
            lines.extend(["", "🏆 <b>当日德州累计盈利榜</b>", "━━━━━━━━━━━━━━━━━"])
            lines.extend([f"{rank_marker(index)} {names.get(uid) or await get_name(app, uid)}：{amount:+d}" for index, (uid, amount) in enumerate(rank, 1)])
            
        delivered = await safe_send_long(app.bot, game.chat_id, "\n".join(lines), parse_mode="HTML")
        if delivered is None:
            await safe_send(app.bot, game.chat_id, "⚠️ 德州已完成结算，但详细结算消息发送失败。")
    except Exception:
        logger.exception("德州结算异常")
    finally:
        if active_poker_games.get(game.chat_id) is game: active_poker_games.pop(game.chat_id, None)
        if game.mode == "official":
            for uid in game.players: await emergency_if_needed(game.chat_id, uid, app, game)
        save_data()



# ==================== 赛马 ====================
class HorseRace:
    def __init__(self, cid, owner, jackpot, mode=None):
        self.chat_id, self.owner_id, self.jackpot = cid, owner, jackpot
        self.mode = mode or current_game_mode()
        self.bets, self.total_bets, self.pool = defaultdict(dict), [0] * HORSE_COUNT, 0
        self.phase, self.create_time, self.positions, self.arrivals = "betting", time.time(), [0.0] * HORSE_COUNT, []
        self.arrival_times, self.race_start_time = {}, None
        self.notified, self.name_cache = set(), {}
        self.game_msg_id = self.animation_msg_id = None
        self.task, self.settled, self.cancelled, self.lock = None, False, False, asyncio.Lock()
        self.final_odds = None
        rates = [random.uniform(.18, .35) for _ in range(HORSE_COUNT)]; total = sum(rates)
        self.rates = [value / total for value in rates]
        # 用胜率抽样每匹对象的精确完赛时间：长期获胜概率更接近显示胜率，仍保留随机爆冷。
        self.finish_durations = {}

    def odds(self):
        total = sum(self.total_bets); smoothing = 1000
        values = []
        for i in range(HORSE_COUNT):
            likelihood = self.total_bets[i] / total if total else 1 / HORSE_COUNT
            posterior = (self.rates[i] * smoothing + likelihood * total) / (smoothing + total)
            values.append(max(1.6, min(1 / max(posterior, .01), 8)))
        return values

    def bet(self, uid, horse, amount):
        if self.phase != "betting" or self.cancelled: return False, "当前不是下注阶段"
        wallet = entertainment_chips if self.mode == "entertainment" else group_chips
        if not 0 <= horse < HORSE_COUNT or amount <= 0 or amount > wallet[self.chat_id][uid]: return False, "马号、金额或筹码无效"
        wallet[self.chat_id][uid] -= amount; self.pool += amount; self.total_bets[horse] += amount
        self.bets[uid][horse] = self.bets[uid].get(horse, 0) + amount
        
        # 记录退款保护
        curr_pending = pending_game_bets[self.chat_id][uid].get("horse", {}).get("amount", 0)
        pending_game_bets[self.chat_id][uid]["horse"] = {"amount": curr_pending + amount, "mode": self.mode}
        save_data(); return True, "下注成功"

    def buttons(self):
        return InlineKeyboardMarkup([[InlineKeyboardButton(f"{HORSE_EMOJI[i]} {amount}", callback_data=f"horsebet_{i}_{amount}") for i in range(HORSE_COUNT)] for amount in FIXED_BET_AMOUNTS])

    async def view(self, app):
        """保持原版赛马下注界面的赛道、路书、胜率和投注信息结构。"""
        remain = max(0, int(RACE_AUTO_START - (time.time() - self.create_time)))
        minutes, seconds = divmod(remain, 60)
        history = "".join(HORSE_EMOJI[index] for index in race_history[self.chat_id][-10:]) or "暂无"
        stats = race_daily_stats[self.chat_id]
        total_wins = sum(stats)
        odds = self.odds()
        lines = [
            f"🏇 赛马大赛 {race_id(self.create_time)} 🏇 【下注中】",
            "━" * 14,
            *[f"🏁{'━' * 13}{HORSE_EMOJI[i]}" for i in range(HORSE_COUNT)],
            "━" * 14,
            "📊 路书",
            f"近10场: {history}",
            "📜 当日胜率:",
            "  " + " | ".join(f"{HORSE_EMOJI[i]} {stats[i]}胜" for i in range(HORSE_COUNT)),
            "  " + " | ".join(f"{HORSE_EMOJI[i]} {stats[i] / total_wins * 100:.0f}%" if total_wins else f"{HORSE_EMOJI[i]} 0%" for i in range(HORSE_COUNT)),
            "📊 投注情况:",
        ]
        for i, odd in enumerate(odds):
            lines.append(f"{HORSE_EMOJI[i]} {HORSE_NAMES[i]}: 胜率{self.rates[i] * 100:.0f}% | {self.total_bets[i]}积分 | 赔率 {odd:.2f}x")
        lines.append("━" * 14)
        if self.bets:
            lines.append("📋 玩家下注：")
            for uid, bets in self.bets.items():
                name = self.name_cache.get(uid) or await get_name(app, uid)
                self.name_cache[uid] = name
                lines.append(f"{name}: " + " ".join(f"{HORSE_EMOJI[h]}{amount}" for h, amount in bets.items()))
            lines.append("")
        lines.extend([f"⏰ 距离开赛还有 {minutes} 分 {seconds:02d} 秒", "🔒 开赛后无法投注"])
        return "\n".join(lines)

    def animation(self):
        lines = ["🏇 赛马进行中", "━" * 14]
        for i, pos in enumerate(self.positions):
            track_pos = max(0, min(RACE_TRACK_LENGTH, int(pos)))
            track = "🏁" + (HORSE_EMOJI[i] + "━" * RACE_TRACK_LENGTH if track_pos >= RACE_TRACK_LENGTH else "━" * (RACE_TRACK_LENGTH - track_pos - 1) + HORSE_EMOJI[i] + "━" * track_pos)
            lines.append(track)
        if self.arrivals: lines.append("✅ 到达：" + " ".join(HORSE_EMOJI[i] for i in self.arrivals))
        return "\n".join(lines)

    async def run(self, app):
        try:
            # 统一通知点：60秒, 30秒
            thresholds = [60, 30]
            while self.phase == "betting" and not self.cancelled:
                # 实时计算剩余时间
                remain = max(0, int(RACE_AUTO_START - (time.time() - self.create_time)))
                
                # 只有在整秒点附近才发出推送通知，防止重复发送
                for threshold in thresholds:
                    if remain <= threshold and threshold not in self.notified:
                        self.notified.add(threshold)
                        await safe_send(app.bot, self.chat_id, f"⏰ 赛马还剩 {threshold // 60} 分钟 {threshold % 60} 秒！")
                
                if not remain: break
                
                # 实时刷新主面板
                await safe_edit(app.bot, self.chat_id, self.game_msg_id, await self.view(app), reply_markup=self.buttons())
                
                # 缩短检查间隔至 5 秒，让通知和显示更同步，且不卡顿
                await asyncio.sleep(min(5, max(1, remain)))

            if self.cancelled: return
            self.phase = "racing"
            self.final_odds = self.odds()
            self.race_start_time = time.time()
            await safe_edit(app.bot, self.chat_id, self.game_msg_id, "🏇 比赛开始！正在奔跑中……", reply_markup=None)
            msg = await safe_send(app.bot, self.chat_id, "🏇 比赛开始！正在奔跑中……"); self.animation_msg_id = msg.message_id if msg else None
            last_update = self.race_start_time
            # 先按胜率加权抽取完整名次，再分配有间隔的完赛时间。
            # 这样长期夺冠率接近显示胜率，同时不会出现开赛第一帧直接到终点。
            remaining = list(range(HORSE_COUNT))
            finish_order = []
            while remaining:
                total_rate = sum(self.rates[index] for index in remaining)
                target = random.uniform(0, total_rate)
                cumulative = 0.0
                for index in remaining:
                    cumulative += self.rates[index]
                    if cumulative >= target:
                        finish_order.append(index)
                        remaining.remove(index)
                        break
            minimum_duration = 6.0
            finish_gap = 1.25
            self.finish_durations = {
                horse: minimum_duration + rank * finish_gap + random.uniform(-0.20, 0.20)
                for rank, horse in enumerate(finish_order)
            }
            while not self.cancelled and len(self.arrivals) < HORSE_COUNT:
                now = time.time()
                elapsed = max(0.05, now - last_update)
                last_update = now
                for i in range(HORSE_COUNT):
                    if i in self.arrival_times:
                        continue
                    duration = self.finish_durations[i]
                    progress = min(1.0, max(0.0, (now - self.race_start_time) / duration))
                    self.positions[i] = RACE_TRACK_LENGTH * progress
                    if progress >= 1.0:
                        self.arrival_times[i] = self.race_start_time + duration
                        self.positions[i] = float(RACE_TRACK_LENGTH)
                self.arrivals = sorted(self.arrival_times, key=self.arrival_times.get)
                await safe_edit(app.bot, self.chat_id, self.animation_msg_id, self.animation())
                if len(self.arrivals) < HORSE_COUNT: await asyncio.sleep(RACE_ANIMATION_INTERVAL)
            if not self.cancelled: await self.settle(app)
        except asyncio.CancelledError: raise
        except Exception:
            logger.exception("赛马任务异常")
            if not self.settled:
                await self.refund(app, "⚠️ 赛马异常，所有下注已退款。")

    async def settle(self, app):
        async with self.lock:
            if self.settled or self.cancelled: return
            self.settled, self.phase = True, "settling"
            try:
                if not self.arrivals: raise RuntimeError("赛马未产生到达顺序")
                locked_odds = self.final_odds or self.odds()
                winner, odd, date = self.arrivals[0], locked_odds[self.arrivals[0]], business_date()
                if self.mode == "official":
                    race_daily_stats[self.chat_id][winner] += 1
                    race_history[self.chat_id] = (race_history[self.chat_id] + [winner])[-10:]
                standings = ["🥇", "🥈", "🥉", "🏅"]
                lines = [f"🏆 赛马大赛 {race_id(self.create_time)} 结果 🏆", "━━━━━━━━━━━━━━━━━"]
                lines.extend(f"{standings[index]} {HORSE_EMOJI[horse]} {HORSE_NAMES[horse]}" for index, horse in enumerate(self.arrivals))

                settlements, total_payout = [], 0
                for uid, bets in self.bets.items():
                    stake, payout = sum(bets.values()), int(bets.get(winner, 0) * odd)
                    net = payout - stake
                    wallet = entertainment_chips if self.mode == "entertainment" else group_chips
                    wallet[self.chat_id][uid] += payout; total_payout += payout
                    if self.mode == "official":
                        profit_by_date[date][self.chat_id][uid] += net
                        race_profit_by_date[date][self.chat_id][uid] += net
                    name = self.name_cache.get(uid) or await get_name(app, uid)
                    self.name_cache[uid] = name
                    settlements.append((uid, name, stake, payout, net))

                available_pool = self.jackpot + self.pool
                supplement = max(0, total_payout - available_pool)
                if self.mode == "official":
                    race_jackpot[self.chat_id] = max(0, available_pool - total_payout)
                if supplement:
                    lines.extend(["", f"⚠️ 奖池不足，系统补充 {supplement} 积分"])
                elif not total_payout:
                    lines.extend(["", "🔄 无人押中，奖池滚入下一期。"])

                lines.extend(["", "💰 本局结算："])
                for _, name, stake, payout, net in settlements:
                    lines.append(f"{name}：投注 {stake}｜派彩 {payout}｜盈亏 {net:+d}｜赔率 {odd:.2f}x")

                if self.mode == "official":
                    day_rank = sorted(race_profit_by_date[date][self.chat_id].items(), key=lambda item: item[1], reverse=True)[:50]
                    lines.extend(["", "🏆 <b>当日赛马累计盈利榜</b>", "━━━━━━━━━━━━━━━━━"])
                    for index, (uid, amount) in enumerate(day_rank, 1):
                        name = self.name_cache.get(uid) or await get_name(app, uid)
                        lines.append(f"{rank_marker(index)} {name}：{amount:+d}")
                else:
                    lines.extend(["", "🎮 娱乐局：本局不计入正式盈亏榜。"])
                
                pending_horse_bets.pop(self.chat_id, None); pending_horse_bet_modes.pop(self.chat_id, None); self.phase = "finished"; save_data()
                # 清除退款记录
                for uid in self.bets: pending_game_bets[self.chat_id].get(uid, {}).pop("horse", None)
                delivered = await safe_send_long(app.bot, self.chat_id, "\n".join(lines), parse_mode="HTML")

                if delivered is None:
                    await safe_send(app.bot, self.chat_id, "⚠️ 赛马已完成结算，但详细结果消息发送失败。筹码与当日盈亏已保存，可使用 /cx 查看排行榜。")
            except Exception:
                logger.exception("赛马结算异常，群 %s", self.chat_id)
                await safe_send(app.bot, self.chat_id, "⚠️ 赛马结算异常，请管理员检查日志；本局将退款以保护玩家筹码。")
                wallet = entertainment_chips if self.mode == "entertainment" else group_chips
                for uid, bets in self.bets.items():
                    wallet[self.chat_id][uid] += sum(bets.values())
                pending_horse_bets.pop(self.chat_id, None)
                pending_horse_bet_modes.pop(self.chat_id, None)
                if self.mode == "official": race_jackpot[self.chat_id] = self.jackpot
                save_data()
            finally:
                await safe_delete(app.bot, self.chat_id, self.animation_msg_id)
                if active_horse_races.get(self.chat_id) is self: active_horse_races.pop(self.chat_id, None)
                if self.mode == "official":
                    for uid in self.bets: await emergency_if_needed(self.chat_id, uid, app)

    async def refund(self, app, notice):
        async with self.lock:
            if self.cancelled: return
            self.cancelled, self.phase = True, "cancelled"
            wallet = entertainment_chips if self.mode == "entertainment" else group_chips
            for uid, bets in self.bets.items(): 
                wallet[self.chat_id][uid] += sum(bets.values())
                pending_game_bets[self.chat_id].get(uid, {}).pop("horse", None)
            if self.mode == "official": race_jackpot[self.chat_id] += self.jackpot
            save_data()
            if active_horse_races.get(self.chat_id) is self: active_horse_races.pop(self.chat_id, None)
            await safe_edit(app.bot, self.chat_id, self.game_msg_id, notice, reply_markup=None)


# ---------- 权限与命令 ----------
def is_auth(cid): return cid in AUTHORIZED_GROUPS
def is_bot_admin(uid): return uid == ADMIN_USER_ID
async def need_auth(update):
    if not update.effective_chat or not is_auth(update.effective_chat.id):
        if update.effective_message: await update.effective_message.reply_text("❌ 此群组未授权，请联系管理员。")
        return False
    return True

async def cmd_start(update, context): await update.message.reply_text("🎮 欢迎使用娱乐机器人！\n\n可用命令：\n/dz - 发起德州扑克\n/sm - 发起赛马\n/wz - 发起五子棋\n/sl - 发起扫雷\n/lhj - 老虎机抽奖\n/21 - 发起21点\n/bjl - 发起百家乐\n\n📊 数据查询：\n/cx - 当日盈亏榜\n/ph - 总筹码榜\n/end - 终止当前游戏")

async def gomoku_wait_timeout(game, app):
    await asyncio.sleep(AUTO_START_TIMEOUT)
    if game.phase == "waiting" and active_gomoku_games.get(game.chat_id) is game:
        active_gomoku_games.pop(game.chat_id, None)
        await update_gomoku_board(game, app, {}, remove_keyboard=True, custom_caption="⌛ 五子棋等待 60 秒无人加入，本局已取消。")


async def cancel_gomoku(game, app, notice):
    """取消五子棋并清理等待计时器、活动状态和旧键盘。"""
    game.phase = "cancelled"
    task, game.wait_task = game.wait_task, None
    if task and task is not asyncio.current_task() and not task.done():
        task.cancel()
    if active_gomoku_games.get(game.chat_id) is game:
        active_gomoku_games.pop(game.chat_id, None)
    await update_gomoku_board(game, app, {}, remove_keyboard=True, custom_caption=notice)


async def settle_gomoku(game, app, names):
    """五子棋结算。"""
    await update_gomoku_board(game, app, names, remove_keyboard=True)
    black = names.get(game.players[0], str(game.players[0]))
    white = names.get(game.players[1], str(game.players[1]))
    result = "🤝 本局和棋。" if game.draw else f"🏆 获胜者：{names.get(game.winner, str(game.winner))}"
    await safe_send(
        app.bot,
        game.chat_id,
        f"🏁 五子棋结算\n━━━━━━━━━━━━━━━━━\n⚫ 黑方：{black}\n⚪ 白方：{white}\n\n{result}",
    )
    if active_gomoku_games.get(game.chat_id) is game:
        active_gomoku_games.pop(game.chat_id, None)


async def cmd_wz(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if cid in active_gomoku_games:
        await update.message.reply_text("当前已有进行中的五子棋。"); return
    game = GomokuGame(cid, uid); game.add(uid); active_gomoku_games[cid] = game
    names = {uid: await get_name(context.application, uid)}
    # 方案二：初始发送文本消息
    msg = await safe_send(context.bot, cid, game.caption(names), reply_markup=game.buttons())
    if msg:
        game.game_msg_id = msg.message_id
        game.wait_task = asyncio.create_task(gomoku_wait_timeout(game, context.application))

async def update_mine_board(game, app, names):
    await safe_edit(
        app.bot,
        game.chat_id,
        game.game_msg_id,
        game.caption(names),
        reply_markup=game.buttons(),
    )


async def cmd_sl(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if cid in active_minesweeper_games:
        await update.message.reply_text("当前已有进行中的扫雷。"); return
    game = MinesweeperGame(cid, uid); game.add(uid); active_minesweeper_games[cid] = game
    msg = await safe_send(context.bot, cid, game.caption({}), reply_markup=game.buttons())
    if msg: game.game_msg_id = msg.message_id


# ---------- 21点 / 百家乐 界面与逻辑 ----------
async def start_bj_turn_timer(game, app):
    game.cancel_timer()
    curr_uid = game.players[game.current_player_idx]
    async def timeout():
        await asyncio.sleep(TURN_TIMEOUT)
        if game.phase == "playing" and game.players[game.current_player_idx] == curr_uid:
            game.next_player()
            await safe_send(app.bot, game.chat_id, f"⏰ {await get_name(app, curr_uid)} 超时自动停牌。")
            if game.phase == "dealer_turn": await update_blackjack_ui(game, app)
            else: await update_blackjack_ui(game, app); await start_bj_turn_timer(game, app)
    game.timer_task = asyncio.create_task(timeout())

async def start_bj_wait_timeout(game, app):
    """21点开房后，若 60 秒内未开始则自动解散。"""
    game.cancel_wait()
    async def expire():
        await asyncio.sleep(AUTO_START_TIMEOUT)
        if game.phase == "waiting" and active_blackjack_games.get(game.chat_id) is game:
            # 退还已加入玩家的筹码
            wallet = entertainment_chips if game.mode == "entertainment" else group_chips
            for uid, bet in game.bets.items():
                wallet[game.chat_id][uid] += bet
                pending_game_bets[game.chat_id].get(uid, {}).pop("21", None)
            active_blackjack_games.pop(game.chat_id, None)
            await safe_edit(app.bot, game.chat_id, game.game_msg_id, "⌛ 21点等待 60 秒未开始，房间已自动解散并退款。", reply_markup=None)
    game.wait_task = asyncio.create_task(expire())

async def start_baccarat_timer(game, app):
    """百家乐下注倒计时刷新任务：30秒自动开牌。"""
    game.cancel_timer()
    async def countdown():
        # 设置总共 30 秒
        total_wait = 30
        interval = 10 # 每 10 秒刷新一次界面，防止刷屏过猛
        
        start_ts = time.time()
        while True:
            await asyncio.sleep(1)
            elapsed = time.time() - start_ts
            if elapsed >= total_wait: break
            
            # 每 10 秒主动刷新一次界面显示剩余时间
            if int(elapsed) % interval == 0 and int(elapsed) > 0:
                if game.phase == "betting" and active_baccarat_games.get(game.chat_id) is game:
                    await update_baccarat_ui(game, app)
        
        # 时间到，自动开牌
        if game.phase == "betting" and active_baccarat_games.get(game.chat_id) is game:
            await settle_baccarat(game, app)
            
    game.timer_task = asyncio.create_task(countdown())

async def update_blackjack_ui(game, app):
    if game.phase == "waiting":
        history_list = "".join(blackjack_history[game.chat_id][-10:]) or "暂无"
        text = (
            f"🃏 <b>21点 (Blackjack)</b>\n"
            f"━━━━━━━━━━━━━━━━━\n"
            f"📊 <b>庄家路书</b>：{history_list}\n\n"
            f"发起人：{await get_name(app, game.owner_id)}\n\n"
            f"已加入：\n"
        )
        for uid in game.players:
            text += f"- {await get_name(app, uid)} (下注: {game.bets[uid]})\n"
        kb = [[InlineKeyboardButton("加入 (下注500)", callback_data="bj_join_500"), InlineKeyboardButton("加入 (下注1000)", callback_data="bj_join_1000")]]
        if game.players: kb.append([InlineKeyboardButton("开始游戏", callback_data="bj_start")])
        kb.append([InlineKeyboardButton("🛑 终止", callback_data="bj_end")])
        await safe_edit(app.bot, game.chat_id, game.game_msg_id, text, reply_markup=InlineKeyboardMarkup(kb), parse_mode="HTML")
    elif game.phase == "playing":
        curr_uid = game.players[game.current_player_idx]
        text = f"🃏 <b>21点 进行中</b>\n\n🏛 <b>庄家</b>：{game.get_card_str(game.dealer_hand, True)}\n\n"
        for uid in game.players:
            mark = " 👈 <b>行动中</b>" if uid == curr_uid else ""
            text += f"👤 <b>玩家</b>：{await get_name(app, uid)} | {game.get_card_str(game.hands[uid])} ({game.get_score(game.hands[uid])}){mark}\n\n"
        
        # 1. 原地更新主面板文字
        await safe_edit(app.bot, game.chat_id, game.game_msg_id, text, reply_markup=None, parse_mode="HTML")
        
        # 2. 动态发送/更新底部的操作按钮
        await safe_delete(app.bot, game.chat_id, game.game_msg_id if game.phase == "waiting" else game.action_msg_id)
        
        dealer_peek = game.get_card_str(game.dealer_hand, True)
        my_hand = game.get_card_str(game.hands[curr_uid])
        my_score = game.get_score(game.hands[curr_uid])
        
        action_text = (
            f"⏰ <b>玩家</b>：{await get_name(app, curr_uid)}\n\n"
            f"🏛 <b>庄家</b>：{dealer_peek}\n\n"
            f"👤 <b>我的</b>：{my_hand} ({my_score}点)"
        )
        
        kb_rows = [[
            InlineKeyboardButton("🃏 要牌 (Hit)", callback_data=f"bj_hit_{curr_uid}"),
            InlineKeyboardButton("✋ 停牌 (Stand)", callback_data=f"bj_stand_{curr_uid}")
        ]]
        
        wallet = entertainment_chips if game.mode == "entertainment" else group_chips
        if len(game.hands[curr_uid]) == 2 and wallet[game.chat_id][curr_uid] >= game.bets[curr_uid]:
            kb_rows.append([InlineKeyboardButton("💰 双倍 (Double Down)", callback_data=f"bj_double_{curr_uid}")])
        
        msg = await safe_send(app.bot, game.chat_id, action_text, reply_markup=InlineKeyboardMarkup(kb_rows), parse_mode="HTML")
        if msg: game.action_msg_id = msg.message_id
    elif game.phase == "dealer_turn":
        # 庄家补牌后直接进入结算
        await safe_delete(app.bot, game.chat_id, game.action_msg_id)
        game.dealer_play()
        # 确保跳转到 finished 逻辑
        await update_blackjack_ui(game, app)
    elif game.phase == "finished":
        # 增加整体 try-except 保护
        try:
            await safe_delete(app.bot, game.chat_id, game.action_msg_id)
            d_score = game.get_score(game.dealer_hand)
            text = f"🃏 <b>21点 结算</b>\n━━━━━━━━━━━━━━━━━\n🏛 <b>庄家</b>：{game.get_card_str(game.dealer_hand)} ({d_score})\n\n"
            date = business_date()
            wallet = entertainment_chips if game.mode == "entertainment" else group_chips
            
            lines = []
            # 预先获取所有名字，提高 HTML 生成速度
            player_names = {}
            for uid in game.players: player_names[uid] = await get_name(app, uid)
            
            for uid in game.players:
                p_score = game.get_score(game.hands[uid])
                bet = game.bets[uid]
                result_str = ""
                payout = 0
                
                if p_score > 21: result_str = "💥 爆牌 (负)"; payout = 0
                elif d_score > 21: 
                    if game.is_blackjack(game.hands[uid]): result_str = "🃏 Blackjack (胜)"; payout = int(bet * 2.5)
                    else: result_str = "🏛 庄爆 (胜)"; payout = bet * 2
                elif p_score > d_score:
                    if game.is_blackjack(game.hands[uid]): result_str = "🃏 Blackjack (胜)"; payout = int(bet * 2.5)
                    else: result_str = "🎉 获胜"; payout = bet * 2
                elif p_score < d_score: result_str = "💸 战败"; payout = 0
                else: result_str = "🤝 平局"; payout = bet
                
                net = payout - bet
                wallet[game.chat_id][uid] += payout
                if game.mode == "official":
                    profit_by_date[date][game.chat_id][uid] += net
                    blackjack_profit_by_date[date][game.chat_id][uid] += net
                hand_text = game.get_card_str(game.hands[uid])
                lines.append(f"👤 <b>玩家</b>：{player_names[uid]} | {hand_text} ({p_score})\n<b>结果</b>：{result_str} | 盈亏 {net:+d}")
                pending_game_bets[game.chat_id].get(uid, {}).pop("21", None)

            # 记录庄家历史 (仅记录本局主要趋势)
            if game.mode == "official":
                # 计算本局玩家总体输赢，用于生成庄家路书图标
                total_net = sum(payout - game.bets[uid] for uid in game.players)
                history_icon = "🏛" if total_net < 0 else ("🤝" if total_net == 0 else "👤")
                blackjack_history[game.chat_id] = (blackjack_history[game.chat_id] + [history_icon])[-10:]

            text += "\n\n".join(lines)
            if game.mode == "entertainment": text += "\n\n🎮 娱乐局，筹码不计入正式榜单。"
            
            if game.mode == "official":
                bj_rank = sorted(blackjack_profit_by_date[date][game.chat_id].items(), key=lambda item: item[1], reverse=True)[:30]
                text += "\n\n🏆 <b>当日 21点 累计盈利榜</b>\n"
                text += "\n".join([f"{rank_marker(i)} {player_names.get(u, '未知')}：{a:+d}" for i, (u, a) in enumerate(bj_rank, 1)])
                
            await safe_delete(app.bot, game.chat_id, game.game_msg_id)
            await safe_send_long(app.bot, game.chat_id, text, parse_mode="HTML")
        except Exception:
            logger.exception("21点结算显示失败")
            await safe_send(app.bot, game.chat_id, "⚠️ 21点已结算，但由于 HTML 渲染问题无法显示详细战报。筹码已保存。")
        finally:
            active_blackjack_games.pop(game.chat_id, None)
            save_data()



async def update_baccarat_ui(game, app):
    if game.phase == "betting":
        # 统一使用 30 秒倒计时逻辑
        total_wait = 30
        remain = max(0, int(total_wait - (time.time() - game.create_time)))
        history_icons = {"player": "🔵", "banker": "🔴", "tie": "🟢"}
        history_list = "".join(history_icons.get(r, "") for r in baccarat_history[game.chat_id][-12:]) or "暂无"
        
        stats = baccarat_daily_stats[game.chat_id]
        total = sum(stats.values())
        if total > 0:
            stats_text = f"🔵{stats['player']} | 🔴{stats['banker']} | 🟢{stats['tie']} (共{total}局)"
            percent_text = f"闲 {stats['player']/total*100:.0f}% | 庄 {stats['banker']/total*100:.0f}% | 和 {stats['tie']/total*100:.0f}%"
        else:
            stats_text = "暂无数据"
            percent_text = "等待开局"

        p_total = sum(b["player"] for b in game.bets.values())
        b_total = sum(b["banker"] for b in game.bets.values())
        t_total = sum(b["tie"] for b in game.bets.values())
        
        text = [
            f"👑 <b>百家乐 大赛</b> 👑",
            "━━━━━━━━━━━━━━━━━",
            f"📊 <b>当日胜率</b>",
            f"{stats_text}",
            f"{percent_text}",
            "",
            f"📉 <b>历史路书</b>：{history_list}",
            "",
            f"💰 <b>当前奖池</b>",
            f"🔵 <b>闲家</b>：{p_total} 积分",
            f"🔴 <b>庄家</b>：{b_total} 积分",
            f"🟢 <b>和局</b>：{t_total} 积分",
            "━━━━━━━━━━━━━━━━━",
        ]
        
        if game.bets:
            text.append("📋 <b>实时下注</b>")
            for uid, b in game.bets.items():
                name = await get_name(app, uid)
                bet_str = []
                if b["player"] > 0: bet_str.append(f"🔵{b['player']}")
                if b["banker"] > 0: bet_str.append(f"🔴{b['banker']}")
                if b["tie"] > 0: bet_str.append(f"🟢{b['tie']}")
                text.append(f"👤 <b>玩家</b>：{name} | {' '.join(bet_str)}")
            text.append("")
            
        text.append(f"⏰ <b>将在 {remain} 秒后自动开牌</b>")
        text.append("🔒 庄闲平任你押，发牌后截止")
        
        kb = [
            [InlineKeyboardButton("🔵 押闲 (1:1)", callback_data="bjl_bet_player"), InlineKeyboardButton("🔴 押庄 (1:0.95)", callback_data="bjl_bet_banker")],
            [InlineKeyboardButton("🟢 押和 (1:8)", callback_data="bjl_bet_tie")],
            [InlineKeyboardButton("🎮 立即开牌", callback_data="bjl_start"), InlineKeyboardButton("🛑 终止", callback_data="bjl_end")]
        ]
        await safe_edit(app.bot, game.chat_id, game.game_msg_id, "\n".join(text), reply_markup=InlineKeyboardMarkup(kb), parse_mode="HTML")

async def settle_baccarat(game, app):
    # 模拟开牌动画
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, "👑 <b>百家乐</b>\n━━━━━━━━━━━━━━━━━\n🎴 <b>正在开牌中，请稍候...</b>", reply_markup=None, parse_mode="HTML")
    await asyncio.sleep(1.5)
    
    p_cards, b_cards, p_val, b_val, result = game.play()
    
    # 记录历史与胜率统计
    if game.mode == "official":
        baccarat_history[game.chat_id] = (baccarat_history[game.chat_id] + [result])[-12:]
        baccarat_daily_stats[game.chat_id][result] += 1
    
    text = f"👑 <b>百家乐 结算</b>\n\n🔵 <b>闲家</b>：{game.card_to_str(p_cards)} ({p_val}点)\n\n🔴 <b>庄家</b>：{game.card_to_str(b_cards)} ({b_val}点)\n\n"
    res_map = {"player": "🔵 闲胜", "banker": "🔴 庄胜", "tie": "🟢 和局"}
    text += f"<b>结果</b>：{res_map[result]}\n━━━━━━━━━━━━━━━━━\n"
    
    date = business_date()
    wallet = entertainment_chips if game.mode == "entertainment" else group_chips
    lines = []
    
    for uid, bets in game.bets.items():
        win_amount = 0
        total_bet = sum(bets.values())
        if result == "player": win_amount = bets["player"] * 2
        elif result == "banker": win_amount = int(bets["banker"] * 1.95)
        elif result == "tie": win_amount = bets["tie"] * 9
        
        net = win_amount - total_bet
        wallet[game.chat_id][uid] += win_amount
        if game.mode == "official":
            profit_by_date[date][game.chat_id][uid] += net
            baccarat_profit_by_date[date][game.chat_id][uid] += net
        if net != 0:
            lines.append(f"👤 <b>玩家</b>：{await get_name(app, uid)}\n<b>盈亏</b>：{net:+d}")
        # 清除退款记录（本局已结束，无论盈亏都清理本游戏的记录）
        pending_game_bets[game.chat_id].get(uid, {}).pop("baccarat", None)
            
    text += "\n\n".join(lines) if lines else "本局无人盈亏。"
    
    # 增加当日百家乐盈利榜
    if game.mode == "official":
        bjl_rank = sorted(baccarat_profit_by_date[date][game.chat_id].items(), key=lambda item: item[1], reverse=True)[:30]
        text += "\n\n🏆 <b>当日 百家乐 累计盈利榜</b>\n"
        text += "\n".join([f"{rank_marker(i)} {await get_name(app, u)}：{a:+d}" for i, (u, a) in enumerate(bjl_rank, 1)])

    # 核心：删除旧消息，发送新结算消息
    await safe_delete(app.bot, game.chat_id, game.game_msg_id)
    await safe_send_long(app.bot, game.chat_id, text, parse_mode="HTML")
    
    # 应急筹码检查
    if game.mode == "official":
        for uid in game.bets.keys():
            await emergency_if_needed(game.chat_id, uid, app)
    
    active_baccarat_games.pop(game.chat_id, None)
    save_data()

async def cmd_21(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if cid in active_blackjack_games:
        await update.message.reply_text("当前已有 21点 进行中。"); return
    mode = current_game_mode()
    game = BlackjackGame(cid, uid, mode)
    active_blackjack_games[cid] = game
    msg = await safe_send(context.bot, cid, "🃏 21点 筹码局准备中...", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("加入 (下注500)", callback_data="bj_join_500")]]))
    if msg: 
        game.game_msg_id = msg.message_id
        await update_blackjack_ui(game, context.application)
        await start_bj_wait_timeout(game, context.application) # 启动等待超时

async def cmd_bjl(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if cid in active_baccarat_games:
        await update.message.reply_text("当前已有 百家乐 进行中。"); return
    mode = current_game_mode()
    game = BaccaratGame(cid, uid, mode)
    active_baccarat_games[cid] = game
    msg = await safe_send(context.bot, cid, "👑 百家乐 准备中...", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("开始押注", callback_data="bjl_bet_player")]]))
    if msg: 
        game.game_msg_id = msg.message_id; 
        await update_baccarat_ui(game, context.application)
        await start_baccarat_timer(game, context.application)
SLOT_SYMBOLS = ["🍒", "🍋", "🍊", "🍇", "🔔", "💎", "7️⃣"]
SLOT_BET = 300  # 单次抽奖金额
SLOT_COOLDOWN = 3 # 冷却时间（秒）


def get_slot_result():
    res = [random.choice(SLOT_SYMBOLS) for _ in range(3)]
    # 简单的中奖逻辑
    if res[0] == res[1] == res[2]:
        if res[0] == "7️⃣": return res, 50 # 777 大奖 50倍
        if res[0] == "💎": return res, 20 # 钻石 20倍
        return res, 10 # 其他三连 10倍
    if res[0] == res[1] or res[1] == res[2] or res[0] == res[2]:
        return res, 2 # 任意两连 2倍
    return res, 0


async def cmd_lhj(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    
    # 彻底并发：不再限制忙碌状态
    # if player_is_busy(cid, uid): ...

    # 检查冷却时间
    now = time.time()
    if now - user_cooldowns[uid] < SLOT_COOLDOWN:
        await update.message.reply_text(f"🕒 别急，歇 {int(SLOT_COOLDOWN - (now - user_cooldowns[uid]))} 秒再抽吧。")
        return
    
    mode = current_game_mode()
    wallet = entertainment_chips if mode == "entertainment" else group_chips
    if wallet[cid][uid] < SLOT_BET:
        await update.message.reply_text(f"❌ 筹码不足，抽一次需要 {SLOT_BET}。")
        return
    
    # 扣钱并设置冷却
    user_cooldowns[uid] = now
    wallet[cid][uid] -= SLOT_BET
    
    # --- 1. 发送转动中的初始消息 ---
    name = await get_name(context.application, uid)
    spin_msg = await safe_send(context.bot, cid, f"🎰 <b>老虎机转动中...</b>\n\n👤 玩家：{name}\n━━━━━━━━━━━━━━━━━\n[ 🔄 | 🔄 | 🔄 ]", parse_mode="HTML")
    
    # --- 2. 模拟转动停顿 (1.5秒) ---
    await asyncio.sleep(1.5)
    
    res, multiplier = get_slot_result()
    payout = SLOT_BET * multiplier
    wallet[cid][uid] += payout
    
    date = business_date()
    res_str = " | ".join(res)
    
    if multiplier > 0:
        result_text = f"🎰 <b>老虎机结果：[ {res_str} ]</b>\n\n🎉 恭喜 {name} 中了 {multiplier} 倍！获得 {payout} 积分。"
    else:
        result_text = f"🎰 <b>老虎机结果：[ {res_str} ]</b>\n\n💸 很遗憾，{name} 未中奖，失去了 {SLOT_BET} 积分。"
    
    # 记录统计
    if mode == "official":
        net = payout - SLOT_BET
        slot_profit_by_date[date][cid][uid] += net
        profit_by_date[date][cid][uid] += net
        
        # 榜单
        s_rank = sorted(slot_profit_by_date[date][cid].items(), key=lambda item: item[1], reverse=True)[:10]
        result_text += "\n\n🏆 <b>当日老虎机累计盈利榜</b>\n"
        result_text += "\n".join([f"{rank_marker(i)} {await get_name(context.application, u)}：{a:+d}" for i, (u, a) in enumerate(s_rank, 1)])

    # --- 3. 原地编辑出结果，确保置底且不刷屏 ---
    if spin_msg:
        await safe_edit(context.bot, cid, spin_msg.message_id, result_text, parse_mode="HTML")
    
    save_data()
    if mode == "official": await emergency_if_needed(cid, uid, context.application)



async def start_wait_timeout(game, app):
    """德州开房后，等待超时无人开局则自动解散。"""
    game.cancel_wait()
    async def expire():
        await asyncio.sleep(AUTO_START_TIMEOUT)
        if game.phase == "waiting" and active_poker_games.get(game.chat_id) is game:
            await refund_poker(game, app, "⌛ 德州等待超时无人开局，房间已解散，筹码已退回。")
    game.wait_task = asyncio.create_task(expire())


async def start_auto_game(game, app):
    """德州房间满 2 人后，短暂倒计时自动开局。"""
    game.cancel_wait()
    await asyncio.sleep(3)
    if game.phase != "waiting" or len(game.players) < 2: return
    if active_poker_games.get(game.chat_id) is not game: return
    if game.start():
        await update_poker_table(game, app)
        await start_turn_timer(game, app)


async def cmd_dz(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id; game = active_poker_games.get(cid)
    mode = game.mode if game and game.phase == "waiting" else current_game_mode()
    wallet = entertainment_chips if mode == "entertainment" else group_chips
    if wallet[cid][uid] < MIN_ENTRY_CHIPS:
        label = "娱乐筹码" if mode == "entertainment" else "筹码"
        await update.message.reply_text(f"❌ 进入德州至少需要 {MIN_ENTRY_CHIPS} {label}。"); return
    if game:
        if game.phase != "waiting": await update.message.reply_text("当前已有进行中的德州扑克。"); return
        if game.add(uid):
            await update_poker_waiting(game, context.application); await update.message.reply_text("已加入当前等待房间。")
            if len(game.players) >= 2:
                game.cancel_wait()
                await start_auto_game(game, context.application)
        else: await update.message.reply_text("你已在等待房间中。")
        return
    game = PokerGame(cid, uid, mode); game.add(uid); active_poker_games[cid] = game
    msg = await safe_send(context.bot, cid, await poker_waiting_text(game, context.application), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("加入游戏", callback_data="texas_join")], [InlineKeyboardButton("🛑 终止房间", callback_data="texas_end")]]))
    if msg:
        game.game_msg_id = msg.message_id
        await start_wait_timeout(game, context.application)

async def cmd_sm(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id
    if cid in active_horse_races: await update.message.reply_text("当前已有赛马进行中。"); return
    mode = current_game_mode()
    jackpot = race_jackpot.pop(cid, 0) if mode == "official" else 0
    race = HorseRace(cid, update.effective_user.id, jackpot, mode); active_horse_races[cid] = race
    msg = await safe_send(context.bot, cid, await race.view(context.application), reply_markup=race.buttons())
    if msg: race.game_msg_id = msg.message_id
    race.task = asyncio.create_task(race.run(context.application)); save_data()

async def refund_poker(game, app, notice):
    """终止未结算牌局时，按开局筹码退还全部 ante、盲注和后续下注。"""
    game.cancel_timer(); game.cancel_auto(); game.cancel_wait()
    wallet = entertainment_chips if game.mode == "entertainment" else group_chips
    for player_id in game.players:
        # 德州下注只在局对象中暂扣；显式恢复开局余额，避免后续改动破坏退款语义。
        wallet[game.chat_id][player_id] = game.initial_chips.get(player_id, wallet[game.chat_id][player_id])
    game.phase = "cancelled"
    if active_poker_games.get(game.chat_id) is game:
        active_poker_games.pop(game.chat_id, None)
    await safe_delete(app.bot, game.chat_id, game.action_msg_id)
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, notice, reply_markup=None)
    save_data()


async def cmd_end(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    arg = context.args[0].lower() if context.args else ""
    
    poker = active_poker_games.get(cid)
    race = active_horse_races.get(cid)
    gomoku = active_gomoku_games.get(cid)
    mine = active_minesweeper_games.get(cid)
    bj = active_blackjack_games.get(cid)
    bjl = active_baccarat_games.get(cid)

    if not any([poker, race, gomoku, mine, bj, bjl]):
        await update.message.reply_text("当前没有进行中的游戏。"); return

    notices = []
    # 如果带了参数，只针对性关闭
    target_all = (arg == "")
    
    if gomoku and (target_all or arg in ["wz", "wzq", "gomoku", "五子棋"]):
        if uid == ADMIN_USER_ID or uid in gomoku.players:
            await cancel_gomoku(gomoku, context.application, "🛑 五子棋已终止。")
            notices.append("五子棋已终止")

    if poker and (target_all or arg in ["dz", "dzpk", "texas", "德州"]):
        if uid == ADMIN_USER_ID or uid in poker.players:
            await refund_poker(poker, context.application, "🛑 德州扑克已终止，筹码已退回。")
            notices.append("德州已退款")

    if race and (target_all or arg in ["sm", "race", "赛马"]):
        if uid == ADMIN_USER_ID or uid in race.bets:
            if race.phase == "betting":
                if race.task and not race.task.done(): race.task.cancel()
                await race.refund(context.application, "🛑 赛马已终止，筹码已退回。")
                notices.append("赛马已退款")
            else: notices.append("赛马进行中无法终止")

    if bj and (target_all or arg in ["21", "bj", "21点"]):
        if uid == ADMIN_USER_ID or uid in bj.players:
            wallet = entertainment_chips if bj.mode == "entertainment" else group_chips
            for p_uid, b in bj.bets.items():
                wallet[cid][p_uid] += b
                pending_game_bets[cid].get(p_uid, {}).pop("21", None)
            active_blackjack_games.pop(cid, None)
            await safe_edit(context.bot, cid, bj.game_msg_id, "🛑 21点已终止，筹码已退回。", reply_markup=None)
            notices.append("21点已退款")

    if bjl: # 百家乐特殊判断，因为 arg 可能对应 bjl
        if target_all or arg in ["bjl", "baccarat", "百家乐"]:
            if uid == ADMIN_USER_ID or uid in bjl.bets.keys():
                wallet = entertainment_chips if bjl.mode == "entertainment" else group_chips
                for p_uid, b_dict in bjl.bets.items():
                    for amount in b_dict.values(): wallet[cid][p_uid] += amount
                    pending_game_bets[cid].get(p_uid, {}).pop("baccarat", None)
                active_baccarat_games.pop(cid, None)
                await safe_edit(context.bot, cid, bjl.game_msg_id, "🛑 百家乐已终止，筹码已退回。", reply_markup=None)
                notices.append("百家乐已退款")

    if mine and (target_all or arg in ["sl", "sldz", "mine", "扫雷"]):
        if uid == ADMIN_USER_ID or uid in mine.players:
            active_minesweeper_games.pop(cid, None)
            await safe_edit(context.bot, cid, mine.game_msg_id, "🛑 扫雷已终止。", reply_markup=None)
            notices.append("扫雷已终止")

    if not notices:
        await update.message.reply_text("❌ 权限不足或未找到匹配的游戏指令。用法示例：/end dz")
    else:
        save_data()
        await update.message.reply_text("；".join(notices))
def player_is_busy(cid, uid):
    poker = active_poker_games.get(cid)
    if poker and poker.phase != "waiting" and uid in poker.players:
        return True
    race = active_horse_races.get(cid)
    if race and race.phase in {"betting", "racing", "settling"} and uid in race.bets:
        return True
    bj = active_blackjack_games.get(cid)
    if bj and bj.phase != "waiting" and uid in bj.players:
        return True
    bjl = active_baccarat_games.get(cid)
    if bjl and bjl.phase == "betting" and uid in bjl.bets:
        return True
    return False


async def _parse_target_amount(update, context):
    if len(context.args) >= 2:
        return int(context.args[0]), int(context.args[1])
    if len(context.args) == 1 and update.message.reply_to_message:
        return update.message.reply_to_message.from_user.id, int(context.args[0])
    raise ValueError


async def cmd_add(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not await need_auth(update): return
    try:
        uid, amount = await _parse_target_amount(update, context)
        if amount <= 0: raise ValueError
    except (ValueError, IndexError):
        await update.message.reply_text("用法：/add 用户ID 数量，或回复玩家消息后使用 /add 数量"); return
    cid = update.effective_chat.id
    if player_is_busy(cid, uid):
        await update.message.reply_text("该玩家正在游戏中，无法修改筹码。"); return
    group_chips[cid][uid] += amount; save_data()
    await update.message.reply_text(f"✅ 已增加 {await get_name(context.application, uid)} {amount} 筹码。")


async def cmd_reduce(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not await need_auth(update): return
    try:
        uid, amount = await _parse_target_amount(update, context)
        if amount <= 0: raise ValueError
    except (ValueError, IndexError):
        await update.message.reply_text("用法：/reduce 用户ID 数量，或回复玩家消息后使用 /reduce 数量"); return
    cid = update.effective_chat.id
    if player_is_busy(cid, uid):
        await update.message.reply_text("该玩家正在游戏中，无法修改筹码。"); return
    if group_chips[cid][uid] < amount:
        await update.message.reply_text("❌ 玩家筹码不足。"); return
    group_chips[cid][uid] -= amount; save_data()
    await update.message.reply_text(f"✅ 已扣除 {await get_name(context.application, uid)} {amount} 筹码。")


async def cmd_cx(update, context):
    if not await need_auth(update): return
    cid, data = update.effective_chat.id, profit_by_date[business_date()].get(update.effective_chat.id, {})
    if not data: await update.message.reply_text("当前业务日暂无盈亏记录。"); return
    lines = ["📊 当日综合盈亏榜", "━"*14]
    for i, (uid, value) in enumerate(sorted(data.items(), key=lambda x:x[1], reverse=True)[:50], 1): lines.append(f"{rank_marker(i)} {await get_name(context.application, uid)}：{value:+d}")
    await safe_send_long(context.bot, cid, "\n".join(lines))

async def cmd_ph(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id
    lines = ["💰 当前筹码榜", "━"*14]
    for i, (uid, value) in enumerate(sorted(group_chips[cid].items(), key=lambda x:x[1], reverse=True)[:50], 1):
        lines.append(f"{rank_marker(i)} {await get_name(context.application, uid)}：{value}（正式）")
    if is_entertainment_time():
        lines.extend(["", "🎮 娱乐筹码（23:00-00:00）", "━"*14])
        for i, (uid, value) in enumerate(sorted(entertainment_chips[cid].items(), key=lambda x:x[1], reverse=True)[:50], 1):
            lines.append(f"{rank_marker(i)} {await get_name(context.application, uid)}：{value}（娱乐）")
    await safe_send_long(context.bot, cid, "\n".join(lines))

async def cmd_sq(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    cid = update.effective_chat.id
    AUTHORIZED_GROUPS.add(cid); save_data()
    await update.message.reply_text(f"✅ 当前群已授权：{cid}")

async def cmd_qxshouquan(update, context):
    if not is_bot_admin(update.effective_user.id): return
    try: cid = int(context.args[0])
    except (IndexError, ValueError): await update.message.reply_text("用法：/qxshouquan 群ID"); return
    AUTHORIZED_GROUPS.discard(cid); save_data(); await update.message.reply_text(f"✅ 已取消授权 {cid}")

async def cmd_autosm(update, context):
    if not await need_auth(update): return
    if not is_bot_admin(update.effective_user.id): await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    cid = update.effective_chat.id; hourly_race_enabled[cid] = not hourly_race_enabled[cid]; save_data()
    await update.message.reply_text(f"整点自动赛马：{'✅ 已开启' if hourly_race_enabled[cid] else '❌ 已关闭'}")

async def on_button(update, context):
    try:
        q = update.callback_query
        if not q or not q.message:
            if q: await q.answer("该操作已过期", show_alert=True)
            return
        cid, uid, data = q.message.chat.id, q.from_user.id, q.data or ""
        if not is_auth(cid): await q.answer("未授权", show_alert=True); return
        
        # --- 21点 回调 ---
        if data.startswith("bj_"):
            game = active_blackjack_games.get(cid)
            if not game: await q.answer("游戏已结束", show_alert=True); return
            if data.startswith("bj_join_"):
                bet = int(data.split("_")[2])
                wallet = entertainment_chips if game.mode == "entertainment" else group_chips
                if wallet[cid][uid] < bet: await q.answer("筹码不足", show_alert=True); return
                if game.add_player(uid, bet):
                    wallet[cid][uid] -= bet
                    await q.answer("已加入"); await update_blackjack_ui(game, context.application)
                else: await q.answer("你已在局中或无法加入", show_alert=True)
            elif data == "bj_start":
                if uid != game.owner_id: await q.answer("仅发起人可开始", show_alert=True); return
                if game.start(): 
                    game.cancel_wait() # 开始后取消等待计时
                    await update_blackjack_ui(game, context.application); await start_bj_turn_timer(game, context.application)
                else: await q.answer("人数不足", show_alert=True)
            elif data.startswith("bj_hit_"):
                if uid not in game.players:
                    await q.answer("❌ 你未参与本局游戏。", show_alert=True); return
                if str(uid) != data.split("_")[2]: await q.answer("不是你的回合", show_alert=True); return
                card = game.hit(uid); await q.answer(f"你抽到了 {card}")
                if game.phase == "finished" or game.phase == "dealer_turn": await update_blackjack_ui(game, context.application)
                else: await update_blackjack_ui(game, context.application); await start_bj_turn_timer(game, context.application)
            elif data.startswith("bj_stand_"):
                if uid not in game.players:
                    await q.answer("❌ 你未参与本局游戏。", show_alert=True); return
                if str(uid) != data.split("_")[2]: await q.answer("不是你的回合", show_alert=True); return
                game.next_player(); await q.answer("停牌")
                if game.phase == "finished" or game.phase == "dealer_turn": await update_blackjack_ui(game, context.application)
                else: await update_blackjack_ui(game, context.application); await start_bj_turn_timer(game, context.application)
            elif data.startswith("bj_double_"):
                if uid not in game.players:
                    await q.answer("❌ 你未参与本局游戏。", show_alert=True); return
                if str(uid) != data.split("_")[2]: await q.answer("不是你的回合", show_alert=True); return
                wallet = entertainment_chips if game.mode == "entertainment" else group_chips
                if wallet[cid][uid] < game.bets[uid]: await q.answer("筹码不足，无法双倍", show_alert=True); return
                
                wallet[cid][uid] -= game.bets[uid]
                game.double_down(uid)
                await q.answer("双倍下注！摸牌并停牌")
                await action_notice(cid, context.application, uid, f"选择了双倍下注！")
                
                if game.phase == "finished" or game.phase == "dealer_turn": await update_blackjack_ui(game, context.application)
                else: await update_blackjack_ui(game, context.application); await start_bj_turn_timer(game, context.application)
            elif data == "bj_end":
                if uid != ADMIN_USER_ID and uid != game.owner_id: await q.answer("权限不足", show_alert=True); return
                # 退还本局下注
                wallet = entertainment_chips if game.mode == "entertainment" else group_chips
                for p_uid, bet in game.bets.items():
                    wallet[cid][p_uid] += bet
                    pending_game_bets[cid].get(p_uid, {}).pop("21", None)
                active_blackjack_games.pop(cid, None)
                await safe_edit(context.bot, cid, game.game_msg_id, "🛑 21点已手动终止，筹码已退回。", reply_markup=None)
            return

        # --- 百家乐 回调 ---
        if data.startswith("bjl_"):
            game = active_baccarat_games.get(cid)
            if not game: await q.answer("游戏已结束", show_alert=True); return
            if data.startswith("bjl_bet_"):
                side = data.split("_")[2]
                bet_amount = BACCARAT_FIXED_BET # 引用全局配置
                wallet = entertainment_chips if game.mode == "entertainment" else group_chips
                if wallet[cid][uid] < bet_amount: await q.answer("筹码不足", show_alert=True); return
                wallet[cid][uid] -= bet_amount
                game.place_bet(uid, side, bet_amount)
                side_names = {"player":"闲", "banker":"庄", "tie":"和"}
                await q.answer(f"✅ 押注 {side_names.get(side, side)} 成功 (累计: {game.bets[uid][side]})", show_alert=False)
                await update_baccarat_ui(game, context.application)
            elif data == "bjl_start":
                if uid != game.owner_id: await q.answer("仅发起人可开始", show_alert=True); return
                await settle_baccarat(game, context.application)
            elif data == "bjl_end":
                if uid != ADMIN_USER_ID and uid != game.owner_id: await q.answer("权限不足", show_alert=True); return
                # 退还本局下注
                wallet = entertainment_chips if game.mode == "entertainment" else group_chips
                for p_uid, b_dict in game.bets.items():
                    for amount in b_dict.values(): wallet[cid][p_uid] += amount
                    pending_game_bets[cid].get(p_uid, {}).pop("baccarat", None)
                active_baccarat_games.pop(cid, None)
                await safe_edit(context.bot, cid, game.game_msg_id, "🛑 百家乐已手动终止，筹码已退回。", reply_markup=None)
            return

        if data == "gomoku_join":
            game = active_gomoku_games.get(cid)
            if not game: await q.answer("五子棋已结束", show_alert=True); return
            if not game.add(uid): await q.answer("无法加入，棋局已开始或人数已满", show_alert=True); return
            if game.wait_task and not game.wait_task.done():
                game.wait_task.cancel()
                game.wait_task = None
            names = {player: await get_name(context.application, player) for player in game.players}
            await q.answer("已加入五子棋")
            await update_gomoku_board(game, context.application, names)
            return
        if data == "gomoku_end":
            game = active_gomoku_games.get(cid)
            if not game: await q.answer("五子棋已结束", show_alert=True); return
            if uid != ADMIN_USER_ID and uid not in game.players:
                await q.answer("仅管理员或本局玩家可终止", show_alert=True); return
            await q.answer("本局已终止")
            await cancel_gomoku(game, context.application, "🛑 五子棋已终止。")
            return
        if data.startswith("gomoku_place_"):
            game = active_gomoku_games.get(cid)
            if not game: await q.answer("棋局已结束", show_alert=True); return
            if uid not in game.players:
                await q.answer("❌ 你不是本局选手，无法落子。", show_alert=True); return
            if uid != game.current_uid():
                await q.answer("⌛ 还没轮到你，请稍等。", show_alert=True); return
            try:
                _, _, r, c = data.split("_")
                r, c = int(r), int(c)
            except ValueError: return
            ok, result = game.place(uid, r, c)
            if not ok: await q.answer(result, show_alert=True); return
            
            names = {p: await get_name(context.application, p) for p in game.players}
            if game.phase == "finished":
                await q.answer("落子成功，游戏结束")
                await settle_gomoku(game, context.application, names)
            else:
                await q.answer("落子成功")
                await update_gomoku_board(game, context.application, names)
            return
        if data.startswith("texas_"):
            game = active_poker_games.get(cid)
            if not game: await q.answer("德州游戏已结束", show_alert=True); return
            if data == "texas_hand":
                hand = game.hands.get(uid); await q.answer(f"你的手牌：{card_str(hand[0])}  {card_str(hand[1])}" if hand and uid not in game.folded else "当前无法查看手牌", show_alert=True); return
            if data == "texas_end":
                if uid != ADMIN_USER_ID and uid not in game.players:
                    await q.answer("权限不足", show_alert=True); return
                await refund_poker(game, context.application, "🛑 德州已终止，筹码已退回。")
                await q.answer("本局已终止")
                return
            if game.phase == "waiting":
                wallet = entertainment_chips if game.mode == "entertainment" else group_chips
                if data == "texas_join" and wallet[cid][uid] < MIN_ENTRY_CHIPS:
                    label = "娱乐筹码" if game.mode == "entertainment" else "筹码"
                    await q.answer(f"进入德州至少需要 {MIN_ENTRY_CHIPS} {label}", show_alert=True)
                elif data == "texas_join" and game.add(uid):
                    await q.answer("已加入"); await update_poker_waiting(game, context.application)
                    if len(game.players) >= 2:
                        game.cancel_wait()
                        await start_auto_game(game, context.application)
                elif data == "texas_start" and uid == game.owner_id and game.start():
                    await q.answer("游戏开始"); await update_poker_table(game, context.application); await start_turn_timer(game, context.application)
                else: await q.answer("无法执行此操作", show_alert=True)
                return
            if uid != game.current(): await q.answer("还没轮到你", show_alert=True); return
            action = {"texas_fold":"fold", "texas_check":"check", "texas_call":"call", "texas_allin":"allin"}.get(data); extra = 0
            if data.startswith("texas_raise_"):
                try: action, extra = "raise", int(data.rsplit("_", 1)[1])
                except ValueError: await q.answer("无效加注额", show_alert=True); return
            if not action: await q.answer("未知操作", show_alert=True); return
            ok, desc = game.action(uid, action, extra)
            if not ok: await q.answer(desc, show_alert=True); return
            await q.answer(desc); await safe_delete(context.bot, cid, game.action_msg_id); await action_notice(cid, context.application, uid, desc)
            if game.phase == "showdown": await settle_poker(game, context.application)
            else: await update_poker_table(game, context.application); await start_turn_timer(game, context.application)
            return
        if data.startswith("horsebet_"):
            race = active_horse_races.get(cid)
            try: _, horse, amount = data.split("_"); horse, amount = int(horse), int(amount)
            except ValueError: await q.answer("无效下注数据", show_alert=True); return
            if not race: await q.answer("赛马已结束", show_alert=True); return
            ok, desc = race.bet(uid, horse, amount)
            if not ok: await q.answer(desc, show_alert=True); return
            race.name_cache[uid] = await get_name(context.application, uid); await q.answer(desc); await action_notice(cid, context.application, uid, f"下注 {amount} 于 {HORSE_EMOJI[horse]}")
            await safe_edit(context.bot, cid, race.game_msg_id, await race.view(context.application), reply_markup=race.buttons())
            return

        if data.startswith("mine_"):
            game = active_minesweeper_games.get(cid)
            if not game: await q.answer("扫雷已结束", show_alert=True); return
            if data == "mine_join":
                if game.add(uid): 
                    await q.answer("已加入"); await update_mine_board(game, context.application, {})
                else: await q.answer("已在游戏中", show_alert=True)
                return
            if data == "mine_start":
                if uid != game.owner_id: await q.answer("仅发起人可开始", show_alert=True); return
                if game.start(): 
                    await q.answer("游戏开始"); await update_mine_board(game, context.application, {})
                else: await q.answer("需要至少1人", show_alert=True)
                return
            if data == "mine_end":
                if uid != ADMIN_USER_ID and uid not in game.players:
                    await q.answer("权限不足", show_alert=True); return
                active_minesweeper_games.pop(cid, None)
                await safe_edit(context.bot, cid, game.game_msg_id, "🛑 扫雷已手动终止。", reply_markup=None)
                await q.answer("已终止")
                return
            if data == "mine_rematch":
                if cid in active_minesweeper_games:
                    active_minesweeper_games.pop(cid, None)
                await cmd_sl(update, context); await q.answer("新局已开启")
                return
            if data.startswith("mine_rev_"):
                if game.phase != "playing": await q.answer("游戏未开始", show_alert=True); return
                # 修复权限 Bug：只有加入游戏的玩家才能点格子
                if uid not in game.players:
                    await q.answer("❌ 你未加入本局扫雷，无法操作。", show_alert=True); return
                try: _, _, r, c = data.split("_"); r, c = int(r), int(c)
                except ValueError: return
                ok, res = game.reveal(uid, r, c)
                if not ok: return
                names = {p: await get_name(context.application, p) for p in game.players}
                if game.phase == "finished":
                    # 扫雷结算消息也置底
                    await safe_delete(context.bot, cid, game.game_msg_id)
                    await safe_send_long(context.bot, cid, game.caption(names))
                    active_minesweeper_games.pop(cid, None)
                else:
                    await update_mine_board(game, context.application, names)
                await q.answer()
                return
    except Exception:
        logger.exception("按钮处理异常")


async def on_text(update, context):
    try:
        message, user = update.effective_message, update.effective_user
        if not message or not message.text or not user or user.is_bot: return
        if message.date and (datetime.now(timezone.utc) - message.date).total_seconds() > STALE_TEXT_COMMAND_SECONDS:
            return
        cid, text = update.effective_chat.id, message.text.strip()
        
        # 统一刷新逻辑
        if text in ["棋盘", "刷新", "看棋", "board", "qp"]:
            found = False
            # 1. 21点
            bj = active_blackjack_games.get(cid)
            if bj: found = True; await update_blackjack_ui(bj, context.application)
            # 2. 百家乐
            bjl = active_baccarat_games.get(cid)
            if bjl: found = True; await update_baccarat_ui(bjl, context.application)
            # 3. 德州
            poker = active_poker_games.get(cid)
            if poker:
                found = True
                await safe_delete(context.bot, cid, poker.game_msg_id)
                if poker.phase == "waiting":
                    msg = await safe_send(context.bot, cid, await poker_waiting_text(poker, context.application), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("加入游戏", callback_data="texas_join")], [InlineKeyboardButton("🛑 终止房间", callback_data="texas_end")]]))
                    if msg: poker.game_msg_id = msg.message_id
                else:
                    msg = await safe_send(context.bot, cid, await poker_table_text(poker, context.application))
                    if msg:
                        poker.game_msg_id = msg.message_id
                        # 恢复当前行动玩家的操作按钮，防止刷新后游戏卡死
                        await start_turn_timer(poker, context.application)
            # 4. 赛马
            race = active_horse_races.get(cid)
            if race and race.phase == "betting":
                found = True
                await safe_delete(context.bot, cid, race.game_msg_id)
                msg = await safe_send(context.bot, cid, await race.view(context.application), reply_markup=race.buttons())
                if msg: race.game_msg_id = msg.message_id
            # 5. 五子棋
            gomoku = active_gomoku_games.get(cid)
            if gomoku:
                found = True
                gnames = {p: await get_name(context.application, p) for p in gomoku.players}
                await update_gomoku_board(gomoku, context.application, gnames)
            # 6. 扫雷
            mine = active_minesweeper_games.get(cid)
            if mine:
                found = True
                mnames = {p: await get_name(context.application, p) for p in mine.players}
                await update_mine_board(mine, context.application, mnames)
            if not found: await message.reply_text("💡 当前没有任何正在进行的游戏。")
            return

        # 百家乐文字下注
        baccarat = active_baccarat_games.get(cid)
        bjl_match = re.fullmatch(r"(?:押|下|买)?(庄|闲|和)\s*(\d+)", text)
        if bjl_match and baccarat:
            if baccarat.phase != "betting":
                await message.reply_text("❌ 百家乐当前不在下注阶段。"); return
            side_map = {"庄": "banker", "闲": "player", "和": "tie"}
            side_cn = bjl_match.group(1); side = side_map[side_cn]
            amount = int(bjl_match.group(2))
            wallet = entertainment_chips if baccarat.mode == "entertainment" else group_chips
            if wallet[cid][user.id] < amount:
                await message.reply_text(f"❌ 筹码不足，你只有 {wallet[cid][user.id]}。"); return
            if amount > 50000:
                await message.reply_text("❌ 百家乐单次下注上限为 50000 积分。"); return
            wallet[cid][user.id] -= amount
            baccarat.place_bet(user.id, side, amount)
            await action_notice(cid, context.application, user.id, f"在百家乐押注了 {side_cn} {amount}")
            await update_baccarat_ui(baccarat, context.application)
            return

        # 21点文字加入
        blackjack = active_blackjack_games.get(cid)
        bj_match = re.fullmatch(r"(?:下注|下|押|买)?(?:21点|21)\s*(\d+)", text)
        if bj_match and blackjack:
            if blackjack.phase != "waiting":
                await message.reply_text("❌ 21点已经开始，请等待下一局。"); return
            amount = int(bj_match.group(1))
            if amount < BJ_MIN_BET:
                await message.reply_text(f"❌ 21点最低下注 {BJ_MIN_BET} 积分。"); return
            wallet = entertainment_chips if blackjack.mode == "entertainment" else group_chips
            if wallet[cid][user.id] < amount:
                await message.reply_text(f"❌ 筹码不足，你只有 {wallet[cid][user.id]}。"); return
            if blackjack.add_player(user.id, amount):
                wallet[cid][user.id] -= amount
                await action_notice(cid, context.application, user.id, f"加入了 21点，下注 {amount}")
                await update_blackjack_ui(blackjack, context.application)
            else: await message.reply_text("❌ 你已在局中或无法加入。")
            return

        # 赛马与德州传统匹配
        match = re.fullmatch(r"下注\s+(\d+)\s+(\d+)", text); race = active_horse_races.get(cid)
        if match and race:
            horse, amount = int(match.group(1))-1, int(match.group(2))
            ok, desc = race.bet(user.id, horse, amount)
            if not ok: await message.reply_text(f"❌ {desc}"); return
            race.name_cache[user.id] = await get_name(context.application, user.id)
            await action_notice(cid, context.application, user.id, f"下注 {amount} 于 {HORSE_EMOJI[horse]}")
            await safe_edit(context.bot, cid, race.game_msg_id, await race.view(context.application), reply_markup=race.buttons())
            return

        # 五子棋
        gomoku = active_gomoku_games.get(cid)
        match = re.fullmatch(r"(?:落子\s+)?(?:(\d{1,2})\s*(?:[,，]\s*|\s+)(\d{1,2})|(\d)(\d))", text)
        if match and gomoku:
            r = int(match.group(1)) if match.group(1) is not None else int(match.group(3))
            c = int(match.group(2)) if match.group(2) is not None else int(match.group(4))
            ok, result = gomoku.place(user.id, r, c)
            if not ok: await message.reply_text(f"❌ {result}"); return
            names = {player: await get_name(context.application, player) for player in gomoku.players}
            if gomoku.phase == "finished": await settle_gomoku(gomoku, context.application, names)
            else: await update_gomoku_board(gomoku, context.application, names)
            return

        # 德州加注
        poker_match = re.fullmatch(r"(?:下注|加注)\s*[:：]?\s*(\d+)\s*(?:积分)?", text); poker = active_poker_games.get(cid)
        if poker_match and poker:
            if poker.phase == "waiting": await message.reply_text("❌ 德州还未开始。"); return
            if user.id != poker.current(): await message.reply_text("❌ 还没轮到你。"); return
            ok, desc = poker.action(user.id, "raise", int(poker_match.group(1)))
            if not ok: await message.reply_text(f"❌ {desc}"); return
            await action_notice(cid, context.application, user.id, desc)
            if poker.phase == "showdown": await settle_poker(poker, context.application)
            else: await update_poker_table(poker, context.application); await start_turn_timer(poker, context.application)
            return
    except Exception:
        logger.exception("文本指令处理异常")


# ---------- 定时任务与启动 ----------
async def daily_reset_scheduler(app):
    global last_business_date
    today = now_bj().strftime("%Y-%m-%d")
    # 第一次启动只记录业务日，避免因部署重启立刻重置玩家筹码。
    if not last_business_date:
        last_business_date = today; save_data()
    while True:
        now = now_bj(); target = (now + timedelta(days=1)).replace(hour=0, minute=0, second=1, microsecond=0)
        await asyncio.sleep((target-now).total_seconds())
        today = now_bj().strftime("%Y-%m-%d")
        # 午夜清理专项榜单数据
        poker_profit_by_date.clear()
        race_profit_by_date.clear()
        blackjack_profit_by_date.clear()
        baccarat_profit_by_date.clear()
        slot_profit_by_date.clear()
        # 午夜先取消娱乐局并退款，避免娱乐局跨日结算后写回娱乐钱包。

        for poker in list(active_poker_games.values()):
            if poker.mode == "entertainment":
                await refund_poker(poker, app, "🕛 娱乐时段结束，本局娱乐筹码已退回。")
        for race in list(active_horse_races.values()):
            if race.mode == "entertainment":
                if race.task and not race.task.done():
                    race.task.cancel()
                    await asyncio.gather(race.task, return_exceptions=True)
                await race.refund(app, "🕛 娱乐时段结束，本局娱乐筹码已退回。")
        entertainment_chips.clear()
        # 不重置正在进行正式德州或赛马中的玩家，避免跨日覆盖未结算状态。
        protected = set()
        for poker in active_poker_games.values():
            if poker.phase != "waiting":
                protected.update((poker.chat_id, uid) for uid in poker.players)
        for race in active_horse_races.values():
            if race.phase in {"betting", "racing", "settling"}:
                protected.update((race.chat_id, uid) for uid in race.bets)
        for bj in active_blackjack_games.values():
            if bj.phase != "waiting":
                protected.update((bj.chat_id, uid) for uid in bj.players)
        for bjl in active_baccarat_games.values():
            if bjl.phase == "betting":
                protected.update((bjl.chat_id, uid) for uid in bjl.bets)
        for chat_id, users in group_chips.items():
            for uid in users:
                if (chat_id, uid) not in protected:
                    users[uid] = STARTING_CHIPS
        for cid in race_daily_stats: race_daily_stats[cid] = [0] * HORSE_COUNT
        for cid in baccarat_daily_stats: baccarat_daily_stats[cid] = {"player": 0, "banker": 0, "tie": 0}
        daily_emergency_used.clear(); last_business_date = today; save_data()

async def leaderboard_scheduler(app):
    while True:
        now = now_bj(); target = now.replace(hour=23, minute=0, second=0, microsecond=0)
        if target <= now: target += timedelta(days=1)
        await asyncio.sleep((target-now).total_seconds())
        date = now_bj().strftime("%Y-%m-%d"); snapshot = profit_by_date.pop(date, {})
        poker_profit_by_date.pop(date, None); race_profit_by_date.pop(date, None)
        blackjack_profit_by_date.pop(date, None); baccarat_profit_by_date.pop(date, None)
        slot_profit_by_date.pop(date, None)
        for cid, data in snapshot.items():
            if not data: continue
            lines = [f"🏆 今日综合排行榜（{date}）", "━"*14]
            for i, (uid, amount) in enumerate(sorted(data.items(), key=lambda x:x[1], reverse=True)[:10], 1): lines.append(f"{rank_marker(i)} {await get_name(app, uid)}：{amount:+d}")
            await safe_send_long(app.bot, cid, "\n".join(lines))
        save_data()

async def hourly_race_scheduler(app):
    last_key = None
    while True:
        now = now_bj(); key = now.strftime("%Y%m%d%H")
        if now.minute == 0 and key != last_key:
            last_key = key
            for cid, enabled in list(hourly_race_enabled.items()):
                if not enabled or cid in active_horse_races: continue
                mode = current_game_mode()
                jackpot = race_jackpot.pop(cid, 0) if mode == "official" else 0
                race = HorseRace(cid, ADMIN_USER_ID, jackpot, mode); active_horse_races[cid] = race
                msg = await safe_send(app.bot, cid, await race.view(app), reply_markup=race.buttons())
                if msg: race.game_msg_id = msg.message_id
                race.task = asyncio.create_task(race.run(app)); save_data()
        next_minute = (now + timedelta(minutes=1)).replace(second=0, microsecond=0)
        await asyncio.sleep(max(1, (next_minute-now).total_seconds()))

async def post_init(app):
    background_tasks.update({
        asyncio.create_task(daily_reset_scheduler(app)), 
        asyncio.create_task(leaderboard_scheduler(app)), 
        asyncio.create_task(hourly_race_scheduler(app)),
        asyncio.create_task(data_save_worker()) 
    })


async def post_shutdown(app):
    force_save_now()


def main():
    global save_event
    token = os.environ.get("BOT_TOKEN")
    if not token: logger.error("未设置 BOT_TOKEN"); return
    
    # 在主循环启动前初始化 Event
    save_event = asyncio.Event()
    
    app = Application.builder().token(token).post_init(post_init).post_shutdown(post_shutdown).build()

    for command, handler in [("start",cmd_start),("dz",cmd_dz),("sm",cmd_sm),("wz",cmd_wz),("sl",cmd_sl),("lhj",cmd_lhj),("21",cmd_21),("bjl",cmd_bjl),("gomoku",cmd_wz),("end",cmd_end),("END",cmd_end),("add",cmd_add),("reduce",cmd_reduce),("cx",cmd_cx),("ph",cmd_ph),("sq",cmd_sq),("qxshouquan",cmd_qxshouquan),("autosm",cmd_autosm)]: app.add_handler(CommandHandler(command, handler))
    app.add_handler(CallbackQueryHandler(on_button)); app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)

if __name__ == "__main__": main()
