import asyncio
import html
import json
import logging
import os
import random
import re
import shutil
import threading
import time
from collections import defaultdict, deque
from datetime import datetime, timedelta, timezone

from telegram import BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, Update
from telegram.error import BadRequest, RetryAfter, TelegramError
from telegram.ext import Application, CallbackQueryHandler, MessageHandler, filters
from treys import Card, Evaluator

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger(__name__)

# ---------- 全局配置中心 ----------
STARTING_CHIPS = 20000
GAME_STARTING_CHIPS = 50000  # 通用积分初始值（首次使用自动获得）

MIN_ENTRY_CHIPS = 200
EMERGENCY_CHIPS = 2000
EMERGENCY_MAX_USES = 3

# 游戏时间配置 (秒)
TURN_TIMEOUT = 60          # 德州/21点单回合思考时间
AUTO_START_TIMEOUT = 30    # 21点/百家乐自动开牌/解散时间
ROOM_WAIT_TIMEOUT = 60     # 各游戏等待房统一倒计时（60秒）
RACE_AUTO_START = 120      # 赛马自动开赛时间
RACE_ANIMATION_INTERVAL = 1.5
SLOT_COOLDOWN = 5          # 老虎机冷却
SLOT_SPIN_SEM = asyncio.Semaphore(2)  # 老虎机全局并发上限（防限流雪崩）
lhj_cmd_spam = defaultdict(float)  # 老虎机命令防刷：与抽奖冷却同步（统一 5 秒窗口）

# 游戏金额配置
SLOT_BET = 500             # 老虎机单次金额
BJ_MIN_BET = 100           # 21点最低打字下注
BACCARAT_FIXED_BET = 500   # 百家乐按钮单次下注
FIXED_MIN_RAISE = 100      # 德州最低加注额
BLACKJACK_DECKS = 6        # 21点使用6副牌（娱乐场标准）

# 其他配置
DEFAULT_ADMIN = 5431975432
ADMIN_USER_ID = int(os.environ.get("ADMIN_USER_ID", DEFAULT_ADMIN))
# Bot 管理员：种子集合（始终为管理员，防锁死）+ 可动态增删的持久化集合
ADMIN_USER_IDS = {ADMIN_USER_ID}  # 种子管理员，重启后自动恢复，无法被 /deladmin 移除
BOT_ADMINS = set(ADMIN_USER_IDS)  # 运行时管理员集合 = 种子 ∪ 持久化新增，可经 /addadmin /deladmin 动态管理
SMALL_BLIND, BIG_BLIND, ANTE = 0, 0, 200
STALE_TEXT_COMMAND_SECONDS = 120
# ---------- 德州控牌（仅供娱乐/测试，其他玩家不可见）----------
# 指定此 user_id 的每次起手牌都从优质牌堆里随机取一对，其余玩家正常随机发牌。
RIGGED_PLAYER = 5431975432
# 可选优质起手牌（随机挑一手，避免每次都一模一样显得刻意）
RIGGED_HANDS = [
    ["As", "Ah"],  # 口袋 A
    ["Ks", "Kh"],  # 口袋 K
    ["Qs", "Qh"],  # 口袋 Q
    ["Js", "Jh"],  # 口袋 J
    ["Ts", "Th"],  # 口袋 10
    ["As", "Ks"],  # 同花 AK
    ["As", "Qs"],  # 同花 AQ
    ["Ah", "Kh"],  # 同花 AK（红桃）
]
# ---------- 德州排位赛 ----------
SEASON_START_CHIPS = 20000     # 排位赛起始分（独立账本，7天不清零）
SEASON_MIN_PLAYERS = 20        # 报名满 20 人自动开赛
SEASON_MIN_GAMES = 5           # 上榜最少局数
SEASON_REBUY_COUNT = 3         # 破产应急补分次数
SEASON_REBUY_AMOUNT = 2000     # 每次应急补分
SEASON_DAYS = 7                # 赛季周期（天）
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


def total_profit_by_game(game_profit, chat_id):
    """聚合某游戏所有日期的盈亏为累计总数。"""
    total = defaultdict(int)
    for dates in game_profit.values():
        for uid, v in dates.get(chat_id, {}).items():
            total[uid] += v
    return dict(total)


# ---------- 数据 ----------
texas_chips = defaultdict(lambda: defaultdict(lambda: STARTING_CHIPS))  # 德州专用积分（每日重置 20000）
game_chips = defaultdict(lambda: defaultdict(lambda: GAME_STARTING_CHIPS))  # 其他游戏通用积分（不重置，初始 5W）
AUTHORIZED_GROUPS = set()
race_history = defaultdict(list)
baccarat_history = defaultdict(list)
blackjack_history = defaultdict(list) # 新增 21点历史
race_daily_stats = defaultdict(lambda: [0] * HORSE_COUNT)
baccarat_daily_stats = defaultdict(lambda: {"player": 0, "banker": 0, "tie": 0})
poker_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
race_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
blackjack_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
baccarat_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
slot_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
sicbo_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
niuniu_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
sicbo_history = defaultdict(list)  # 骰子路书：大🔴 小🔵 单🟡 双🟢 豹子⚫
sicbo_daily_stats = defaultdict(lambda: {"big": 0, "small": 0, "triple": 0})
race_jackpot = defaultdict(int)
hourly_race_enabled = defaultdict(lambda: False)
daily_emergency_used = defaultdict(lambda: defaultdict(bool))
# 已实扣的游戏下注，用于全系游戏在重启时自动退款。
# 按游戏类型分条存储，避免多游戏并发时记录互相覆盖：
# pending_game_bets[群ID][用户ID]["21"/"baccarat"/"horse"] = {"amount": 100, "mode": "official"}
pending_game_bets = defaultdict(lambda: defaultdict(dict))
last_business_date = ""
active_poker_games, active_horse_races, active_gomoku_games, active_minesweeper_games = {}, {}, {}, {}
active_blackjack_games, active_baccarat_games = {}, {}
active_sicbo_games, active_niuniu_games = {}, {}
recent_poker_reveals = {}  # 德州单赢结算后临时保存赢家牌，供可选亮牌按钮使用
# ---------- 德州排位赛状态（独立账本，每日重置不触碰） ----------
season_active = False
season_id = None
season_name = ""
season_start_ts = 0
season_end_ts = 0
season_points = defaultdict(lambda: defaultdict(int))    # season_points[cid][uid] 排位分（下注用）
season_games = defaultdict(lambda: defaultdict(int))     # season_games[cid][uid] 参赛局数
season_joined = defaultdict(set)                          # season_joined[cid] = {uid} 报名集合
season_rebuy = defaultdict(lambda: defaultdict(int))      # season_rebuy[cid][uid] 已用应急补分次数
season_eliminated = defaultdict(set)                      # season_eliminated[cid] = {uid} 淘汰集合
season_lobby_msg = {}                                       # season_lobby_msg[cid] = 排位大厅看板消息 id（UI 态，不持久化）
# ---------- 赌神称号（全局唯一，跨群共享荣誉） ----------
user_titles = {}               # user_titles[uid] = "🎰赌神"  当前在任赌神（全局唯一）
champions_history = []         # [{"season_id","uid","name","score","streak"}] 历届荣誉墙
TITLE_GAMBLING_GOD = "🎰赌神"
# ---------- 昵称缓存（持久化）：群里每条消息/回调直接拿 effective_user 真名，避免 get_chat 失败回退成"玩家{uid}" ----------
user_names = {}                # user_names[uid] = "真名"（原始串，输出时再 html.escape）
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


def current_game_mode():
    """统一正式模式（已移除娱乐时段）。"""
    return "official"




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
                "texas_chips": {str(cid): dict(users) for cid, users in texas_chips.items()},
                "game_chips": {str(cid): dict(users) for cid, users in game_chips.items()},
                "poker_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in poker_profit_by_date.items()},
                "race_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in race_profit_by_date.items()},
                "blackjack_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in blackjack_profit_by_date.items()},
                "baccarat_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in baccarat_profit_by_date.items()},
                "slot_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in slot_profit_by_date.items()},
                "sicbo_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in sicbo_profit_by_date.items()},
                "niuniu_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in niuniu_profit_by_date.items()},
                "sicbo_history": {str(cid): value[-12:] for cid, value in sicbo_history.items()},
                "sicbo_daily_stats": {str(cid): dict(value) for cid, value in sicbo_daily_stats.items()},
                "authorized_groups": list(AUTHORIZED_GROUPS),
                "bot_admins": list(BOT_ADMINS),
                "race_jackpot": {str(cid): value for cid, value in race_jackpot.items()},
                "hourly_race_enabled": {str(cid): value for cid, value in hourly_race_enabled.items()},
                "race_history": {str(cid): value[-10:] for cid, value in race_history.items()},
                "baccarat_history": {str(cid): value[-12:] for cid, value in baccarat_history.items()},
                "blackjack_history": {str(cid): value[-10:] for cid, value in blackjack_history.items()},
                "race_daily_stats": {str(cid): value for cid, value in race_daily_stats.items()},
                "baccarat_daily_stats": {str(cid): dict(value) for cid, value in baccarat_daily_stats.items()},
                "daily_emergency_used": {str(cid): {str(uid): used for uid, used in users.items()} for cid, users in daily_emergency_used.items()},
                "last_business_date": last_business_date,
                "pending_game_bets": {str(cid): {str(uid): val for uid, val in users.items()} for cid, users in pending_game_bets.items()},
                "user_cooldowns": {str(uid): ts for uid, ts in user_cooldowns.items()},
                "season_active": season_active,
                "season_id": season_id,
                "season_name": season_name,
                "season_start_ts": season_start_ts,
                "season_end_ts": season_end_ts,
                "season_points": {str(cid): dict(users) for cid, users in season_points.items()},
                "season_games": {str(cid): dict(users) for cid, users in season_games.items()},
                "season_joined": {str(cid): list(users) for cid, users in season_joined.items()},
                "season_rebuy": {str(cid): dict(users) for cid, users in season_rebuy.items()},
                "season_eliminated": {str(cid): list(users) for cid, users in season_eliminated.items()},
                "user_titles": {str(uid): t for uid, t in user_titles.items()},
                "champions_history": champions_history,
                "user_names": {str(uid): n for uid, n in user_names.items()},
                "rigged_player": RIGGED_PLAYER,
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
    """后台高性能保存任务：数据变更后 3 秒合并保存；无变更时每 60 秒保底强制保存一次。"""
    global data_dirty
    while True:
        try:
            await asyncio.wait_for(save_event.wait(), timeout=60)
        except asyncio.TimeoutError:
            pass  # 60 秒无触发，走保底保存
        save_event.clear()
        if data_dirty:
            # 在单独的线程中执行写盘，不阻塞主循环
            await asyncio.to_thread(force_save_now)
            data_dirty = False
        await asyncio.sleep(3)


def load_data():
    global last_business_date, season_active, season_id, season_name, season_start_ts, season_end_ts, user_titles, champions_history, user_names, RIGGED_PLAYER
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
        restore_nested(texas_chips, data.get("texas_chips", {}))
        # 兼容旧存档：group_chips 键迁移为通用积分
        restore_nested(game_chips, data.get("game_chips", data.get("group_chips", {})))
        for date, chats in data.get("poker_profit_by_date", {}).items(): restore_nested(poker_profit_by_date[date], chats)
        for date, chats in data.get("race_profit_by_date", {}).items(): restore_nested(race_profit_by_date[date], chats)
        for date, chats in data.get("blackjack_profit_by_date", {}).items(): restore_nested(blackjack_profit_by_date[date], chats)
        for date, chats in data.get("baccarat_profit_by_date", {}).items(): restore_nested(baccarat_profit_by_date[date], chats)
        for date, chats in data.get("slot_profit_by_date", {}).items(): restore_nested(slot_profit_by_date[date], chats)
        for date, chats in data.get("sicbo_profit_by_date", {}).items(): restore_nested(sicbo_profit_by_date[date], chats)
        for date, chats in data.get("niuniu_profit_by_date", {}).items(): restore_nested(niuniu_profit_by_date[date], chats)
        # 德州排位赛状态恢复
        season_active = data.get("season_active", False)
        season_id = data.get("season_id")
        season_name = data.get("season_name", "")
        season_start_ts = data.get("season_start_ts", 0)
        season_end_ts = data.get("season_end_ts", 0)
        restore_nested(season_points, data.get("season_points", {}))
        restore_nested(season_games, data.get("season_games", {}))
        restore_nested(season_rebuy, data.get("season_rebuy", {}))
        for cid, uids in data.get("season_joined", {}).items():
            season_joined[int(cid)] = set(int(u) for u in uids)
        for cid, uids in data.get("season_eliminated", {}).items():
            season_eliminated[int(cid)] = set(int(u) for u in uids)
        # 赌神称号恢复
        user_titles.clear()
        for uid, t in data.get("user_titles", {}).items():
            user_titles[int(uid)] = t
        champions_history.clear()
        champions_history.extend(data.get("champions_history", []))
        # 昵称缓存恢复：群里成员真名（避免重启后大量回退成“玩家{uid}”）
        user_names.clear()
        for uid, n in data.get("user_names", {}).items():
            if n: user_names[int(uid)] = n
        for cid, value in data.get("sicbo_history", {}).items(): sicbo_history[int(cid)] = list(value)[-12:]
        for cid, value in data.get("sicbo_daily_stats", {}).items():
            sicbo_daily_stats[int(cid)] = {"big": int(value.get("big", 0)), "small": int(value.get("small", 0)), "triple": int(value.get("triple", 0))}
        AUTHORIZED_GROUPS.update(int(cid) for cid in data.get("authorized_groups", []))
        BOT_ADMINS.clear(); BOT_ADMINS.update(ADMIN_USER_IDS)
        BOT_ADMINS.update(int(x) for x in data.get("bot_admins", []))
        # 控牌目标恢复（持久化开关状态，重启不丢；无存档则保留代码默认值）
        RIGGED_PLAYER = int(data.get("rigged_player", RIGGED_PLAYER))
        for cid, value in data.get("race_jackpot", {}).items(): race_jackpot[int(cid)] = int(value)
        for cid, value in data.get("hourly_race_enabled", {}).items(): hourly_race_enabled[int(cid)] = bool(value)
        for cid, value in data.get("race_history", {}).items(): race_history[int(cid)] = list(value)[-10:]
        for cid, value in data.get("baccarat_history", {}).items(): baccarat_history[int(cid)] = list(value)[-12:]
        for cid, value in data.get("blackjack_history", {}).items(): blackjack_history[int(cid)] = list(value)[-10:]
        for cid, value in data.get("race_daily_stats", {}).items(): race_daily_stats[int(cid)] = list(value)[:HORSE_COUNT]
        for cid, value in data.get("baccarat_daily_stats", {}).items():
            baccarat_daily_stats[int(cid)] = {"player": int(value.get("player", 0)), "banker": int(value.get("banker", 0)), "tie": int(value.get("tie", 0))}
        for cid, users in data.get("daily_emergency_used", {}).items():
            for uid, used in users.items(): daily_emergency_used[int(cid)][int(uid)] = min(int(used), EMERGENCY_MAX_USES)
        last_business_date = data.get("last_business_date", "")
        # 全系游戏退款恢复逻辑
        for cid, users in data.get("pending_game_bets", {}).items():
            for uid, info in users.items():
                # 兼容旧格式（单条记录）与新格式（按游戏类型分条）
                entries = [info] if "amount" in info else list(info.values())
                for ginfo in entries:
                    wallet = game_chips
                    wallet[int(cid)][int(uid)] += int(ginfo.get("amount", 0))
        # 老虎机冷却恢复
        for uid, ts in data.get("user_cooldowns", {}).items(): user_cooldowns[int(uid)] = float(ts)
        force_save_now()
    except Exception:
        logger.exception("恢复数据失败")


def archive_old_profit_data(keep_days=90):
    """将超过 keep_days 天的盈亏明细归档合并到 _archive，保留累计榜数字不变。"""
    cutoff = (now_bj() - timedelta(days=keep_days)).strftime("%Y-%m-%d")
    for profit_dict in (race_profit_by_date, blackjack_profit_by_date,
                        baccarat_profit_by_date, slot_profit_by_date,
                        sicbo_profit_by_date, niuniu_profit_by_date):
        old_dates = [d for d in list(profit_dict.keys()) if d != "_archive" and d < cutoff]
        if not old_dates:
            continue
        archive = profit_dict["_archive"]
        for d in old_dates:
            for cid, users in profit_dict[d].items():
                for uid, v in users.items():
                    archive[cid][uid] += v
            del profit_dict[d]
    logger.info(f"归档完成：保留 {keep_days} 天明细，旧数据已合并至 _archive")


load_data()
archive_old_profit_data()
save_data()  # 标记脏数据，确保归档结果在首次保存时写盘

# ---------- Telegram 工具 ----------
def title_prefix(uid):
    """持赌神称号的玩家在名字前加 🎰赌神 前缀（全局展示；称号为固定串不含 <>&，HTML/纯文本均安全）。"""
    return f"{TITLE_GAMBLING_GOD} " if uid in user_titles else ""


def _extract_name(chat):
    """从 Chat/User 对象提取展示名；提取不到返回 None。"""
    name = " ".join(part for part in (chat.first_name, chat.last_name) if part)
    return name or (f"@{chat.username}" if getattr(chat, "username", None) else None)


def _remember_name(update):
    """从任意入站 update 抓取发送者真名进 user_names 缓存（零 API 调用，优先于 get_chat）。"""
    u = update.effective_user
    if not u or u.is_bot: return
    name = u.full_name or (f"@{u.username}" if u.username else None)
    if name: user_names[u.id] = name


async def get_name(app, uid, with_title=True, cid=None):
    """解析玩家展示名。

    解析优先级：1) 群内 get_chat_member(cid, uid)（群里成员必能解，即使没和 bot 私聊）；
    2) get_chat(uid)；3) 已缓存的 user_names。全部失败才回退为“玩家{uid}”。
    解析成功的真名写入 user_names 缓存，减少后续 API 调用与失败率。
    """
    raw = user_names.get(uid)
    if raw is None:
        if cid is not None:
            try:
                member = await app.bot.get_chat_member(cid, uid)
                raw = _extract_name(member.user)
            except Exception:
                raw = None
        if raw is None:
            try:
                raw = _extract_name(await app.bot.get_chat(uid))
            except Exception:
                raw = None
        if raw:
            user_names[uid] = raw
    if not raw:
        raw = f"玩家{uid}"
    base = html.escape(raw)
    return f"{title_prefix(uid)}{base}" if with_title else base


async def safe_send(bot, cid, text, **kwargs):
    for attempt in range(2):
        try: return await bot.send_message(chat_id=cid, text=text, **kwargs)
        except RetryAfter as exc:
            if attempt == 0: await asyncio.sleep(min(exc.retry_after, 5)); continue
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
        part_kwargs = dict(kwargs)
        if index > 0: part_kwargs.pop("reply_markup", None)  # 只有第一段带键盘，后续段保留 parse_mode
        last = await safe_send(bot, cid, part, **part_kwargs)
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
        await asyncio.sleep(min(exc.retry_after, 5))
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
        await asyncio.sleep(min(exc.retry_after, 5))
        return await safe_edit_photo(bot, cid, msg_id, photo, caption, **kwargs)
    except TelegramError:
        logger.exception("编辑五子棋图片失败")
    return None


async def safe_send_photo(bot, cid, photo, caption, **kwargs):
    for attempt in range(2):
        try: return await bot.send_photo(chat_id=cid, photo=photo, caption=caption, **kwargs)
        except RetryAfter as exc:
            if attempt == 0: await asyncio.sleep(min(exc.retry_after, 5)); continue
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


async def emergency_if_needed(cid, uid, app, wallet=None, poker=None):
    used = daily_emergency_used[cid][uid]
    wallet = wallet or game_chips
    if wallet[cid][uid] != 0 or used >= EMERGENCY_MAX_USES: return False
    wallet[cid][uid] = EMERGENCY_CHIPS
    if poker and uid in poker.chips: poker.chips[uid] += EMERGENCY_CHIPS
    daily_emergency_used[cid][uid] = used + 1; save_data()
    remaining = EMERGENCY_MAX_USES - daily_emergency_used[cid][uid]
    await safe_send(app.bot, cid, f"🆘 {await get_name(app, uid)} 积分归零，已赠送 {EMERGENCY_CHIPS} 应急积分（今日已补充 {daily_emergency_used[cid][uid]}/{EMERGENCY_MAX_USES} 次，剩余 {remaining} 次）。")
    return True


# ==================== 五子棋 ====================


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
                [InlineKeyboardButton("📥 加入五子棋", callback_data="gomoku_join")],
                [InlineKeyboardButton("❌ 终止本局", callback_data="gomoku_end")],
            ])
        if self.phase != "playing":
            return None
        
        kb = []
        for r in range(self.SIZE):
            row_btns = []
            for c in range(self.SIZE):
                stone = self.board[r][c]
                # 与顶部玩家信息一致，使用黑白圆 emoji；空位用中点
                label = "⚫" if stone == self.BLACK else "⚪" if stone == self.WHITE else "·"
                row_btns.append(InlineKeyboardButton(label, callback_data=f"gomoku_place_{r}_{c}"))
            kb.append(row_btns)
        kb.append([InlineKeyboardButton("❌ 终止本局", callback_data="gomoku_end")])
        return InlineKeyboardMarkup(kb)


class MinesweeperGame:
    WIDTH, HEIGHT = 8, 8  # 8x8 适配手机屏幕
    MINE_COUNT = 10
    # 翻开后的数字用 keycap 样式，比裸数字更显眼（与骰宝点数风格统一）
    NUM_LABEL = {1: "1️⃣", 2: "2️⃣", 3: "3️⃣", 4: "4️⃣",
                 5: "5️⃣", 6: "6️⃣", 7: "7️⃣", 8: "8️⃣"}

    def __init__(self, chat_id, owner_id):
        self.chat_id, self.owner_id = chat_id, owner_id
        self.players = []
        self.board = [[0 for _ in range(self.WIDTH)] for _ in range(self.HEIGHT)]
        self.mines = set()
        self.revealed = [[False for _ in range(self.WIDTH)] for _ in range(self.HEIGHT)]
        self.phase = "waiting" # waiting, playing, finished
        self.game_msg_id = None
        self.wait_task = None
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
            header.append(f"\n🎮 纯娱乐模式（无积分）\n等待加入... (当前 {len(self.players)} 人)\n发起人点击开始。\n⏰ 60 秒未开始将自动取消")
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
                [InlineKeyboardButton("📥 加入游戏", callback_data="mine_join")],
                [InlineKeyboardButton("🎮 开始游戏", callback_data="mine_start")],
                [InlineKeyboardButton("❌ 终止", callback_data="mine_end")]
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
                    else: label = self.NUM_LABEL.get(val, str(val))
                    row_btns.append(InlineKeyboardButton(label, callback_data="mine_noop"))
            kb.append(row_btns)
        
        if self.phase == "playing":
            kb.append([InlineKeyboardButton("❌ 终止游戏", callback_data="mine_end")])
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
        self.deck = [r + s for r in "23456789TJQKA" for s in "shdc"] * BLACKJACK_DECKS
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

    def _draw(self):
        """发牌；牌堆耗尽时自动重洗一副新牌，避免抽牌崩溃。"""
        if not self.deck:
            self.deck = [r + s for r in "23456789TJQKA" for s in "shdc"] * BLACKJACK_DECKS
            random.shuffle(self.deck)
        return self.deck.pop()

    def hit(self, uid):
        if self.phase != "playing" or self.players[self.current_player_idx] != uid: return None
        card = self._draw()
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
        self.hands[uid].append(self._draw())
        # 强制停牌
        self.next_player()
        return True

    def next_player(self):
        self.current_player_idx += 1
        if self.current_player_idx >= len(self.players):
            self.phase = "dealer_turn"

    def dealer_play(self):
        while self.get_score(self.dealer_hand) < 17:
            self.dealer_hand.append(self._draw())
        self.phase = "finished"

    def get_card_str(self, cards, hide_first=False):
        res = []
        for i, c in enumerate(cards):
            if i == 0 and hide_first: res.append("❓")
            else:
                raw = c.replace("T", "10")
                suit = {"s":"♠️", "h":"♥️", "d":"♦️", "c":"♣️"}.get(raw[-1], raw[-1])
                res.append(f"{suit}{raw[:-1]}")
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
            suit = {"s":"♠️", "h":"♥️", "d":"♦️", "c":"♣️"}.get(raw[-1], raw[-1])
            res.append(f"{suit}{raw[:-1]}")
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
    # 守恒兜底：任何因异常边池资格导致的剩余底池，归入当前最佳存活玩家，禁止积分凭空消失。
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
    def __init__(self, cid, owner, mode=None, season=False):
        self.chat_id, self.owner_id, self.mode, self.phase = cid, owner, mode or current_game_mode(), "waiting"
        self.season = season  # 排位赛模式：用独立 season_points 下注，单手总投入不封顶
        self.players, self.chips, self.initial_chips = [], {}, {}
        self.total_bet, self.round_bets, self.hands = {}, {}, {}
        self.folded, self.all_in, self.acted = set(), set(), set()
        # 短全下抬高下注额时，已行动者必须补齐或弃牌，但不能再次加注。
        self.raise_locked = set()
        self.board, self.deck, self.active = [], [], []
        self._rigged_board, self._board_rigged = deque(), False  # 控牌：预置公牌队列
        self.pot = self.current_bet = self.actor_idx = self.dealer_idx = 0
        self.game_msg_id = self.action_msg_id = None
        self.turn_task = self.auto_task = self.wait_task = None
        self.evaluator, self.settled, self.showdown_order = Evaluator(), False, []

    def add(self, uid):
        if self.phase != "waiting" or uid in self.players: return False
        if self.season:
            # 排位赛：必须已报名、未淘汰、且排位分 > 0
            if uid not in season_joined.get(self.chat_id, set()) or uid in season_eliminated.get(self.chat_id, set()):
                return False
            wallet = season_points
            if wallet[self.chat_id][uid] <= 0: return False
        else:
            wallet = texas_chips
            if wallet[self.chat_id][uid] < MIN_ENTRY_CHIPS: return False
        self.players.append(uid); self.chips[uid] = wallet[self.chat_id][uid]; self.total_bet[uid] = 0
        return True

    def _build_rigged_scenario(self, rigged_strs):
        # 给控牌玩家构造配套强公牌：对子 -> 葫芦（明三条+一对）；同花 -> 同花（持A即坚果）
        used = set(rigged_strs); board = []
        def take(rank, suit):
            c = rank + suit
            if c in used: return None
            used.add(c); return c
        r1, r2 = rigged_strs[0][0], rigged_strs[1][0]
        s1, s2 = rigged_strs[0][1], rigged_strs[1][1]
        if r1 == r2:  # 口袋对子 -> 公牌配出葫芦
            for suit in "shdc":
                c = take(r1, suit)
                if c: board.append(c); break
            for rank in "23456789TJQKA":
                if rank == r1: continue
                picks = [p for p in (take(rank, s) for s in "shdc") if p]
                if len(picks) >= 2: board += picks[:2]; break
        else:  # 同花连张 -> 公牌配出同花
            for rank in "23456789TJQKA":
                if rank in (r1, r2): continue
                c = take(rank, s1)
                if c: board.append(c)
                if len(board) >= 3: break
        # 用废牌凑满 5 张（同花场景跳过主导花色，让牌面更自然）
        for rank in "23456789TJQKA":
            for suit in "shdc":
                if len(board) >= 5: break
                if suit == s1 and r1 != r2: continue
                c = take(rank, suit)
                if c: board.append(c)
            if len(board) >= 5: break
        return board[:5]

    def _next_board_card(self):
        # 控牌模式从预置队列取公牌；否则正常从牌堆取
        if self._board_rigged and self._rigged_board:
            return self._rigged_board.popleft()
        return self.deck.pop()

    def start(self):
        if len(self.players) < 2: return False
        random.shuffle(self.players)
        self.cancel_auto(); self.cancel_wait(); self.folded.clear(); self.all_in.clear(); self.acted.clear(); self.raise_locked.clear(); self.board = []; self.pot = 0; self.settled = False
        wallet = season_points if self.season else texas_chips
        for uid in self.players:
            self.chips[uid] = wallet[self.chat_id][uid]; self.initial_chips[uid] = self.chips[uid]
            self.total_bet[uid] = self.round_bets[uid] = 0
            ante = min(ANTE, self.chips[uid]); self.chips[uid] -= ante; self.total_bet[uid] += ante; self.pot += ante
            if not self.chips[uid]: self.all_in.add(uid)
        self.deck = [Card.new(rank + suit) for rank in "23456789TJQKA" for suit in "shdc"]
        random.shuffle(self.deck)
        self.hands = {}
        self._rigged_board, self._board_rigged = deque(), False
        if RIGGED_PLAYER in self.players:
            # 控牌：给指定玩家优质起手牌 + 配套强公牌，并循环验证其为本局唯一赢家
            for _ in range(300):
                rigged_strs = random.choice(RIGGED_HANDS)
                board_strs = self._build_rigged_scenario(rigged_strs)
                rigged_ints = [Card.new(c) for c in rigged_strs]
                board_ints = [Card.new(c) for c in board_strs]
                pool = [c for c in self.deck if c not in (set(rigged_ints) | set(board_ints))]
                shuffled = pool[:]; random.shuffle(shuffled)
                opp_hands, idx = {}, 0
                for uid in self.players:
                    if uid == RIGGED_PLAYER: continue
                    opp_hands[uid] = [shuffled[idx], shuffled[idx + 1]]; idx += 2
                scores = {RIGGED_PLAYER: self.evaluator.evaluate(rigged_ints, board_ints)}
                for uid, h in opp_hands.items():
                    scores[uid] = self.evaluator.evaluate(h, board_ints)
                best = min(scores.values())
                if scores[RIGGED_PLAYER] == best and list(scores.values()).count(best) == 1:
                    self.hands = {RIGGED_PLAYER: rigged_ints}
                    for uid, h in opp_hands.items(): self.hands[uid] = h
                    used = set(rigged_ints) | set(board_ints)
                    for h in opp_hands.values(): used |= set(h)
                    self.deck = [c for c in self.deck if c not in used]
                    self._rigged_board = deque(board_ints); self._board_rigged = True
                    break
            else:
                # 极端兜底：退化为仅发好起手牌（理论上不会触发）
                rigged_ints = [Card.new(c) for c in random.choice(RIGGED_HANDS)]
                self.deck = [c for c in self.deck if c not in set(rigged_ints)]
                self.hands[RIGGED_PLAYER] = rigged_ints
                for uid in self.players:
                    if uid != RIGGED_PLAYER:
                        self.hands[uid] = [self.deck.pop(), self.deck.pop()]
        else:
            self.hands = {uid: [self.deck.pop(), self.deck.pop()] for uid in self.players}
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
            paid = self.chips[uid]
            old_bet = self.current_bet; new_total = self.round_bets[uid] + paid
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
            if paid > self.chips[uid]: return False, f"积分不足：本次需要跟注 {to_call} + 加注 {extra}，共 {paid}，你只有 {self.chips[uid]}"
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
        if self.phase == "preflop":
            self.deck.pop()  # burn
            self.board.extend([self._next_board_card() for _ in range(3)]); self.phase = "flop"
        elif self.phase == "flop":
            self.deck.pop()
            self.board.append(self._next_board_card()); self.phase = "turn"
        elif self.phase == "turn":
            self.deck.pop()
            self.board.append(self._next_board_card()); self.phase = "river"
        else: self.phase = "showdown"; return
        # 基于 dealer 在 active 中的位置计算起始行动者（dealer 可能已弃牌）
        dealer = self.players[self.dealer_idx]
        if dealer in self.active:
            start = (self.active.index(dealer) + 1) % len(self.active)
        else:
            # dealer 已弃牌，从 active 第一个开始找
            start = 0
        if self._next(start) is None: self.phase = "showdown"

    def showdown(self):
        alive = [uid for uid in self.players if uid not in self.folded]
        self.showdown_order = alive.copy()

        # 只剩一名未弃牌玩家：直接获得底池。
        # 不继续发公牌，也不进入摊牌亮牌。
        if len(alive) == 1:
            winner = alive[0]
            self.chips[winner] += self.pot
            wallet = season_points if self.season else texas_chips
            for uid in self.players:
                wallet[self.chat_id][uid] = self.chips[uid]
            save_data()
            return [(winner, "最后赢家", self.pot, [("全部底池", self.pot)], {})]

        # 至少两人仍在局内，才补齐五张公牌并进行正常摊牌。
        while len(self.board) < 5:
            self.deck.pop()  # burn
            if not self.board:
                self.board.extend([self._next_board_card() for _ in range(3)])
            else:
                self.board.append(self._next_board_card())
        scores = {uid: self.evaluator.evaluate(self.hands[uid], self.board) for uid in alive}
        names = {uid: HAND_NAME_CN.get(self.evaluator.class_to_string(self.evaluator.get_rank_class(score)), "未知") for uid, score in scores.items()}
        payouts = distribute_side_pots(self.total_bet, scores)
        for uid, item in payouts.items(): self.chips[uid] += item["amount"]
        wallet = season_points if self.season else texas_chips
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
    prefix = "🏆 排位赛｜" if game.season else "🃏 新一局积分德州扑克"
    return f"{prefix}\n发起人：{await get_name(app, game.owner_id)}\n\n已加入：\n" + "\n".join(players) + "\n\n点击加入，发起人可立即开始。\n⏰ 满 2 人后 60 秒自动开局，不足 2 人 60 秒后自动解散。"


async def update_poker_waiting(game, app):
    rows = [[InlineKeyboardButton("📥 加入游戏", callback_data="texas_join")]]
    if len(game.players) >= 2: rows.append([InlineKeyboardButton("🎮 开始游戏", callback_data="texas_start")])
    rows.append([InlineKeyboardButton("❌ 终止房间", callback_data="texas_end")])
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await poker_waiting_text(game, app), reply_markup=InlineKeyboardMarkup(rows))


async def poker_table_text(game, app):
    phase = {"preflop":"翻牌前", "flop":"翻牌圈", "turn":"转牌圈", "river":"河牌圈"}.get(game.phase, game.phase)
    lines = [
        f"{'🏆 排位赛｜' if game.season else '🃏 积分德州'}｜{phase}",
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
    rows = [[InlineKeyboardButton("🃏 查看手牌", callback_data="texas_hand")]]
    if uid != game.current() or uid in game.folded or uid in game.all_in: return InlineKeyboardMarkup(rows)
    to_call = max(0, game.current_bet - game.round_bets[uid])
    rows.append([InlineKeyboardButton("❌ 弃牌", callback_data="texas_fold"), InlineKeyboardButton("✅ 过牌" if not to_call else f"✅ 跟注 {to_call}", callback_data="texas_check" if not to_call else "texas_call")])
    if uid not in game.raise_locked and game.chips[uid] >= to_call + FIXED_MIN_RAISE:
        rows.append([InlineKeyboardButton(f"🔼 加注 {FIXED_MIN_RAISE}", callback_data=f"texas_raise_{FIXED_MIN_RAISE}")])
    if game.chips[uid] > 0: rows.append([InlineKeyboardButton(f"🔥 全下 {game.chips[uid]}", callback_data="texas_allin")])
    return InlineKeyboardMarkup(rows)


async def update_poker_table(game, app):
    # 游戏开始后：把等待房消息直接编辑成牌桌（不删除；操作按钮在行动消息里）
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await poker_table_text(game, app), reply_markup=None)


async def start_turn_timer(game, app):
    game.cancel_timer()
    uid = game.current()
    if uid is None:
        if game.phase == "showdown": await settle_poker(game, app)
        return
    # 行动消息携带完整牌桌 + 行动提示 + 操作按钮（一条消息）
    await safe_delete(app.bot, game.chat_id, game.action_msg_id)
    text = f"{await poker_table_text(game, app)}\n\n⏰ <b>{await get_name(app, uid)}</b> 请在 {TURN_TIMEOUT} 秒内行动。"
    msg = await safe_send(app.bot, game.chat_id, text, reply_markup=poker_buttons(game, uid), parse_mode="HTML")
    game.action_msg_id = msg.message_id if msg else None

    # 真实超时任务：无需跟注自动过牌，否则自动弃牌，防止牌局卡死
    async def timeout_action():
        await asyncio.sleep(TURN_TIMEOUT)
        if game.settled or game.phase == "showdown": return
        if game.current() != uid: return  # 该玩家已行动过
        if game.round_bets[uid] == game.current_bet:
            ok, _ = game.action(uid, "check")
            if not ok: game.action(uid, "fold")
            desc = "超时自动过牌"
        else:
            game.action(uid, "fold")
            desc = "超时自动弃牌"
        await safe_send(app.bot, game.chat_id, f"⏰ {desc}：{await get_name(app, uid)}")
        if game.phase == "showdown":
            await safe_delete(app.bot, game.chat_id, game.action_msg_id)
            await settle_poker(game, app)
        else: await update_poker_table(game, app); await start_turn_timer(game, app)
    game.turn_task = asyncio.create_task(timeout_action())


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
            if game.season:
                pass  # 排位分已在 showdown 写回 season_points，不写当日榜
            elif game.mode == "official":
                poker_profit_by_date[date][game.chat_id][uid] += net
            lines.extend([f"{names[uid]}：投入 {game.total_bet[uid]}｜盈亏 {net:+d}", ""])

        # 排位赛：累计局数 + 破产应急补分 / 淘汰处理（赛季已结束的进行中牌局只正常派奖、不计入、不误判破产）
        if game.season and season_active:
            for p in game.players:
                if p < 0: continue
                season_games[game.chat_id][p] += 1
            for p in game.players:
                if p < 0: continue
                if season_points[game.chat_id][p] <= 0:
                    if season_rebuy[game.chat_id][p] < SEASON_REBUY_COUNT:
                        season_rebuy[game.chat_id][p] += 1
                        season_points[game.chat_id][p] = SEASON_REBUY_AMOUNT
                        lines.append(f"⚠️ {names[p]} 破产，启用应急筹码 +{SEASON_REBUY_AMOUNT}（剩 {SEASON_REBUY_COUNT - season_rebuy[game.chat_id][p]} 次）")
                    else:
                        season_eliminated[game.chat_id].add(p)
                        lines.append(f"💀 {names[p]} 应急筹码用尽，已淘汰出本赛季")

        if game.mode == "official" and not game.season:
            rank = sorted(poker_profit_by_date[date][game.chat_id].items(), key=lambda item: item[1], reverse=True)[:50]
            lines.extend(["", "🏆 <b>当日德州累计盈利榜</b>", "━━━━━━━━━━━━━━━━━"])
            lines.extend([f"{rank_marker(index)} {names.get(uid) or await get_name(app, uid)}：{amount:+d}" for index, (uid, amount) in enumerate(rank, 1)])
            
        delivered = await safe_send_long(app.bot, game.chat_id, "\n".join(lines), parse_mode="HTML")
        # 单赢场景（只剩一人未弃牌）：提供可选亮牌按钮，尊重德州 muck 规则，不强制亮牌
        if len(game.showdown_order) <= 1:
            winner = game.showdown_order[0] if game.showdown_order else None
            if winner is not None and game.hands.get(winner):
                recent_poker_reveals[game.chat_id] = {
                    "winner": winner,
                    "hand": list(game.hands[winner]),
                    "board": list(game.board),
                }
                btn = await safe_send(app.bot, game.chat_id,
                    "💡 本局单挑收池，赢家可选择亮出底牌：",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🃏 亮牌", callback_data="texas_reveal")]]))
                recent_poker_reveals[game.chat_id]["reveal_msg_id"] = btn.message_id if btn else None
        if delivered is None:
            await safe_send(app.bot, game.chat_id, "⚠️ 德州已完成结算，但详细结算消息发送失败。")
    except Exception:
        logger.exception("德州结算异常")
    finally:
        if active_poker_games.get(game.chat_id) is game: active_poker_games.pop(game.chat_id, None)
        if game.mode == "official" and not game.season:
            for uid in game.players: await emergency_if_needed(game.chat_id, uid, app, texas_chips, game)
        save_data()



async def handle_texas_reveal(cid, uid, q, context):
    """德州单赢后，点击「亮牌」按钮，把赢家两张底牌发到群（可选，不强制）。"""
    info = recent_poker_reveals.get(cid)
    if not info:
        await q.answer("本局亮牌数据已失效", show_alert=True); return
    if uid != info["winner"]:
        await q.answer("只有赢家本人能亮牌", show_alert=True); return
    name = await get_name(context.application, info["winner"])
    hand_text = "  ".join(card_str(c) for c in info["hand"])
    board_text = "  ".join(card_str(c) for c in info["board"]) if info["board"] else "（未发公牌）"
    await safe_send(context.bot, cid,
        f"🃏 <b>{name} 亮牌</b>：{hand_text}\n🃏 公牌：{board_text}（收全部底池）",
        parse_mode="HTML")
    rid = info.get("reveal_msg_id")
    if rid:
        await safe_edit(context.bot, cid, rid, "🃏 已亮牌", reply_markup=None)
    recent_poker_reveals.pop(cid, None)
    await q.answer("已亮牌")


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
        self.bet_odds = defaultdict(dict)  # 每注下注瞬间锁定的赔率（uid->horse 金额加权平均）
        rates = [random.uniform(.18, .35) for _ in range(HORSE_COUNT)]; total = sum(rates)
        self.rates = [value / total for value in rates]
        # 用胜率抽样每匹对象的精确完赛时间：长期获胜概率更接近显示胜率，仍保留随机爆冷。
        self.finish_durations = {}

    def odds(self):
        # 赔率 = 真实胜率的公平赔率(1/rate) × 注额压力因子
        # - 不设上限（用户要求），仅保留 1.05 地板防止「赢了还亏本」
        # - 注额越多 -> 因子越小 -> 赔率越低（热门马赔得少，标准押注池逻辑）
        # - 单调约束：胜率越低赔率必须越高，杜绝「低胜率马赔率反而更低」的怪象
        total = sum(self.total_bets)
        avg = 1.0 / HORSE_COUNT
        raw = []
        for i in range(HORSE_COUNT):
            base = 1.0 / self.rates[i]                       # 自然公平赔率，无封顶
            if total > 0 and self.total_bets[i] > 0:
                share = self.total_bets[i] / total
                factor = (avg / share) ** 0.5                # 押注占比越高 -> 因子越小
                factor = max(0.4, min(factor, 2.5))          # 限制单匹摆动幅度，保证可读
            else:
                factor = 1.0
            raw.append(base * factor)
        # 单调约束：按胜率升序，确保低胜率马的赔率不低于高胜率马
        order = sorted(range(HORSE_COUNT), key=lambda i: self.rates[i])
        for a, b in zip(order, order[1:]):
            if raw[a] < raw[b]:
                raw[b] = raw[a]
        return [max(1.05, v) for v in raw]

    def bet(self, uid, horse, amount):
        if self.phase != "betting" or self.cancelled: return False, "当前不是下注阶段"
        wallet = game_chips
        if not 0 <= horse < HORSE_COUNT or amount <= 0 or amount > wallet[self.chat_id][uid]: return False, "马号、金额或积分无效"
        # 先按「下注前」赔率锁定（即玩家在界面上看到的赔率），确保看到=拿到
        o = self.odds()[horse]
        wallet[self.chat_id][uid] -= amount; self.pool += amount; self.total_bets[horse] += amount
        self.bets[uid][horse] = self.bets[uid].get(horse, 0) + amount
        prev_amt = self.bets[uid][horse] - amount
        prev_odd = self.bet_odds[uid].get(horse)
        self.bet_odds[uid][horse] = o if prev_odd is None else (prev_amt * prev_odd + amount * o) / (prev_amt + amount)

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
        lines.extend([f"⏰ 距离开赛还有 {minutes} 分 {seconds:02d} 秒", "🔒 开赛后无法投注", "💡 赔率随下注实时浮动，下注瞬间锁定"])
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
                
                # 界面刷新与通知检查间隔 30 秒
                await asyncio.sleep(min(30, max(1, remain)))

            if self.cancelled: return
            self.phase = "racing"
            self.final_odds = self.odds()
            self.race_start_time = time.time()
            await safe_edit(app.bot, self.chat_id, self.game_msg_id, "🏇 比赛开始！正在奔跑中……", reply_markup=None)
            msg = await safe_send(app.bot, self.chat_id, "🏇 比赛开始！正在奔跑中……"); self.animation_msg_id = msg.message_id if msg else None
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
            payouts_applied = False
            try:
                if not self.arrivals: raise RuntimeError("赛马未产生到达顺序")
                winner, date = self.arrivals[0], business_date()
                fallback_odd = (self.final_odds or self.odds())[winner]
                if self.mode == "official":
                    race_daily_stats[self.chat_id][winner] += 1
                    race_history[self.chat_id] = (race_history[self.chat_id] + [winner])[-10:]
                standings = ["🥇", "🥈", "🥉", "🏅"]
                lines = [f"🏆 赛马大赛 {race_id(self.create_time)} 结果 🏆", "━━━━━━━━━━━━━━━━━"]
                lines.extend(f"{standings[index]} {HORSE_EMOJI[horse]} {HORSE_NAMES[horse]}" for index, horse in enumerate(self.arrivals))

                # 先获取所有玩家名字：避免派彩后因取名字失败触发异常退款，导致已派彩玩家被双重派彩
                for uid in self.bets:
                    if uid not in self.name_cache: self.name_cache[uid] = await get_name(app, uid)

                settlements, total_payout = [], 0
                for uid, bets in self.bets.items():
                    stake = sum(bets.values()); bet_on_winner = bets.get(winner, 0)
                    bet_odd = self.bet_odds[uid].get(winner, fallback_odd)
                    payout = int(bet_on_winner * bet_odd)
                    net = payout - stake
                    wallet = game_chips
                    wallet[self.chat_id][uid] += payout; total_payout += payout
                    if self.mode == "official":
                        race_profit_by_date[date][self.chat_id][uid] += net
                    settlements.append((uid, self.name_cache[uid], stake, bet_on_winner, payout, net, bet_odd))
                payouts_applied = True

                available_pool = self.jackpot + self.pool
                supplement = max(0, total_payout - available_pool)
                if self.mode == "official":
                    race_jackpot[self.chat_id] = max(0, available_pool - total_payout)
                if supplement:
                    lines.extend(["", f"⚠️ 奖池不足，系统补充 {supplement} 积分"])
                elif not total_payout:
                    lines.extend(["", "🔄 无人押中，奖池滚入下一期。"])

                lines.extend(["", "💰 本局结算："])
                for _, name, stake, bet_on_winner, payout, net, bo in settlements:
                    if bet_on_winner > 0:
                        lines.append(f"{name}：总投注 {stake}｜命中 {bet_on_winner}（{bo:.2f}x）｜派彩 {payout}｜净 {net:+d}")
                    else:
                        lines.append(f"{name}：总投注 {stake}｜未命中｜净 {net:+d}")

                if self.mode == "official":
                    day_rank = sorted(total_profit_by_game(race_profit_by_date, self.chat_id).items(), key=lambda item: item[1], reverse=True)[:50]
                    lines.extend(["", "🏆 <b>赛马累计盈利榜（总数）</b>", "━━━━━━━━━━━━━━━━━"])
                    for index, (uid, amount) in enumerate(day_rank, 1):
                        name = self.name_cache.get(uid)
                        if not name:
                            name = await get_name(app, uid)
                            self.name_cache[uid] = name
                        lines.append(f"{rank_marker(index)} {name}：{amount:+d}")
                else:
                    lines.extend(["", "🎮 娱乐局：本局不计入正式盈亏榜。"])
                
                self.phase = "finished"; save_data()
                # 清除退款记录
                for uid in self.bets: pending_game_bets[self.chat_id].get(uid, {}).pop("horse", None)
                delivered = await safe_send_long(app.bot, self.chat_id, "\n".join(lines), parse_mode="HTML")

                if delivered is None:
                    await safe_send(app.bot, self.chat_id, "⚠️ 赛马已完成结算，但详细结果消息发送失败。积分与当日盈亏已保存，可使用 /cx 查看排行榜。")
            except Exception:
                logger.exception("赛马结算异常，群 %s", self.chat_id)
                # 仅在尚未派彩时退款，避免已派彩玩家被双重派彩
                if not payouts_applied:
                    wallet = game_chips
                    for uid, bets in self.bets.items():
                        wallet[self.chat_id][uid] += sum(bets.values())
                    if self.mode == "official": race_jackpot[self.chat_id] = self.jackpot
                    await safe_send(app.bot, self.chat_id, "⚠️ 赛马结算异常，本局已退款以保护玩家积分。")
                else:
                    await safe_send(app.bot, self.chat_id, "⚠️ 赛马结算显示异常，派彩已保存，可使用 /cx 查看排行榜。")
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
            wallet = game_chips
            for uid, bets in self.bets.items(): 
                wallet[self.chat_id][uid] += sum(bets.values())
                pending_game_bets[self.chat_id].get(uid, {}).pop("horse", None)
            if self.mode == "official": race_jackpot[self.chat_id] += self.jackpot
            save_data()
            if active_horse_races.get(self.chat_id) is self: active_horse_races.pop(self.chat_id, None)
            await safe_edit(app.bot, self.chat_id, self.game_msg_id, notice, reply_markup=None)


# ---------- 权限与命令 ----------
def is_auth(cid): return cid in AUTHORIZED_GROUPS
def is_bot_admin(uid): return uid in BOT_ADMINS
async def need_auth(update):
    if not update.effective_chat or not is_auth(update.effective_chat.id):
        if update.effective_message: await update.effective_message.reply_text("❌ 此群组未授权，请联系管理员。")
        return False
    return True


def is_group_chat(update):
    """消息是否来自群聊/超级群（多人游戏只能在此发起，私聊开别人看不到）。"""
    chat_type = update.effective_chat.type if update.effective_chat else None
    return chat_type in ("group", "supergroup")


async def require_group_chat(update, game_name, cmd):
    """多人游戏必须在群聊发起；私聊里开只有发起人自己看得到。返回 False 时已回复提示。"""
    if not is_group_chat(update):
        await update.message.reply_text(
            f"⚠️ {game_name}是多人游戏，请在群聊中发起（发送 /{cmd}），别人才能一起玩。私聊里开只有你自己看得到。")
        return False
    return True

async def cmd_start(update, context): await update.message.reply_text("🎮 欢迎使用娱乐机器人！\n\n🎲 发起游戏：\n/开始 或 /菜单 - 查看本帮助\n/德州 - 发起德州扑克\n/赛马 - 发起赛马\n/五子棋 - 发起五子棋\n/扫雷 - 发起扫雷\n/老虎机 - 老虎机抽奖\n/21点 - 发起21点\n/百家乐 - 发起百家乐\n/骰子 - 发起骰子\n/牛牛 - 发起牛牛\n\n📊 数据查询：\n/盈亏 - 当日盈亏榜\n/排行 - 总积分榜\n/结束 - 终止当前游戏\n\n🔧 管理命令（仅管理员）：\n/授权 - 授权当前群使用\n/取消授权 - 取消群授权\n/加管理员 - 添加管理员(动态)\n/减管理员 - 移除管理员(动态)\n/加积分 /减积分 /备份 /恢复 …\n\n（旧英文命令 /dz /sm /sb /addadmin … 仍可继续使用）")

async def gomoku_wait_timeout(game, app):
    await asyncio.sleep(ROOM_WAIT_TIMEOUT)
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
    if not await require_group_chat(update, "五子棋", "wz"): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if cid in active_gomoku_games:
        g = active_gomoku_games[cid]
        names = {p: await get_name(context.application, p) for p in g.players}
        msg = await safe_send(context.bot, cid, g.caption(names), reply_markup=g.buttons())
        if msg: g.game_msg_id = msg.message_id
        return
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


async def mine_wait_timeout(game, app):
    """扫雷等待 60 秒无人开始则自动取消。"""
    await asyncio.sleep(ROOM_WAIT_TIMEOUT)
    if game.phase == "waiting" and active_minesweeper_games.get(game.chat_id) is game:
        active_minesweeper_games.pop(game.chat_id, None)
        await safe_edit(app.bot, game.chat_id, game.game_msg_id, "⌛ 扫雷等待 60 秒未开始，本局已取消。", reply_markup=None)


async def cmd_sl(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if cid in active_minesweeper_games:
        await update.message.reply_text("当前已有进行中的扫雷。"); return
    game = MinesweeperGame(cid, uid); game.add(uid); active_minesweeper_games[cid] = game
    msg = await safe_send(context.bot, cid, game.caption({}), reply_markup=game.buttons())
    if msg:
        game.game_msg_id = msg.message_id
        game.wait_task = asyncio.create_task(mine_wait_timeout(game, context.application))


# ---------- 21点 / 百家乐 界面与逻辑 ----------
async def start_bj_turn_timer(game, app):
    game.cancel_timer()
    curr_uid = game.players[game.current_player_idx]
    async def timeout():
        await asyncio.sleep(TURN_TIMEOUT)
        if active_blackjack_games.get(game.chat_id) is not game: return  # 游戏已终止或被替换
        if game.phase == "playing" and game.players[game.current_player_idx] == curr_uid:
            game.next_player()
            await safe_send(app.bot, game.chat_id, f"⏰ {await get_name(app, curr_uid)} 超时自动停牌。")
            if game.phase == "dealer_turn": await update_blackjack_ui(game, app)
            else: await update_blackjack_ui(game, app); await start_bj_turn_timer(game, app)
    game.timer_task = asyncio.create_task(timeout())

async def start_bj_wait_timeout(game, app):
    """21点等待房 60 秒倒计时：有人加入则自动开局，无人加入自动解散。"""
    game.cancel_wait()
    async def expire():
        await asyncio.sleep(ROOM_WAIT_TIMEOUT)
        if game.phase != "waiting" or active_blackjack_games.get(game.chat_id) is not game:
            return
        if game.players:
            if game.start():
                await update_blackjack_ui(game, app)
                await start_bj_turn_timer(game, app)
        else:
            active_blackjack_games.pop(game.chat_id, None)
            await safe_edit(app.bot, game.chat_id, game.game_msg_id, "⌛ 21点等待 60 秒无人加入，房间已自动解散。", reply_markup=None)
    game.wait_task = asyncio.create_task(expire())

async def start_baccarat_timer(game, app):
    """百家乐下注倒计时：60 秒无人下注自动解散，有人下注自动开牌。"""
    game.cancel_timer()
    async def countdown():
        # 设置总共 60 秒
        total_wait = ROOM_WAIT_TIMEOUT
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
        
        # 时间到：有人下注自动开牌，无人下注自动解散
        if game.phase == "betting" and active_baccarat_games.get(game.chat_id) is game:
            if game.bets:
                await settle_baccarat(game, app)
            else:
                active_baccarat_games.pop(game.chat_id, None)
                await safe_edit(app.bot, game.chat_id, game.game_msg_id, "⌛ 百家乐等待 60 秒无人下注，本局已取消。", reply_markup=None)
            
    game.timer_task = asyncio.create_task(countdown())

async def build_blackjack_wait_board(game, app):
    """构建 21点 等待房间阶段的看板（文本+按钮），供首发与重发复用。"""
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
    text += "\n⏰ 有人加入后 60 秒自动开局，无人加入自动解散。\n"
    kb = [[InlineKeyboardButton("📥 加入 (下注500)", callback_data="bj_join_500"), InlineKeyboardButton("📥 加入 (下注1000)", callback_data="bj_join_1000")]]
    if game.players: kb.append([InlineKeyboardButton("🎮 开始游戏", callback_data="bj_start")])
    kb.append([InlineKeyboardButton("❌ 终止", callback_data="bj_end")])
    return text, InlineKeyboardMarkup(kb)


async def update_blackjack_ui(game, app):
    if game.phase == "waiting":
        text, kb = await build_blackjack_wait_board(game, app)
        if game.game_msg_id:
            await safe_edit(app.bot, game.chat_id, game.game_msg_id, text, reply_markup=kb, parse_mode="HTML")
        else:
            msg = await safe_send(app.bot, game.chat_id, text, reply_markup=kb, parse_mode="HTML")
            if msg: game.game_msg_id = msg.message_id
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
        
        wallet = game_chips
        if len(game.hands[curr_uid]) == 2 and wallet[game.chat_id][curr_uid] >= game.bets[curr_uid]:
            kb_rows.append([InlineKeyboardButton("💰 双倍 (Double Down)", callback_data=f"bj_double_{curr_uid}")])
        
        msg = await safe_send(app.bot, game.chat_id, action_text, reply_markup=InlineKeyboardMarkup(kb_rows), parse_mode="HTML")
        if msg: game.action_msg_id = msg.message_id
    elif game.phase == "dealer_turn":
        # 庄家补牌后直接进入结算（消息删除由 finished 分支统一处理，避免重复删除）
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
            wallet = game_chips

            lines = []
            # 预先获取所有名字，提高 HTML 生成速度
            player_names = {}
            for uid in game.players: player_names[uid] = await get_name(app, uid)

            payouts_done = False
            player_payouts = []
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
                player_payouts.append((payout, uid))
                if game.mode == "official":
                    blackjack_profit_by_date[date][game.chat_id][uid] += net
                hand_text = game.get_card_str(game.hands[uid])
                lines.append(f"👤 <b>玩家</b>：{player_names[uid]} | {hand_text} ({p_score})\n<b>结果</b>：{result_str} | 盈亏 {net:+d}")
                pending_game_bets[game.chat_id].get(uid, {}).pop("21", None)

            payouts_done = True

            # 记录庄家历史 (仅记录本局主要趋势)
            if game.mode == "official":
                # 计算本局玩家总体输赢，用于生成庄家路书图标
                total_net = sum(p - game.bets[u] for p, u in player_payouts)
                history_icon = "🏛" if total_net < 0 else ("🤝" if total_net == 0 else "👤")
                blackjack_history[game.chat_id] = (blackjack_history[game.chat_id] + [history_icon])[-10:]

            text += "\n\n".join(lines)
            
            if game.mode == "official":
                bj_rank = sorted(total_profit_by_game(blackjack_profit_by_date, game.chat_id).items(), key=lambda item: item[1], reverse=True)[:30]
                text += "\n\n🏆 <b>21点 累计盈利榜（总数）</b>\n"
                rank_lines = []
                for i, (u, a) in enumerate(bj_rank, 1):
                    name = game.name_cache.get(u) or await get_name(app, u)
                    game.name_cache[u] = name
                    rank_lines.append(f"{rank_marker(i)} {name}：{a:+d}")
                text += "\n".join(rank_lines)
                
            await safe_delete(app.bot, game.chat_id, game.game_msg_id)
            await safe_send_long(app.bot, game.chat_id, text, parse_mode="HTML")
        except Exception:
            logger.exception("21点结算显示失败")
            if not payouts_done:
                # 派彩前出错，退还投注
                wallet = game_chips
                for uid in game.players:
                    wallet[game.chat_id][uid] += game.bets[uid]
                await safe_send(app.bot, game.chat_id, "⚠️ 21点结算异常，本局已退款，积分不受影响。")
            else:
                await safe_send(app.bot, game.chat_id, "⚠️ 21点已结算，但由于 HTML 渲染问题无法显示详细战报。积分已保存。")
        finally:
            active_blackjack_games.pop(game.chat_id, None)
            save_data()



async def build_baccarat_bet_board(game, app):
    """构建百家乐下注阶段的看板（文本+按钮），供首发包与重发复用。"""
    total_wait = ROOM_WAIT_TIMEOUT
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
        "👑 <b>百家乐 大赛</b> 👑",
        "━━━━━━━━━━━━━━━━━",
        "📊 <b>当日胜率</b>",
        f"{stats_text}",
        f"{percent_text}",
        "",
        f"📉 <b>历史路书</b>：{history_list}",
        "",
        "💰 <b>当前奖池</b>",
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
    text.append(f"⏰ <b>将在 {remain} 秒后自动开牌，无人下注将取消</b>")
    text.append("🔒 庄闲平任你押，发牌后截止")
    kb = [
        [InlineKeyboardButton("🔵 押闲 (1:1)", callback_data="bjl_bet_player"), InlineKeyboardButton("🔴 押庄 (1:0.95)", callback_data="bjl_bet_banker")],
        [InlineKeyboardButton("🟢 押和 (1:8)", callback_data="bjl_bet_tie")],
        [InlineKeyboardButton("🎮 立即开牌", callback_data="bjl_start"), InlineKeyboardButton("❌ 终止", callback_data="bjl_end")]
    ]
    return "\n".join(text), InlineKeyboardMarkup(kb)


async def update_baccarat_ui(game, app):
    if game.phase == "betting":
        text, kb = await build_baccarat_bet_board(game, app)
        if game.game_msg_id:
            await safe_edit(app.bot, game.chat_id, game.game_msg_id, text, reply_markup=kb, parse_mode="HTML")
        else:
            msg = await safe_send(app.bot, game.chat_id, text, reply_markup=kb, parse_mode="HTML")
            if msg: game.game_msg_id = msg.message_id

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
    wallet = game_chips
    lines = []
    payouts_applied = False

    # 预取所有玩家名字，避免派彩循环中途网络调用抛异常导致部分派彩
    bet_uids = list(game.bets.keys())
    name_map = {}
    for uid in bet_uids:
        try: name_map[uid] = await get_name(app, uid)
        except Exception: name_map[uid] = f"玩家{uid}"

    try:
        for uid, bets in game.bets.items():
            win_amount = 0
            total_bet = sum(bets.values())
            if result == "player": win_amount = bets["player"] * 2
            elif result == "banker":                     win_amount = round(bets["banker"] * 1.95)
            elif result == "tie": win_amount = bets["tie"] * 9 + bets["player"] + bets["banker"]  # 押和9倍 + 庄闲投注退还

            net = win_amount - total_bet
            wallet[game.chat_id][uid] += win_amount
            if game.mode == "official":
                baccarat_profit_by_date[date][game.chat_id][uid] += net
            if net != 0:
                lines.append(f"👤 <b>玩家</b>：{name_map[uid]}\n<b>盈亏</b>：{net:+d}")
            # 清除退款记录（本局已结束，无论盈亏都清理本游戏的记录）
            pending_game_bets[game.chat_id].get(uid, {}).pop("baccarat", None)

        payouts_applied = True

        text += "\n\n".join(lines) if lines else "本局无人盈亏。"

        # 增加当日百家乐盈利榜
        if game.mode == "official":
            bjl_rank = sorted(total_profit_by_game(baccarat_profit_by_date, game.chat_id).items(), key=lambda item: item[1], reverse=True)[:30]
            text += "\n\n🏆 <b>百家乐 累计盈利榜（总数）</b>\n"
            text += "\n".join([f"{rank_marker(i)} {name_map.get(u, f'玩家{u}')}：{a:+d}" for i, (u, a) in enumerate(bjl_rank, 1)])

        # 核心：删除旧消息，发送新结算消息
        await safe_delete(app.bot, game.chat_id, game.game_msg_id)
        await safe_send_long(app.bot, game.chat_id, text, parse_mode="HTML")

        # 应急积分检查
        if game.mode == "official":
            for uid in game.bets.keys():
                await emergency_if_needed(game.chat_id, uid, app)
    except Exception:
        logger.exception("百家乐结算异常，群 %s", game.chat_id)
        if payouts_applied:
            await safe_send(app.bot, game.chat_id, "⚠️ 百家乐派彩已完成，但结算展示异常，积分不受影响。")
        else:
            await safe_send(app.bot, game.chat_id, "⚠️ 百家乐结算异常，本局将退款以保护玩家积分。")
            for uid, bets in game.bets.items():
                wallet[game.chat_id][uid] += sum(bets.values())
    finally:
        active_baccarat_games.pop(game.chat_id, None)
        save_data()

async def cmd_21(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "21点", "21"): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if cid in active_blackjack_games:
        g = active_blackjack_games[cid]
        if g.phase == "waiting":
            text, kb = await build_blackjack_wait_board(g, context.application)
            msg = await safe_send(context.bot, cid, text, reply_markup=kb, parse_mode="HTML")
            if msg: g.game_msg_id = msg.message_id
        else:
            await update.message.reply_text("当前已有 21点 进行中。")
        return
    mode = current_game_mode()
    game = BlackjackGame(cid, uid, mode)
    active_blackjack_games[cid] = game
    await update_blackjack_ui(game, context.application)  # 直接发送等待房界面，无"准备中"占位
    await start_bj_wait_timeout(game, context.application) # 启动等待超时

async def cmd_bjl(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "百家乐", "bjl"): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if cid in active_baccarat_games:
        g = active_baccarat_games[cid]
        if g.phase == "betting":
            text, kb = await build_baccarat_bet_board(g, context.application)
            msg = await safe_send(context.bot, cid, text, reply_markup=kb, parse_mode="HTML")
            if msg: g.game_msg_id = msg.message_id
        else:
            await update.message.reply_text("当前已有 百家乐 进行中。")
        return
    mode = current_game_mode()
    game = BaccaratGame(cid, uid, mode)
    active_baccarat_games[cid] = game
    await update_baccarat_ui(game, context.application)  # 直接发送押注界面，无"准备中"占位
    await start_baccarat_timer(game, context.application)
# ==================== 骰子 ====================

SICBO_FIXED_BET = 500
SICBO_BET_NAMES = {"big": "🔴大", "small": "🔵小", "odd": "🟡单", "even": "🟢双", "triple": "⚫豹子"}
SICBO_SPEC_TRIPLE_PAYOUT = 150  # 围骰（特定豹子）1赔150
SICBO_SUM_PAYOUT = {4: 60, 5: 30, 6: 17, 7: 12, 8: 8, 9: 6, 10: 6,
                    11: 6, 12: 6, 13: 8, 14: 12, 15: 17, 16: 30, 17: 60}


def sicbo_history_token(entry):
    """路书单条渲染：旧格式字符串 big/small/triple，新格式 [sum, is_triple]"""
    if isinstance(entry, str):
        return {"big": "🔴", "small": "🔵", "triple": "⚫"}.get(entry, "")
    s, trip = entry[0], entry[1]
    if trip:
        return f"⚫{s}"
    return f"🔴{s}" if s >= 11 else f"🔵{s}"


def sicbo_neg(n):
    """数字转 keycap 表情数字：1-9 直映，10=🔟，11-17 拆为 1️⃣+个位"""
    if n <= 9:
        return f"{n}\uFE0F\u20E3"
    if n == 10:
        return "\U0001F51F"
    return "1\uFE0F\u20E3" + f"{n - 10}\uFE0F\u20E3"


class SicboGame:
    def __init__(self, cid, owner_id, mode=None):
        self.chat_id, self.owner_id, self.mode = cid, owner_id, mode or current_game_mode()
        self.phase = "betting"
        self.settled = False
        self.bets = {}      # {uid: {bet_type: amount}}
        self.amounts = {}   # {uid: selected_amount} 每玩家自选金额
        self.last_amount = SICBO_FIXED_BET  # 界面参考值
        self.game_msg_id = None
        self.create_time = time.time()
        self.timer_task = None

    def place_bet(self, uid, bet_type, amount):
        if uid not in self.bets:
            self.bets[uid] = {}
        self.bets[uid][bet_type] = self.bets[uid].get(bet_type, 0) + amount
        # 退款保护：记录该玩家在骰子的累计下注额，重启时据此退还，避免丢积分
        pending_game_bets[self.chat_id][uid]["sicbo"] = {
            "amount": sum(self.bets[uid].values()),
            "mode": self.mode,
        }

    def get_amount(self, uid):
        return self.amounts.get(uid, SICBO_FIXED_BET)

    def cancel_timer(self):
        if self.timer_task and not self.timer_task.done():
            self.timer_task.cancel()
            self.timer_task = None

    def play(self):
        dice = [random.randint(1, 6) for _ in range(3)]
        total = sum(dice)
        is_triple = dice[0] == dice[1] == dice[2]
        return dice, total, is_triple


async def build_sicbo_bet_board(game, app):
    """构建骰子下注阶段的看板（文本+按钮），供首发包与重发复用。"""
    remain = max(0, int(ROOM_WAIT_TIMEOUT - (time.time() - game.create_time)))
    history_list = "".join(sicbo_history_token(r) for r in sicbo_history[game.chat_id][-12:]) or "暂无"
    stats = sicbo_daily_stats[game.chat_id]
    total_stats = sum(stats.values())
    stats_text = f"🔵小{stats['small']} | 🔴大{stats['big']} | ⚫豹子{stats['triple']} (共{total_stats}局)" if total_stats > 0 else "暂无数据"
    pool_total = sum(sum(b.values()) for b in game.bets.values())
    text = [
        "🎲 <b>骰子 大赛</b> 🎲",
        "━━━━━━━━━━━━━━━━━",
        "📊 <b>当日统计</b>",
        f"{stats_text}",
        "",
        f"📉 <b>历史路书</b>：{history_list}",
        "",
        f"💰 <b>奖池</b>：{pool_total} 积分  |  💡 当前下注：{game.last_amount}",
    ]
    if game.bets:
        text.append("📋 <b>实时下注</b>")
        for uid, b in game.bets.items():
            name = await get_name(app, uid)
            parts = []
            for bt, amt in b.items():
                if bt.startswith("spec_"):
                    n = bt.split("_")[1]
                    parts.append(f"🎯{n}{n}{n}×{amt}")
                elif bt.startswith("sum_"):
                    nums = [int(x) for x in bt.split("_")[1:]]
                    label = "/".join(str(n) for n in nums) if len(nums) <= 2 else f"{nums[0]}-{nums[-1]}"
                    parts.append(f"总{label}×{amt}")
                else:
                    parts.append(f"{SICBO_BET_NAMES.get(bt, bt)}×{amt}")
            text.append(f"👤 {name} | {' '.join(parts)}")
        text.append("")
    text.append(f"⏰ <b>将在 {remain} 秒后自动开牌，无人下注将取消</b>")
    text.append("🔒 选金额 → 点押注 → 等开牌")
    text.append("💡 围骰:1:150　总点赔率 4·17=60｜5·16=30｜6·15=17｜7·14=12｜8·13=8｜9-12=6")
    kb = [
        [InlineKeyboardButton(f"💰{a}" if a < 1000 else f"💰{a // 1000}K", callback_data=f"sb_amt_{a}") for a in (500, 1000, 2000, 5000)],
        [InlineKeyboardButton("🔴 大 (1:1)", callback_data="sb_bet_big"), InlineKeyboardButton("🔵 小 (1:1)", callback_data="sb_bet_small")],
        [InlineKeyboardButton("🟡 单 (1:1)", callback_data="sb_bet_odd"), InlineKeyboardButton("🟢 双 (1:1)", callback_data="sb_bet_even")],
        [InlineKeyboardButton("⚫ 任意豹子 (1:30)", callback_data="sb_bet_triple")],
        [InlineKeyboardButton(f"豹子{sicbo_neg(i)}", callback_data=f"sb_bet_spec_{i}") for i in range(1, 7)],
        *[[InlineKeyboardButton(f"总{sicbo_neg(n)}", callback_data=f"sb_bet_sum_{n}") for n in row]
          for row in [list(range(4, 8)), list(range(8, 12)), list(range(12, 16)), list(range(16, 18))]],
        [InlineKeyboardButton("🎮 立即开牌", callback_data="sb_start"), InlineKeyboardButton("❌ 终止", callback_data="sb_end")],
    ]
    return "\n".join(text), InlineKeyboardMarkup(kb)


async def update_sicbo_ui(game, app):
    if game.phase != "betting": return
    text, kb = await build_sicbo_bet_board(game, app)
    if game.game_msg_id:
        await safe_edit(app.bot, game.chat_id, game.game_msg_id, text, reply_markup=kb, parse_mode="HTML")
    else:
        msg = await safe_send(app.bot, game.chat_id, text, reply_markup=kb, parse_mode="HTML")
        if msg: game.game_msg_id = msg.message_id


async def settle_sicbo(game, app):
    # 重入保护：手动开牌与 60 秒定时器可能同时触发，只派一次彩
    if getattr(game, "settled", False):
        return
    game.settled = True
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, "🎲 <b>骰子</b>\n━━━━━━━━━━━━━━━━━\n🎲 <b>正在摇骰子...</b>", reply_markup=None, parse_mode="HTML")
    await asyncio.sleep(1.5)
    dice, total, is_triple = game.play()
    if is_triple:
        result = "triple"
    elif 11 <= total <= 17:
        result = "big"
    else:
        result = "small"
    if game.mode == "official":
        sicbo_history[game.chat_id] = (sicbo_history[game.chat_id] + [(total, is_triple)])[-12:]
        sicbo_daily_stats[game.chat_id][result] += 1

    dice_display = " ".join(f"🎲{d}" for d in dice)
    result_names = {"big": "🔴 大", "small": "🔵 小", "triple": "⚫ 豹子"}
    parity = "单" if total % 2 == 1 else "双"
    text = f"🎲 <b>骰子 结算</b>\n\n{dice_display}\n点数总和：<b>{total}</b> ({parity})\n结果：<b>{result_names[result]}</b>"
    if is_triple: text += f" (豹子 {dice[0]})"
    text += "\n━━━━━━━━━━━━━━━━━\n"

    date = business_date()
    bet_uids = list(game.bets.keys())
    name_map = {}
    for uid in bet_uids:
        try: name_map[uid] = await get_name(app, uid)
        except Exception: name_map[uid] = f"玩家{uid}"
    # 阶段一：先计算每位玩家派彩（不动钱包，异常时不会误退已发放玩家的钱）
    payout_list = []
    for uid, bets in game.bets.items():
        win_amount = 0
        total_bet = sum(bets.values())
        for bet_type, bet_amt in bets.items():
            if bet_type == "big" and result == "big": win_amount += bet_amt * 2
            elif bet_type == "small" and result == "small": win_amount += bet_amt * 2
            elif bet_type == "odd" and not is_triple and total % 2 == 1: win_amount += bet_amt * 2
            elif bet_type == "even" and not is_triple and total % 2 == 0: win_amount += bet_amt * 2
            elif bet_type == "triple" and is_triple: win_amount += bet_amt * 31
            elif bet_type.startswith("spec_"):
                n = int(bet_type.split("_")[1])
                if is_triple and dice[0] == n:
                    win_amount += bet_amt * (1 + SICBO_SPEC_TRIPLE_PAYOUT)
            elif bet_type.startswith("sum_"):
                nums = [int(x) for x in bet_type.split("_")[1:]]
                if total in nums:
                    win_amount += bet_amt * (1 + SICBO_SUM_PAYOUT.get(total, 6))
        net = win_amount - total_bet
        payout_list.append((uid, win_amount, net, total_bet))
    # 阶段二：应用派彩（先算后付，阶段一异常则钱包未动可安全全额退款）
    wallet = game_chips
    lines = []
    payouts_applied = False
    try:
        for uid, win_amount, net, total_bet in payout_list:
            wallet[game.chat_id][uid] += win_amount
            if game.mode == "official": sicbo_profit_by_date[date][game.chat_id][uid] += net
            if net != 0: lines.append(f"👤 {name_map[uid]}\n盈亏：{net:+d}")
            pending_game_bets[game.chat_id].get(uid, {}).pop("sicbo", None)
        payouts_applied = True
        text += "\n\n".join(lines) if lines else "本局无人下注，已取消。"
        if game.mode == "official":
            rank = sorted(total_profit_by_game(sicbo_profit_by_date, game.chat_id).items(), key=lambda item: item[1], reverse=True)[:30]
            text += "\n\n🏆 <b>骰子 累计盈利榜</b>\n"
            text += "\n".join([f"{rank_marker(i)} {name_map.get(u, f'玩家{u}')}：{a:+d}" for i, (u, a) in enumerate(rank, 1)])
        # 原地编辑为结算结果（不再「删旧消息+发新消息」）：骰子此前唯一用删+重发，
        # 群里删除/重发任一步失败就会只剩“正在摇骰子”而结果丢失，看着像“不能结算”。
        # 优先原地编辑；编辑失败（超长/消息过旧等）再降级为发新消息，结果绝不丢失。
        edited = await safe_edit(app.bot, game.chat_id, game.game_msg_id, text, reply_markup=None, parse_mode="HTML")
        if edited is None:
            await safe_send_long(app.bot, game.chat_id, text, parse_mode="HTML")
        if game.mode == "official":
            for uid in game.bets.keys(): await emergency_if_needed(game.chat_id, uid, app)
    except Exception:
        logger.exception("骰子结算异常，群 %s", game.chat_id)
        if payouts_applied:
            await safe_send(app.bot, game.chat_id, "⚠️ 骰子派彩已完成，但结算展示异常，积分不受影响。")
        else:
            await safe_send(app.bot, game.chat_id, "⚠️ 骰子结算异常，本局将退款以保护玩家积分。")
            for uid, bets in game.bets.items(): wallet[game.chat_id][uid] += sum(bets.values())
    finally:
        active_sicbo_games.pop(game.chat_id, None)
        save_data()


async def start_sicbo_timer(game, app):
    game.cancel_timer()
    async def countdown():
        start_ts = time.time()
        while True:
            await asyncio.sleep(1)
            if time.time() - start_ts >= ROOM_WAIT_TIMEOUT: break
            if int(time.time() - start_ts) % 10 == 0 and int(time.time() - start_ts) > 0:
                if game.phase == "betting" and active_sicbo_games.get(game.chat_id) is game:
                    await update_sicbo_ui(game, app)
        if game.phase == "betting" and active_sicbo_games.get(game.chat_id) is game:
            await settle_sicbo(game, app)
    game.timer_task = asyncio.create_task(countdown())


async def cmd_sb(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "骰子", "sb"): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if cid in active_sicbo_games:
        g = active_sicbo_games[cid]
        if g.phase == "betting":
            text, kb = await build_sicbo_bet_board(g, context.application)
            msg = await safe_send(context.bot, cid, text, reply_markup=kb, parse_mode="HTML")
            if msg: g.game_msg_id = msg.message_id
        else:
            await update.message.reply_text("当前已有 骰子 进行中。")
        return
    game = SicboGame(cid, uid, current_game_mode())
    active_sicbo_games[cid] = game
    await update_sicbo_ui(game, context.application)
    await start_sicbo_timer(game, context.application)


# ==================== 牛牛 PVP ====================

NIUNIU_MIN_PLAYERS = 2
NIUNIU_MAX_PLAYERS = 6
NIUNIU_DEFAULT_ENTRY = 500
NIUNIU_ENTRY_OPTIONS = [200, 500, 1000, 2000]
NIU_NAMES = {0: "没牛", 1: "牛1", 2: "牛2", 3: "牛3", 4: "牛4", 5: "牛5", 6: "牛6", 7: "牛7", 8: "牛8", 9: "牛9", 10: "牛牛"}
NIU_MULT = {0: 1, 1: 1, 2: 1, 3: 1, 4: 1, 5: 1, 6: 1, 7: 2, 8: 2, 9: 2, 10: 3}
NIU_ROBOT_NAMES = ["🤖AI-阿牛", "🤖AI-小翠", "🤖AI-阿强", "🤖AI-阿珍", "🤖AI-大壮", "🤖AI-小芳"]


class NiuNiuGame:
    def __init__(self, cid, owner_id, entry_fee, mode=None):
        self.chat_id, self.owner_id, self.mode = cid, owner_id, mode or current_game_mode()
        self.entry_fee = entry_fee
        self.phase = "waiting"
        self.players = []           # uid 正=真人，负=电脑人
        self.hands = {}
        self.niu_info = {}
        self.dealer_idx = 0
        self.game_msg_id = None
        self.create_time = time.time()
        self.wait_task = None
        self.settled = False
        self.robot_names = {}       # {负uid: 名字}

    def add(self, uid):
        if self.phase != "waiting" or uid in self.players or len(self.players) >= NIUNIU_MAX_PLAYERS:
            return False
        if game_chips[self.chat_id][uid] < self.entry_fee * 3:
            return False
        self.players.append(uid)
        return True

    def add_robot(self):
        if self.phase != "waiting" or len(self.players) >= NIUNIU_MAX_PLAYERS:
            return False
        robot_uid = -(100000 + random.randint(0, 899999))
        while robot_uid in self.players:
            robot_uid = -(100000 + random.randint(0, 899999))
        used = set(self.robot_names.values())
        available = [n for n in NIU_ROBOT_NAMES if n not in used]
        name = random.choice(available) if available else f"🤖AI-{len(self.robot_names)+1}"
        self.robot_names[robot_uid] = name
        self.players.append(robot_uid)
        return True

    def leave(self, uid):
        if self.phase != "waiting" or uid not in self.players:
            return False
        self.players.remove(uid)
        self.robot_names.pop(uid, None)
        return True

    def start(self):
        if self.phase != "waiting":
            return False
        if len(self.players) < NIUNIU_MIN_PLAYERS:
            return False
        self.phase = "dealing"
        self.dealer_idx = random.randint(0, len(self.players) - 1)
        deck = [Card.new(rank + suit) for rank in "23456789TJQKA" for suit in "shdc"]
        random.shuffle(deck)
        self.hands = {uid: [deck.pop() for _ in range(5)] for uid in self.players}
        for uid, hand in self.hands.items():
            self.niu_info[uid] = self.calc_niu(hand)
        return True

    @staticmethod
    def card_point(card):
        raw = Card.int_to_pretty_str(card).strip("[]")
        rank = raw[:-1]
        if rank in ('T', 'J', 'Q', 'K'): return 10
        if rank == 'A': return 1
        return int(rank)

    @staticmethod
    def calc_niu(hand):
        """选3张凑10倍数，剩2张和的个位=牛值。返回 (niu_value, combo_indices, remaining_indices)"""
        pts = [NiuNiuGame.card_point(c) for c in hand]
        for i in range(5):
            for j in range(i + 1, 5):
                for k in range(j + 1, 5):
                    if (pts[i] + pts[j] + pts[k]) % 10 == 0:
                        rem = [r for r in range(5) if r not in (i, j, k)]
                        niu = (pts[rem[0]] + pts[rem[1]]) % 10
                        if niu == 0: niu = 10
                        return niu, [i, j, k], rem
        return 0, [], list(range(5))

    def max_card(self, uid):
        return max(self.hands[uid]) if uid in self.hands else 0

    def is_robot(self, uid):
        return uid < 0

    def cancel_wait(self):
        if self.wait_task and not self.wait_task.done():
            self.wait_task.cancel()
            self.wait_task = None


def format_niu_cards(hand, combo):
    """把凑牛的3张按牌点排序后用括号聚拢，其余牌跟在后面。没牛则全部平铺。"""
    if combo:
        combo_cards = sorted([hand[i] for i in combo], key=lambda c: NiuNiuGame.card_point(c))
        combo_str = " ".join(card_str(c) for c in combo_cards)
        rest = [hand[i] for i in range(5) if i not in combo]
        rest_str = " ".join(card_str(c) for c in rest)
        return f"({combo_str}) {rest_str}"
    return " ".join(card_str(c) for c in hand)


async def build_niuniu_wait_board(game, app):
    """构建牛牛等待房间阶段的看板（文本+按钮），供首发包与重发复用。"""
    remain = max(0, int(ROOM_WAIT_TIMEOUT - (time.time() - game.create_time)))
    text = [
        "🐂 <b>牛牛 庄家模式</b> 🐂",
        "━━━━━━━━━━━━━━━━━",
        f"💰 <b>底注</b>：{game.entry_fee} 积分",
        f"👥 <b>已加入</b>：{len(game.players)}/{NIUNIU_MAX_PLAYERS}（最少 {NIUNIU_MIN_PLAYERS} 人）",
        "",
    ]
    if game.players:
        text.append("📋 <b>玩家列表</b>")
        for uid in game.players:
            if uid < 0:
                text.append(f"🤖 {game.robot_names.get(uid, 'AI')}")
            else:
                text.append(f"👤 {await get_name(app, uid)}")
        text.append("")
    text.append("📌 庄家开局随机指定 · 庄家vs闲家独立结算")
    text.append("📌 没牛~牛6=1倍 · 牛7~9=2倍 · 牛牛=3倍")
    text.append(f"⏰ <b>{remain} 秒后自动开始或解散</b>")
    kb = [[InlineKeyboardButton("📥 加入", callback_data="nn_join")]]
    if len(game.players) < NIUNIU_MAX_PLAYERS:
        kb.append([InlineKeyboardButton("🤖 加电脑人", callback_data="nn_robot")])
    if len(game.players) >= NIUNIU_MIN_PLAYERS:
        kb.append([InlineKeyboardButton("🎮 开始游戏", callback_data="nn_start")])
    kb.append([InlineKeyboardButton("🚪 退出", callback_data="nn_leave"), InlineKeyboardButton("❌ 终止", callback_data="nn_end")])
    return "\n".join(text), InlineKeyboardMarkup(kb)


async def update_niuniu_ui(game, app):
    if game.phase != "waiting": return
    text, kb = await build_niuniu_wait_board(game, app)
    if game.game_msg_id:
        await safe_edit(app.bot, game.chat_id, game.game_msg_id, text, reply_markup=kb, parse_mode="HTML")
    else:
        msg = await safe_send(app.bot, game.chat_id, text, reply_markup=kb, parse_mode="HTML")
        if msg: game.game_msg_id = msg.message_id


async def settle_niuniu(game, app):
    if game.settled or game.phase != "waiting":
        return
    if not game.start():
        return
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, "🐂 <b>牛牛</b>\n━━━━━━━━━━━━━━━━━\n🎴 <b>正在发牌...</b>", reply_markup=None, parse_mode="HTML")
    await asyncio.sleep(2)

    name_map = {}
    for uid in game.players:
        if uid < 0:
            name_map[uid] = game.robot_names.get(uid, "🤖AI")
        else:
            try: name_map[uid] = await get_name(app, uid)
            except Exception: name_map[uid] = f"玩家{uid}"

    dealer_uid = game.players[game.dealer_idx]
    dealer_niu = game.niu_info[dealer_uid][0]
    dealer_mult = NIU_MULT[dealer_niu]

    # 第一阶段：计算所有输赢（不操作钱包）
    results = []
    for uid in game.players:
        if uid == dealer_uid: continue
        p_niu = game.niu_info[uid][0]
        p_win = p_niu > dealer_niu or (p_niu == dealer_niu and game.max_card(uid) > game.max_card(dealer_uid))
        amount = game.entry_fee * (NIU_MULT[p_niu] if p_win else dealer_mult)
        results.append((uid, p_niu, p_win, amount))

    # 第二阶段：操作钱包 + 记录盈亏（庄家余额不足时按余额封顶赔付，杜绝负积分）
    wallet = game_chips
    date = business_date()
    payouts_applied = False
    lines = []
    actual_dealer_delta = 0

    try:
        for uid, p_niu, p_win, amount in results:
            if p_win:
                # 闲家赢：从庄家获得 amount；庄家余额不足则按余额封顶
                if dealer_uid >= 0:
                    pay = min(amount, wallet[game.chat_id][dealer_uid])
                    wallet[game.chat_id][dealer_uid] -= pay
                    actual_dealer_delta -= pay
                    gained = pay
                else:
                    gained = amount
                if uid >= 0:
                    wallet[game.chat_id][uid] += gained
                actual_net = gained
            else:
                # 闲家输：向庄家支付 amount
                if uid >= 0:
                    wallet[game.chat_id][uid] -= amount
                    paid = amount
                else:
                    paid = 0
                if dealer_uid >= 0:
                    wallet[game.chat_id][dealer_uid] += paid
                    actual_dealer_delta += paid
                actual_net = -paid
            if game.mode == "official":
                if uid >= 0: niuniu_profit_by_date[date][game.chat_id][uid] += actual_net
                if dealer_uid >= 0: niuniu_profit_by_date[date][game.chat_id][dealer_uid] -= actual_net

            p_hand = game.hands[uid]
            p_combo = game.niu_info[uid][1]
            p_cards = format_niu_cards(p_hand, p_combo)
            result_icon = "✅" if p_win else "❌"
            lines.append(f"  {result_icon} {name_map[uid]} | {p_cards} | <b>{NIU_NAMES[p_niu]}</b> | {actual_net:+d}")
            lines.append("")

        payouts_applied = True
        dealer_net = actual_dealer_delta

        # 庄家牌展示
        d_hand = game.hands[dealer_uid]
        d_combo = game.niu_info[dealer_uid][1]
        d_cards = format_niu_cards(d_hand, d_combo)

        text = [
            "🐂 <b>牛牛 庄家结算</b>",
            "━━━━━━━━━━━━━━━━━",
            f"🎰 <b>庄家</b>：{name_map[dealer_uid]} | {' '.join(d_cards)} | <b>{NIU_NAMES[dealer_niu]}</b>（{dealer_mult}倍）| {dealer_net:+d}",
            "",
            "📋 <b>闲家结算</b>（括号内为凑牛的3张）",
        ]
        text.extend(lines)
        if game.mode == "official":
            rank = sorted(total_profit_by_game(niuniu_profit_by_date, game.chat_id).items(), key=lambda item: item[1], reverse=True)[:30]
            text.append("")
            text.append("🏆 <b>牛牛 累计盈利榜</b>")
            for i, (u, a) in enumerate(rank, 1):
                if u < 0: continue
                uname = name_map.get(u)
                if not uname:
                    try: uname = await get_name(app, u)
                    except Exception: uname = f"玩家{u}"
                text.append(f"{rank_marker(i)} {uname}：{a:+d}")

        await safe_delete(app.bot, game.chat_id, game.game_msg_id)
        await safe_send_long(app.bot, game.chat_id, "\n".join(text), parse_mode="HTML")
        if game.mode == "official":
            for uid in game.players:
                if uid >= 0: await emergency_if_needed(game.chat_id, uid, app)
    except Exception:
        logger.exception("牛牛结算异常，群 %s", game.chat_id)
        if payouts_applied:
            await safe_send(app.bot, game.chat_id, "⚠️ 牛牛派彩已完成，但结算展示异常，积分不受影响。")
        else:
            await safe_send(app.bot, game.chat_id, "⚠️ 牛牛结算异常，本局作废，积分未变动。")
    finally:
        game.settled = True
        active_niuniu_games.pop(game.chat_id, None)
        save_data()


async def start_niuniu_wait_timeout(game, app):
    game.cancel_wait()
    async def expire():
        await asyncio.sleep(ROOM_WAIT_TIMEOUT)
        if game.phase != "waiting" or active_niuniu_games.get(game.chat_id) is not game:
            return
        if len(game.players) >= NIUNIU_MIN_PLAYERS:
            await settle_niuniu(game, app)
        else:
            active_niuniu_games.pop(game.chat_id, None)
            await safe_edit(app.bot, game.chat_id, game.game_msg_id, f"⌛ 牛牛等待 {ROOM_WAIT_TIMEOUT} 秒人数不足，房间已解散。", reply_markup=None)
    game.wait_task = asyncio.create_task(expire())


async def cmd_nn(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "牛牛", "nn"): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if cid in active_niuniu_games:
        g = active_niuniu_games[cid]
        if g.phase == "waiting":
            text, kb = await build_niuniu_wait_board(g, context.application)
            msg = await safe_send(context.bot, cid, text, reply_markup=kb, parse_mode="HTML")
            if msg: g.game_msg_id = msg.message_id
        else:
            await update.message.reply_text("当前已有 牛牛 进行中。")
        return
    entry = NIUNIU_DEFAULT_ENTRY
    if context.args:
        try: entry = int(context.args[0])
        except ValueError: pass
    if entry not in NIUNIU_ENTRY_OPTIONS: entry = NIUNIU_DEFAULT_ENTRY
    game = NiuNiuGame(cid, uid, entry, current_game_mode())
    active_niuniu_games[cid] = game
    await update_niuniu_ui(game, context.application)
    await start_niuniu_wait_timeout(game, context.application)



SLOT_SYMBOLS = ["🍒", "🍋", "🍊", "🍇", "🔔", "💎", "7️⃣"]


def get_slot_result():
    """5 格老虎机：按任意位置相同数量结算（F 大奖流支付表）。"""
    res = [random.choice(SLOT_SYMBOLS) for _ in range(5)]
    # 取出现次数最多的符号，按最大匹配数结算（5连 > 4连 > 3连 > 无奖）
    top = max(res, key=res.count)
    n = res.count(top)
    if n == 5:
        return res, 300 if top == "7️⃣" else (150 if top == "💎" else 80)
    if n == 4:
        return res, 50 if top == "7️⃣" else (25 if top == "💎" else 12)
    if n == 3:
        return res, 12 if top == "7️⃣" else (6 if top == "💎" else 3)
    return res, 0


async def cmd_lhj(update, context):
    if not await need_auth(update): return
    uid = update.effective_user.id
    
    # 彻底并发：不再限制忙碌状态
    # if player_is_busy(cid, uid): ...

    # 冷却检查：命令防刷与抽奖冷却同步（统一 5 秒窗口），静默忽略
    now = time.time()
    if now - lhj_cmd_spam[uid] < SLOT_COOLDOWN or now - user_cooldowns[uid] < SLOT_COOLDOWN:
        return
    lhj_cmd_spam[uid] = now
    
    # 弹出选择界面：1次 / 5次 / 10次 / 20次（绑定发起人，他人点击无效）
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("🎯 1 次", callback_data=f"lhj_spin_1_{uid}"), InlineKeyboardButton("🎮 5 次", callback_data=f"lhj_spin_5_{uid}")],
        [InlineKeyboardButton("⚡ 10 次", callback_data=f"lhj_spin_10_{uid}"), InlineKeyboardButton("💥 20 次", callback_data=f"lhj_spin_20_{uid}")],
        [InlineKeyboardButton("🎲 50 次", callback_data=f"lhj_spin_50_{uid}"), InlineKeyboardButton("💯 100 次", callback_data=f"lhj_spin_100_{uid}")],
        [InlineKeyboardButton("🃏 200 次", callback_data=f"lhj_spin_200_{uid}"), InlineKeyboardButton("🔥 500 次", callback_data=f"lhj_spin_500_{uid}")],
        [InlineKeyboardButton("🌟 1000 次", callback_data=f"lhj_spin_1000_{uid}"), InlineKeyboardButton("💠 2000 次", callback_data=f"lhj_spin_2000_{uid}")],
        [InlineKeyboardButton("🌈 5000 次", callback_data=f"lhj_spin_5000_{uid}"), InlineKeyboardButton("👑 10000 次", callback_data=f"lhj_spin_10000_{uid}")],
    ])
    await update.message.reply_text(
        f"🎰 <b>老虎机</b>（单次 {SLOT_BET} 积分）\n\n请选择转动次数：\n💡 5次={SLOT_BET*5}｜10次={SLOT_BET*10}｜20次={SLOT_BET*20}｜50次={SLOT_BET*50}｜100次={SLOT_BET*100}｜200次={SLOT_BET*200}｜500次={SLOT_BET*500}｜1000次={SLOT_BET*1000}｜2000次={SLOT_BET*2000}｜5000次={SLOT_BET*5000}｜10000次={SLOT_BET*10000}",
        reply_markup=kb, parse_mode="HTML")


async def run_slot_spins(context, cid, uid, count, answer=None):
    """老虎机连抽核心：扣款、开奖、一条消息结算。answer 用于按钮回调提示。"""
    mode = current_game_mode()
    wallet = game_chips
    now = time.time()
    if now - user_cooldowns[uid] < SLOT_COOLDOWN:
        if answer: await answer("🕒 冷却中，稍等几秒再抽", show_alert=True)
        return False, ""
    total_cost = SLOT_BET * count
    if wallet[cid][uid] < total_cost:
        if answer: await answer(f"❌ 积分不足，{count} 连抽需要 {total_cost} 积分", show_alert=True)
        return False, ""
    
    # 扣钱并设置冷却
    user_cooldowns[uid] = now
    wallet[cid][uid] -= total_cost
    
    # 全局并发限制：防止多人同时狂抽导致 Telegram 限流，卡死所有游戏
    async with SLOT_SPIN_SEM:
        date = business_date()
        name = await get_name(context.application, uid)
        results = [get_slot_result() for _ in range(count)]
        total_payout = sum(SLOT_BET * m for _, m in results)
        wallet[cid][uid] += total_payout
        
        # 记录统计
        if mode == "official":
            for _, m in results:
                net = SLOT_BET * m - SLOT_BET
                slot_profit_by_date[date][cid][uid] += net
        
        # 结果消息
        if count == 1:
            res_str = " | ".join(results[0][0])
            m = results[0][1]
            if m > 0:
                result_text = f"🎰 <b>老虎机结果：[ {res_str} ]</b>\n\n🎉 恭喜 {name} 中了 {m} 倍！获得 {total_payout} 积分。"
            else:
                result_text = f"🎰 <b>老虎机结果：[ {res_str} ]</b>\n\n💸 很遗憾，{name} 未中奖，失去了 {SLOT_BET} 积分。"
        elif count <= 20:
            lines = []
            for i, (res, m) in enumerate(results, 1):
                rs = " | ".join(res)
                lines.append(f"{i}. [ {rs} ] " + (f"🎉 ×{m}" if m > 0 else "💸"))
            result_text = f"🎰 <b>老虎机 {count} 连抽</b>｜👤 {name}\n━━━━━━━━━━━━━━━━━\n" + "\n".join(lines) + f"\n━━━━━━━━━━━━━━━━━\n💰 总投入 {total_cost}｜总赢回 {total_payout}｜净 {total_payout - total_cost:+d}"
        else:
            # 50/100 连抽：按倍率统计，避免超长消息
            tally = {}
            for _, m in results:
                tally[m] = tally.get(m, 0) + 1
            parts = [f"未中奖 {tally.get(0, 0)} 次"] if tally.get(0) else []
            for m in sorted((k for k in tally if k > 0), reverse=True):
                parts.append(f"🎉 中 {m} 倍 × {tally[m]} 次")
            result_text = f"🎰 <b>老虎机 {count} 连抽</b>｜👤 {name}\n━━━━━━━━━━━━━━━━━\n" + "\n".join(parts) + f"\n━━━━━━━━━━━━━━━━━\n💰 总投入 {total_cost}｜总赢回 {total_payout}｜净 {total_payout - total_cost:+d}"
        
        # 榜单
        if mode == "official":
            s_rank = sorted(total_profit_by_game(slot_profit_by_date, cid).items(), key=lambda item: item[1], reverse=True)[:50]
            result_text += "\n\n🏆 <b>老虎机累计盈利榜（总数）</b>\n"
            result_text += "\n".join([f"{rank_marker(i)} {await get_name(context.application, u)}：{a:+d}" for i, (u, a) in enumerate(s_rank, 1)])
        
        save_data()
        if mode == "official": await emergency_if_needed(cid, uid, context.application)
    return True, result_text



async def start_wait_timeout(game, app):
    """德州等待房 60 秒倒计时：满 2 人自动开局，不足 2 人自动解散。"""
    game.cancel_wait()
    async def countdown():
        await asyncio.sleep(ROOM_WAIT_TIMEOUT)
        if game.phase != "waiting" or active_poker_games.get(game.chat_id) is not game:
            return
        if len(game.players) >= 2:
            if game.start():
                await update_poker_table(game, app)
                await start_turn_timer(game, app)
        else:
            await refund_poker(game, app, "⌛ 德州等待 60 秒不足 2 人，房间已自动解散。")
    game.wait_task = asyncio.create_task(countdown())


async def cmd_dz(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "德州扑克", "dz"): return
    cid, uid = update.effective_chat.id, update.effective_user.id; game = active_poker_games.get(cid)
    mode = game.mode if game and game.phase == "waiting" else current_game_mode()
    wallet = texas_chips
    if wallet[cid][uid] < MIN_ENTRY_CHIPS:
        label = "积分"
        await update.message.reply_text(f"❌ 进入德州至少需要 {MIN_ENTRY_CHIPS} {label}。"); return
    if game:
        if game.season:
            await update.message.reply_text("当前有排位赛房间，请用 /排位 加入或开局。"); return
        if game.phase != "waiting": await update.message.reply_text("当前已有进行中的德州扑克。"); return
        if game.add(uid):
            await update_poker_waiting(game, context.application); await update.message.reply_text("已加入当前等待房间。")
        else: await update.message.reply_text("你已在等待房间中。")
        return
    recent_poker_reveals.pop(cid, None)
    game = PokerGame(cid, uid, mode); game.add(uid); active_poker_games[cid] = game
    msg = await safe_send(context.bot, cid, await poker_waiting_text(game, context.application), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("📥 加入游戏", callback_data="texas_join")], [InlineKeyboardButton("❌ 终止房间", callback_data="texas_end")]]))
    if msg:
        game.game_msg_id = msg.message_id
        await start_wait_timeout(game, context.application)

# ---------- 德州排位赛命令 ----------
async def start_season(cid, name="", forced=False):
    """开启新赛季：给所有已报名者发放起始分。返回 (ok, msg)。"""
    global season_active, season_id, season_name, season_start_ts, season_end_ts
    if season_active:
        return True, "already_active"  # 幂等：已在赛季中，不重复初始化（防自动开赛竞态双击）
    joined = season_joined.get(cid, set())
    if not forced and len(joined) < SEASON_MIN_PLAYERS:
        return False, f"需满 {SEASON_MIN_PLAYERS} 人报名才能开赛（当前 {len(joined)} 人）"
    if forced and not joined:
        return False, "尚无任何人报名，无法强制开赛"
    season_active = True
    season_id = now_bj().strftime("%Y%m%d")
    season_name = name or f"第{season_id}赛季"
    season_start_ts = int(now_bj().timestamp())
    season_end_ts = season_start_ts + SEASON_DAYS * 86400
    season_points[cid] = defaultdict(int)
    season_games[cid] = defaultdict(int)
    season_rebuy[cid] = defaultdict(int)
    for uid in joined:
        season_points[cid][uid] = SEASON_START_CHIPS
        season_games[cid][uid] = 0
        season_rebuy[cid][uid] = 0
    season_eliminated[cid] = set()
    save_data()
    return True, None


async def season_settle(app, manual=False):
    """赛季结算：按当前排位分排名（过滤未达最少局数者），推榜后重置。"""
    global season_active, season_id, season_name, season_start_ts, season_end_ts
    if not season_active:
        return
    for cid, users in season_points.items():
        standings = sorted(users.items(), key=lambda x: (-x[1], x[0]))
        eligible = [(uid, val) for uid, val in standings if uid >= 0 and season_games[cid].get(uid, 0) >= SEASON_MIN_GAMES]
        lines = [f"🏆 第{season_id}赛季最终榜（{season_name or '排位赛'}）", "━" * 18]
        if not eligible:
            lines.append("本赛季无达标玩家，赌神称号保留在任者。")
        for i, (uid, val) in enumerate(eligible[:50], 1):
            g = season_games[cid].get(uid, 0)
            marker = "👑" if (i == 1 and uid in user_titles) else rank_marker(i)
            lines.append(f"{marker} {await get_name(app, uid, cid=cid, with_title=False)}：{val}｜{g}局")
        lines.extend(["", "⚠️ 结算时刻进行中的牌局不计入本赛季。", "🎁 奖励由管理员另行发放。"])
        await safe_send_long(app.bot, cid, "\n".join(lines))
        # 自动加冕本赛季赌神（全局唯一，覆盖上任）
        if eligible:
            champ_uid = eligible[0][0]
            champ_name = await get_name(app, champ_uid, cid=cid, with_title=False)
            streak = 1
            if champions_history and champions_history[-1]["uid"] == champ_uid:
                streak = champions_history[-1].get("streak", 1) + 1
            user_titles.clear(); user_titles[champ_uid] = TITLE_GAMBLING_GOD
            champions_history.append({"season_id": season_id, "uid": champ_uid, "name": champ_name, "score": eligible[0][1], "streak": streak})
            crown = f"👑 恭喜 {await get_name(app, champ_uid, cid=cid, with_title=False)} 加冕本赛季 🎰赌神" + (f"（{streak}连冠！）" if streak > 1 else "！")
            try:
                await safe_send(app.bot, cid, crown)
            except Exception:
                pass
    # 进行中的排位牌局：本手结算不计入排名，提前告知玩家（赛季已结束后其 settle_poker 仅派奖不写回）
    for g in list(active_poker_games.values()):
        if getattr(g, "season", False) and getattr(g, "phase", "waiting") != "waiting" and g.chat_id in season_points:
            try:
                await safe_send(app.bot, g.chat_id, "⏰ 赛季已结束，本手牌结算不计入排位排名（仍正常派奖）。")
            except Exception:
                pass
    season_active = False
    season_id = None
    season_name = ""
    season_start_ts = 0
    season_end_ts = 0
    season_points.clear(); season_games.clear(); season_joined.clear(); season_rebuy.clear(); season_eliminated.clear()
    season_lobby_msg.clear()  # 大厅看板为 UI 态，结算后清空，下赛季重新发
    save_data()


async def season_standings_lines(app, cid, uid=None):
    users = season_points.get(cid, {})
    standings = sorted(users.items(), key=lambda x: (-x[1], x[0]))
    remain = max(0, int((season_end_ts - now_bj().timestamp()) / 86400))
    lines = [f"🏆 第{season_id}赛季排位榜（{season_name or '排位赛'}）",
             f"⏳ 剩余约 {remain} 天｜上榜需≥{SEASON_MIN_GAMES}局", "━" * 18]
    if not standings:
        lines.append("暂无数据")
    for i, (u, val) in enumerate(standings[:50], 1):
        g = season_games[cid].get(u, 0)
        tag = "" if g >= SEASON_MIN_GAMES else f"（{g}局·未达标）"
        marker = "👑" if (i == 1 and u in user_titles) else rank_marker(i)
        lines.append(f"{marker} {await get_name(app, u, cid=cid, with_title=False)}：{val}｜{g}局{tag}")
    # 个人排名行：请求者不在前 50 时，单独补一行真实名次，避免大群看不到自己
    if uid is not None and uid in users:
        full_rank = next((i for i, (u, _) in enumerate(standings, 1) if u == uid), None)
        if full_rank is not None and full_rank > 50:
            g = season_games[cid].get(uid, 0)
            tag = "" if g >= SEASON_MIN_GAMES else f"（{g}局·未达标）"
            lines.append(f"…（仅显示前 50，你当前第 {full_rank} 名：{users[uid]} 分{tag}）")
    return lines


async def season_signup(app, cid, uid):
    """报名 / 赛中补报名。处理自动开赛。返回 (ok, key)。key∈joining/started/joined_active。"""
    if uid in season_eliminated.get(cid, set()):
        return False, "eliminated"
    if season_active:
        season_joined.setdefault(cid, set()).add(uid)
        if uid not in season_points.get(cid, {}):
            season_points[cid][uid] = SEASON_START_CHIPS
            season_games[cid][uid] = 0
            season_rebuy[cid][uid] = 0
        save_data()
        return True, "joined_active"
    season_joined.setdefault(cid, set()).add(uid)
    save_data()
    n = len(season_joined[cid])
    if n >= SEASON_MIN_PLAYERS:
        ok, msg = await start_season(cid)
        # 只有真正“首次开赛”的那次才回 started；并发点按钮导致的二次进入回 joined_active
        return True, "started" if (ok and msg != "already_active") else "joined_active"
    return True, "joining"


async def season_lobby_content(app, cid):
    """返回 (text, reply_markup) 排位大厅看板，按赛季状态切换。"""
    if not season_active:
        joined = list(season_joined.get(cid, set()))
        n = len(joined)
        # 列出已报名昵称（最多 15 个，避免刷屏 + 控制 get_chat API 调用量）
        names = [await get_name(app, u) for u in joined[:15]]
        names_text = ("、".join(names) + (f" 等 {n} 人" if n > 15 else "")) if n else "（暂无）"
        text = (f"🏆 <b>排位赛报名大厅</b>\n\n"
                f"当前报名：<b>{n}/{SEASON_MIN_PLAYERS}</b> 人\n"
                f"满 {SEASON_MIN_PLAYERS} 人自动开赛，每人 {SEASON_START_CHIPS} 分，周期 {SEASON_DAYS} 天。\n"
                f"已报名：{names_text}\n"
                f"点下面按钮报名，或用 /排位报名 也能一键报名。")
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton(f"📝 报名参赛（{n}/{SEASON_MIN_PLAYERS}）", callback_data="season_signup")],
            [InlineKeyboardButton("❌ 关闭看板", callback_data="season_lobby_close")],
        ])
    else:
        remain = max(0, int((season_end_ts - now_bj().timestamp()) / 86400))
        sn = html.escape(season_name or '排位赛')  # 防止管理员自定义赛季名含 < 或 & 触发 BadRequest
        text = (f"🏆 <b>第{season_id}赛季「{sn}」进行中</b>\n\n"
                f"⏳ 剩余约 {remain} 天｜上榜需≥{SEASON_MIN_GAMES}局\n"
                f"用 /排位 开局入座；中途想加入点下面按钮。")
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("📝 中途报名加入", callback_data="season_signup")],
            [InlineKeyboardButton("📊 看排位榜", callback_data="season_rank_btn")],
            [InlineKeyboardButton("❌ 关闭看板", callback_data="season_lobby_close")],
        ])
    return text, markup


async def render_season_lobby(app, cid):
    """编辑已有大厅看板，没有则新发。"""
    text, markup = await season_lobby_content(app, cid)
    mid = season_lobby_msg.get(cid)
    if mid:
        try:
            await safe_edit(app.bot, cid, mid, text, reply_markup=markup, parse_mode="HTML")
            return
        except Exception:
            pass
    msg = await safe_send(app.bot, cid, text, reply_markup=markup, parse_mode="HTML")
    if msg:
        season_lobby_msg[cid] = msg.message_id


async def cmd_season_join(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "德州排位赛", "排位"): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    ok, key = await season_signup(context.application, cid, uid)
    if not ok:
        await update.message.reply_text("❌ 你已被淘汰，无法报名本赛季。"); return
    await render_season_lobby(context.application, cid)
    if key == "started":
        await update.message.reply_text(f"🏆 报名满 {SEASON_MIN_PLAYERS} 人，第{season_id}赛季「{season_name or '排位赛'}」开始！每人 {SEASON_START_CHIPS} 分，周期 {SEASON_DAYS} 天。用 /排位 开局。")
    elif key == "joined_active":
        await update.message.reply_text(f"✅ 已加入进行中的赛季（需满 {SEASON_MIN_GAMES} 局才上榜）。当前分 {season_points[cid][uid]}。用 /排位 开局。")
    else:
        n = len(season_joined[cid])
        await update.message.reply_text(f"✅ 已报名本赛季排位赛（{n}/{SEASON_MIN_PLAYERS}）。满 {SEASON_MIN_PLAYERS} 人自动开赛；也可点群里的大厅看板报名。")


async def cmd_season_start(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可强制开赛"); return
    if not await require_group_chat(update, "德州排位赛", "排位"): return
    cid = update.effective_chat.id
    if season_active:
        await update.message.reply_text("⚠️ 本赛季已在进行中。"); return
    name = " ".join(context.args) if context.args else ""
    ok, msg = await start_season(cid, name, forced=True)
    if ok:
        await update.message.reply_text(f"🏆 第{season_id}赛季「{season_name or '排位赛'}」由管理员强制开启！每人 {SEASON_START_CHIPS} 分，周期 {SEASON_DAYS} 天。用 /排位 开局。")
    else:
        await update.message.reply_text(msg)


async def cmd_season_end(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    cid = update.effective_chat.id
    if not season_active:
        await update.message.reply_text("⚠️ 当前无进行中的赛季。"); return
    await season_settle(context.application, manual=True)
    await update.message.reply_text("🏁 赛季已手动结算并重置。")


async def cmd_season_rank(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if not season_active:
        await update.message.reply_text("⚠️ 当前无进行中的赛季排位赛。"); return
    lines = await season_standings_lines(context.application, cid, uid=uid)
    await safe_send_long(context.bot, cid, "\n".join(lines))


async def cmd_god(update, context):
    """查看当前赌神与历届荣誉墙。"""
    if not await need_auth(update): return
    app = context.application
    cid = update.effective_chat.id
    lines = ["👑 <b>🎰赌神 荣誉殿堂</b>", "━" * 16]
    if not user_titles:
        lines.append("当前暂无 🎰赌神。拿下排位赛冠军即可加冕！")
    else:
        uid = next(iter(user_titles))
        lines.append(f"🏅 现任赌神：{await get_name(app, uid, cid=cid, with_title=False)}")
    if champions_history:
        lines.append("", "📜 <b>历届荣誉墙</b>")
        for rec in champions_history[-12:][::-1]:
            streak = rec.get("streak", 1)
            sfx = f" · {streak}连冠" if streak > 1 else ""
            lines.append(f"第{rec['season_id']}赛季：{rec.get('name', '?')}（{rec.get('score', 0)}分）{sfx}")
    else:
        lines.append("", "📜 历届荣誉墙：暂无记录")
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines), parse_mode="HTML")


async def cmd_god_grant(update, context):
    """管理员封赌神（全局唯一，覆盖上任）。"""
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not context.args:
        await update.message.reply_text("用法：/封赌神 <用户ID>"); return
    try:
        uid = int(context.args[0])
    except ValueError:
        await update.message.reply_text("❌ 用户 ID 必须是数字。"); return
    user_titles.clear(); user_titles[uid] = TITLE_GAMBLING_GOD
    save_data()
    await update.message.reply_text(f"👑 已将 {uid} 封为 🎰赌神（覆盖上任）。")


async def cmd_god_revoke(update, context):
    """管理员撤赌神。"""
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not context.args:
        await update.message.reply_text("用法：/撤赌神 <用户ID>"); return
    try:
        uid = int(context.args[0])
    except ValueError:
        await update.message.reply_text("❌ 用户 ID 必须是数字。"); return
    if uid in user_titles:
        del user_titles[uid]
        save_data()
        await update.message.reply_text(f"🔻 已撤销 {uid} 的 🎰赌神 称号。")
    else:
        await update.message.reply_text("ℹ️ 该用户当前没有 🎰赌神 称号。")


async def cmd_season_help(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id
    text = (
        "🏆 <b>德州排位赛使用说明</b>\n\n"
        "<b>报名 / 开局</b>\n"
        "• /排位 — 一键报名（静默）并可在开赛后开/入牌桌；未报名会自动补报\n"
        "• /排位报名 — 报名并弹出群里「报名大厅」看板（满 20 自动开赛）\n"
        "• 大厅看板按钮：📝 报名参赛 / 📝 中途报名加入\n\n"
        "<b>查询</b>\n"
        "• /排位榜 — 看当前排名（榜尾显示你的名次）\n"
        "• /赌神 — 查看 🎰赌神 称号与历届荣誉墙\n"
        "• 大厅看板按钮：📊 看排位榜\n\n"
        "<b>管理员专属</b>\n"
        "• /排位开赛 [赛季名] — 强制开赛（可自定义名，如 /排位开赛 赌神大战秋季赛）\n"
        "• /排位结束 — 提前结算并推最终榜\n\n"
        "<b>自动机制</b>\n"
        "• 每日 23:00 自动推一次排位榜\n"
        "• 开赛后第 7 天（到点后的首个午夜）自动结算，可能晚最多约 24 小时\n\n"
        "📌 满 20 人开赛；起始 20000 分；输光可应急补分 3×2000，再输光淘汰；满 5 局才上榜。\n"
        "💡 以上「排位」命令均可换「赛季」前缀，含义完全相同，如 /赛季榜 /赛季报名 /赛季开赛 /赛季结束。\n"
        "⚠️ 群里若中文命令无反应，多为 BotFather 隐私模式拦截，发 /setprivacy → Disable 即可。"
    )
    await safe_send_long(context.bot, cid, text, parse_mode="HTML")


async def cmd_season_play(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "德州排位赛", "排位"): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if not season_active:
        ok, key = await season_signup(context.application, cid, uid)
        if not ok:
            await update.message.reply_text("❌ 你已被淘汰，无法参加本赛季排位。"); return
        if key == "started":
            await render_season_lobby(context.application, cid)  # 满 20 自动开赛：翻转看板为进行中，继续往下开房
        else:
            # UX2：/排位 静默报名不弹看板（看板仅在 /排位报名 或按钮点击时出现，减少刷屏）
            n = len(season_joined[cid])
            await update.message.reply_text(f"✅ 已报名本赛季排位赛（{n}/{SEASON_MIN_PLAYERS}）。满 {SEASON_MIN_PLAYERS} 人自动开赛；发 /排位报名 可看报名大厅。")
            return
    # 赛季进行中：开 / 入房间（赛中未报名者自动补报名）
    if uid in season_eliminated.get(cid, set()):
        await update.message.reply_text("❌ 你已被淘汰，无法参加本赛季排位。"); return
    if uid not in season_joined.get(cid, set()):
        season_joined.setdefault(cid, set()).add(uid)
        if uid not in season_points.get(cid, {}):
            season_points[cid][uid] = SEASON_START_CHIPS
            season_games[cid][uid] = 0
            season_rebuy[cid][uid] = 0
        save_data()
    if season_points[cid][uid] <= 0:
        await update.message.reply_text("❌ 你的排位分已用完，等待应急补分或下局。"); return
    game = active_poker_games.get(cid)
    if game:
        if game.season:
            if game.phase != "waiting": await update.message.reply_text("当前已有进行中的排位赛。"); return
            if game.add(uid):
                await update_poker_waiting(game, context.application); await update.message.reply_text("已加入当前等待房间。")
            else: await update.message.reply_text("你已在等待房间中。")
            return
        else:
            await update.message.reply_text("当前有日常德州房间，请先 /结束 后再开排位赛。"); return
    game = PokerGame(cid, uid, current_game_mode(), season=True); game.add(uid); active_poker_games[cid] = game
    msg = await safe_send(context.bot, cid, await poker_waiting_text(game, context.application), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("📥 加入游戏", callback_data="texas_join")], [InlineKeyboardButton("❌ 终止房间", callback_data="texas_end")]]))
    if msg:
        game.game_msg_id = msg.message_id
        await start_wait_timeout(game, context.application)

async def cmd_sm(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "赛马", "sm"): return
    cid = update.effective_chat.id
    if cid in active_horse_races:
        race = active_horse_races[cid]
        # 已有赛马：直接把当前带按钮的看板重发出来，让后发的人也能立刻看到/参与，而不是只回一句文字
        if getattr(race, "phase", "") == "betting":
            msg = await safe_send(context.bot, cid, await race.view(context.application), reply_markup=race.buttons())
            if msg: race.game_msg_id = msg.message_id
        else:
            await update.message.reply_text("当前已有赛马进行中。")
        return
    mode = current_game_mode()
    jackpot = race_jackpot.pop(cid, 0) if mode == "official" else 0
    race = HorseRace(cid, update.effective_user.id, jackpot, mode); active_horse_races[cid] = race
    msg = await safe_send(context.bot, cid, await race.view(context.application), reply_markup=race.buttons())
    if msg: race.game_msg_id = msg.message_id
    race.task = asyncio.create_task(race.run(context.application)); save_data()

async def refund_poker(game, app, notice):
    """终止未结算牌局时，按开局积分退还全部 ante、盲注和后续下注。"""
    game.cancel_timer(); game.cancel_auto(); game.cancel_wait()
    wallet = season_points if game.season else texas_chips
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
    sb_game = active_sicbo_games.get(cid)
    nn_game = active_niuniu_games.get(cid)

    if not any([poker, race, gomoku, mine, bj, bjl, sb_game, nn_game]):
        await update.message.reply_text("当前没有进行中的游戏。"); return

    notices = []
    # 如果带了参数，只针对性关闭
    target_all = (arg == "")
    
    if gomoku and (target_all or arg in ["wz", "wzq", "gomoku", "五子棋"]):
        if is_bot_admin(uid) or uid in gomoku.players:
            await cancel_gomoku(gomoku, context.application, "🛑 五子棋已终止。")
            notices.append("五子棋已终止")

    if poker and (target_all or arg in ["dz", "dzpk", "texas", "德州"]):
        if is_bot_admin(uid) or uid in poker.players:
            await refund_poker(poker, context.application, "🛑 德州扑克已终止，积分已退回。")
            notices.append("德州已退款")

    if race and (target_all or arg in ["sm", "race", "赛马"]):
        if is_bot_admin(uid) or uid in race.bets:
            if race.phase == "betting":
                if race.task and not race.task.done(): race.task.cancel()
                await race.refund(context.application, "🛑 赛马已终止，积分已退回。")
                notices.append("赛马已退款")
            else: notices.append("赛马进行中无法终止")

    if bj and (target_all or arg in ["21", "bj", "21点"]):
        if is_bot_admin(uid) or uid in bj.players:
            bj.cancel_timer(); bj.cancel_wait()
            wallet = game_chips
            for p_uid, b in bj.bets.items():
                wallet[cid][p_uid] += b
                pending_game_bets[cid].get(p_uid, {}).pop("21", None)
            active_blackjack_games.pop(cid, None)
            await safe_edit(context.bot, cid, bj.game_msg_id, "🛑 21点已终止，积分已退回。", reply_markup=None)
            notices.append("21点已退款")

    if bjl: # 百家乐特殊判断，因为 arg 可能对应 bjl
        if target_all or arg in ["bjl", "baccarat", "百家乐"]:
            if is_bot_admin(uid) or uid in bjl.bets.keys():
                bjl.cancel_timer()
                wallet = game_chips
                for p_uid, b_dict in bjl.bets.items():
                    for amount in b_dict.values(): wallet[cid][p_uid] += amount
                    pending_game_bets[cid].get(p_uid, {}).pop("baccarat", None)
                active_baccarat_games.pop(cid, None)
                await safe_edit(context.bot, cid, bjl.game_msg_id, "🛑 百家乐已终止，积分已退回。", reply_markup=None)
                notices.append("百家乐已退款")

    if mine and (target_all or arg in ["sl", "sldz", "mine", "扫雷"]):
        if is_bot_admin(uid) or uid in mine.players:
            active_minesweeper_games.pop(cid, None)
            await safe_edit(context.bot, cid, mine.game_msg_id, "🛑 扫雷已终止。", reply_markup=None)
            notices.append("扫雷已终止")

    if sb_game and (target_all or arg in ["sb", "sicbo", "骰子"]):
        if is_bot_admin(uid) or uid in sb_game.bets.keys() or uid == sb_game.owner_id:
            sb_game.cancel_timer()
            wallet = game_chips
            for p_uid, b_dict in sb_game.bets.items(): wallet[cid][p_uid] += sum(b_dict.values())
            active_sicbo_games.pop(cid, None)
            await safe_edit(context.bot, cid, sb_game.game_msg_id, "🛑 骰子已终止，积分已退回。", reply_markup=None)
            notices.append("骰子已退款")

    if nn_game and (target_all or arg in ["nn", "niuniu", "牛牛"]):
        if is_bot_admin(uid) or uid in nn_game.players or uid == nn_game.owner_id:
            nn_game.cancel_wait()
            active_niuniu_games.pop(cid, None)
            await safe_edit(context.bot, cid, nn_game.game_msg_id, "🛑 牛牛已终止。", reply_markup=None)
            notices.append("牛牛已终止")

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
        await update.message.reply_text("该玩家正在游戏中，无法修改积分。"); return
    game_chips[cid][uid] += amount; save_data()
    await update.message.reply_text(f"✅ 已增加 {await get_name(context.application, uid)} {amount} 积分。")



async def cmd_adddz(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not await need_auth(update): return
    try:
        uid, amount = await _parse_target_amount(update, context)
        if amount <= 0: raise ValueError
    except (ValueError, IndexError):
        await update.message.reply_text("用法：/adddz 用户ID 数量，或回复玩家消息后使用 /adddz 数量"); return
    cid = update.effective_chat.id
    if player_is_busy(cid, uid):
        await update.message.reply_text("该玩家正在游戏中，无法修改积分。"); return
    texas_chips[cid][uid] += amount; save_data()
    await update.message.reply_text(f"✅ 已给 {await get_name(context.application, uid)} 添加 {amount} 德州积分，当前 {texas_chips[cid][uid]}。")


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
        await update.message.reply_text("该玩家正在游戏中，无法修改积分。"); return
    if game_chips[cid][uid] < amount:
        await update.message.reply_text("❌ 玩家积分不足。"); return
    game_chips[cid][uid] -= amount; save_data()
    await update.message.reply_text(f"✅ 已扣除 {await get_name(context.application, uid)} {amount} 积分。")


async def cmd_cx(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id
    date = business_date()
    texas = poker_profit_by_date[date].get(cid, {})
    combined = {}
    for g in (blackjack_profit_by_date, race_profit_by_date, baccarat_profit_by_date, slot_profit_by_date):
        for uid, v in total_profit_by_game(g, cid).items():
            combined[uid] = combined.get(uid, 0) + v
    if not texas and not combined:
        await update.message.reply_text("当前业务日暂无盈亏记录。"); return
    lines = ["🃏 德州当日盈亏", "━"*14]
    if texas:
        for i, (uid, value) in enumerate(sorted(texas.items(), key=lambda x:x[1], reverse=True)[:50], 1):
            lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：{value:+d}")
    else:
        lines.append("暂无记录")
    lines.extend(["", "🎮 通用游戏累计盈亏", "━"*14])
    if combined:
        for i, (uid, value) in enumerate(sorted(combined.items(), key=lambda x:x[1], reverse=True)[:50], 1):
            lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：{value:+d}")
    else:
        lines.append("暂无记录")
    await safe_send_long(context.bot, cid, "\n".join(lines))

async def cmd_ph(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id
    lines = ["💰 德州积分榜", "━"*14]
    for i, (uid, value) in enumerate(sorted(texas_chips[cid].items(), key=lambda x:x[1], reverse=True)[:50], 1):
        lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：{value}")
    lines.extend(["", "🎮 通用积分榜", "━"*14])
    for i, (uid, value) in enumerate(sorted(game_chips[cid].items(), key=lambda x:x[1], reverse=True)[:50], 1):
        lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：{value}")
    await safe_send_long(context.bot, cid, "\n".join(lines))

async def cmd_sq(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not is_group_chat(update):
        await update.message.reply_text("⚠️ 授权需在群聊中进行：请在目标群里发送 /授权，机器人会把该群加入授权名单。私聊里授权无意义，且会导致游戏开在私聊、别人看不到。")
        return
    cid = update.effective_chat.id
    AUTHORIZED_GROUPS.add(cid); save_data()
    await update.message.reply_text(f"✅ 当前群已授权：{cid}")

async def cmd_qxshouquan(update, context):
    if not is_bot_admin(update.effective_user.id): return
    try: cid = int(context.args[0])
    except (IndexError, ValueError): await update.message.reply_text("用法：/qxshouquan 群ID"); return
    AUTHORIZED_GROUPS.discard(cid); save_data(); await update.message.reply_text(f"✅ 已取消授权 {cid}")

async def cmd_addadmin(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    try: uid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("用法：/addadmin 用户ID，例如 /addadmin 123456789"); return
    if uid in BOT_ADMINS:
        await update.message.reply_text(f"ℹ️ {uid} 已经是管理员了"); return
    BOT_ADMINS.add(uid); save_data()
    await update.message.reply_text(f"✅ 已添加机器人管理员：{uid}")

async def cmd_deladmin(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    try: uid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("用法：/deladmin 用户ID，例如 /deladmin 123456789"); return
    if uid in ADMIN_USER_IDS:
        await update.message.reply_text(f"⚠️ {uid} 是种子管理员，重启后自动恢复，无法移除（如需移除请改代码 ADMIN_USER_IDS）"); return
    if uid not in BOT_ADMINS:
        await update.message.reply_text(f"ℹ️ {uid} 不是管理员"); return
    BOT_ADMINS.discard(uid); save_data()
    await update.message.reply_text(f"✅ 已移除机器人管理员：{uid}")

async def cmd_admin_list(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    seeds = set(ADMIN_USER_IDS)
    dynamic = BOT_ADMINS - seeds
    lines = ["👑 <b>当前机器人管理员</b>",
             f"共 <b>{len(BOT_ADMINS)}</b> 人（种子 {len(seeds)} + 动态 {len(dynamic)}）", ""]
    lines.append("🔒 种子管理员（重启保留，不可被 /deladmin 移除）：")
    for uid in sorted(seeds):
        lines.append(f"  • {await get_name(context.application, uid)}（{uid}）")
    lines.append("")
    if dynamic:
        lines.append("➕ 动态添加（可被 /deladmin 移除）：")
        for uid in sorted(dynamic):
            lines.append(f"  • {await get_name(context.application, uid)}（{uid}）")
    else:
        lines.append("（暂无动态添加的管理员）")
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines), parse_mode="HTML")

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
        _remember_name(update)
        if not is_auth(cid): await q.answer("未授权", show_alert=True); return
        
        # --- 21点 回调 ---
        if data.startswith("bj_"):
            game = active_blackjack_games.get(cid)
            if not game: await q.answer("游戏已结束", show_alert=True); return
            if data.startswith("bj_join_"):
                bet = int(data.split("_")[2])
                wallet = game_chips
                if wallet[cid][uid] < bet: await q.answer("积分不足", show_alert=True); return
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
                card = game.hit(uid); await q.answer(f"你抽到了 {game.get_card_str([card])}")
                if game.phase == "finished" or game.phase == "dealer_turn": await update_blackjack_ui(game, context.application)
                else: await update_blackjack_ui(game, context.application); await start_bj_turn_timer(game, context.application)
            elif data.startswith("bj_stand_"):
                if uid not in game.players:
                    await q.answer("❌ 你未参与本局游戏。", show_alert=True); return
                if str(uid) != data.split("_")[2]: await q.answer("不是你的回合", show_alert=True); return
                # 额外校验：必须当前确为该玩家回合，防止旧按钮双击跳过下一位玩家
                if game.players[game.current_player_idx] != uid: await q.answer("不是你的回合", show_alert=True); return
                game.next_player(); await q.answer("停牌")
                if game.phase == "finished" or game.phase == "dealer_turn": await update_blackjack_ui(game, context.application)
                else: await update_blackjack_ui(game, context.application); await start_bj_turn_timer(game, context.application)
            elif data.startswith("bj_double_"):
                if uid not in game.players:
                    await q.answer("❌ 你未参与本局游戏。", show_alert=True); return
                if str(uid) != data.split("_")[2]: await q.answer("不是你的回合", show_alert=True); return
                wallet = game_chips
                if wallet[cid][uid] < game.bets[uid]: await q.answer("积分不足，无法双倍", show_alert=True); return
                
                # 原子化：先让 game 校验回合并翻倍（内部翻倍 bets + 更新退款保护），
                # 仅成功才扣钱；避免超时/重复点击导致静默丢分
                prev_bet = game.bets[uid]
                if not game.double_down(uid):
                    await q.answer("操作失败：已不是你的回合", show_alert=True); return
                wallet[cid][uid] -= prev_bet
                await q.answer("双倍下注！摸牌并停牌")
                await action_notice(cid, context.application, uid, "选择了双倍下注！")
                
                if game.phase == "finished" or game.phase == "dealer_turn": await update_blackjack_ui(game, context.application)
                else: await update_blackjack_ui(game, context.application); await start_bj_turn_timer(game, context.application)
            elif data == "bj_end":
                if not is_bot_admin(uid) and uid != game.owner_id: await q.answer("权限不足", show_alert=True); return
                game.cancel_timer(); game.cancel_wait()
                # 退还本局下注
                wallet = game_chips
                for p_uid, bet in game.bets.items():
                    wallet[cid][p_uid] += bet
                    pending_game_bets[cid].get(p_uid, {}).pop("21", None)
                active_blackjack_games.pop(cid, None)
                await safe_edit(context.bot, cid, game.game_msg_id, "🛑 21点已手动终止，积分已退回。", reply_markup=None)
            return

        # --- 百家乐 回调 ---
        if data.startswith("bjl_"):
            game = active_baccarat_games.get(cid)
            if not game: await q.answer("游戏已结束", show_alert=True); return
            if data.startswith("bjl_bet_"):
                side = data.split("_")[2]
                bet_amount = BACCARAT_FIXED_BET # 引用全局配置
                wallet = game_chips
                if wallet[cid][uid] < bet_amount: await q.answer("积分不足", show_alert=True); return
                wallet[cid][uid] -= bet_amount
                game.place_bet(uid, side, bet_amount)
                side_names = {"player":"闲", "banker":"庄", "tie":"和"}
                await q.answer(f"✅ 押注 {side_names.get(side, side)} 成功 (累计: {game.bets[uid][side]})", show_alert=False)
                await update_baccarat_ui(game, context.application)
            elif data == "bjl_start":
                if uid != game.owner_id: await q.answer("仅发起人可开始", show_alert=True); return
                if not game.bets:
                    game.cancel_timer()
                    active_baccarat_games.pop(cid, None)
                    await q.answer("无人下注，本局已取消", show_alert=True)
                    await safe_edit(context.bot, cid, game.game_msg_id, "🛑 百家乐无人下注，本局已取消。", reply_markup=None)
                    return
                await settle_baccarat(game, context.application)
            elif data == "bjl_end":
                if not is_bot_admin(uid) and uid != game.owner_id: await q.answer("权限不足", show_alert=True); return
                game.cancel_timer()
                # 退还本局下注
                wallet = game_chips
                for p_uid, b_dict in game.bets.items():
                    for amount in b_dict.values(): wallet[cid][p_uid] += amount
                    pending_game_bets[cid].get(p_uid, {}).pop("baccarat", None)
                active_baccarat_games.pop(cid, None)
                await safe_edit(context.bot, cid, game.game_msg_id, "🛑 百家乐已手动终止，积分已退回。", reply_markup=None)
            return

        # --- 骰子 回调 ---
        if data.startswith("sb_"):
            game = active_sicbo_games.get(cid)
            if not game: await q.answer("游戏已结束", show_alert=True); return
            if data.startswith("sb_amt_"):
                amt = int(data.split("_")[2])
                game.amounts[uid] = amt; game.last_amount = amt
                await q.answer(f"已切换到 {amt} 积分")
                await update_sicbo_ui(game, context.application)
            elif data.startswith("sb_bet_spec_"):
                n = int(data.split("_")[3]); amt = game.get_amount(uid)
                if game_chips[cid][uid] < amt: await q.answer("积分不足", show_alert=True); return
                game_chips[cid][uid] -= amt; game.place_bet(uid, f"spec_{n}", amt)
                await q.answer(f"✅ 押围骰 {n}{n}{n} ({amt}积分)")
                await update_sicbo_ui(game, context.application)
            elif data.startswith("sb_bet_sum_"):
                s = int(data.split("_")[3]); amt = game.get_amount(uid)
                if game_chips[cid][uid] < amt: await q.answer("积分不足", show_alert=True); return
                game_chips[cid][uid] -= amt; game.place_bet(uid, f"sum_{s}", amt)
                await q.answer(f"✅ 押总点数 {s} ({amt}积分)")
                await update_sicbo_ui(game, context.application)
            elif data.startswith("sb_bet_"):
                bet_type = data.split("_")[2]; amt = game.get_amount(uid)
                if game_chips[cid][uid] < amt: await q.answer("积分不足", show_alert=True); return
                game_chips[cid][uid] -= amt; game.place_bet(uid, bet_type, amt)
                await q.answer(f"✅ 押 {SICBO_BET_NAMES.get(bet_type, bet_type)} ({amt}积分)")
                await update_sicbo_ui(game, context.application)
            elif data == "sb_start":
                if uid != game.owner_id: await q.answer("仅发起人可开始", show_alert=True); return
                await q.answer("🎲 正在开牌...")
                game.cancel_timer(); await settle_sicbo(game, context.application)
            elif data == "sb_end":
                if not is_bot_admin(uid) and uid != game.owner_id: await q.answer("权限不足", show_alert=True); return
                game.cancel_timer()
                for p_uid, b_dict in game.bets.items(): game_chips[cid][p_uid] += sum(b_dict.values())
                active_sicbo_games.pop(cid, None)
                await safe_edit(context.bot, cid, game.game_msg_id, "🛑 骰子已手动终止，积分已退回。", reply_markup=None)
            return

        # --- 牛牛 回调 ---
        if data.startswith("nn_"):
            game = active_niuniu_games.get(cid)
            if not game: await q.answer("游戏已结束", show_alert=True); return
            if data == "nn_join":
                if not game.add(uid): await q.answer("无法加入：积分不足或房间已满", show_alert=True); return
                await q.answer("已加入牛牛"); await update_niuniu_ui(game, context.application)
            elif data == "nn_robot":
                if uid != game.owner_id and not is_bot_admin(uid): await q.answer("仅发起人可加电脑人", show_alert=True); return
                if not game.add_robot(): await q.answer("房间已满", show_alert=True); return
                await q.answer("已加入电脑人"); await update_niuniu_ui(game, context.application)
            elif data == "nn_start":
                if uid != game.owner_id: await q.answer("仅发起人可开始", show_alert=True); return
                if len(game.players) < NIUNIU_MIN_PLAYERS: await q.answer("人数不足", show_alert=True); return
                game.cancel_wait(); await settle_niuniu(game, context.application)
            elif data == "nn_leave":
                if not game.leave(uid): await q.answer("你不在房间内", show_alert=True); return
                await q.answer("已退出"); await update_niuniu_ui(game, context.application)
            elif data == "nn_end":
                if not is_bot_admin(uid) and uid != game.owner_id: await q.answer("权限不足", show_alert=True); return
                game.cancel_wait()
                active_niuniu_games.pop(cid, None)
                await safe_edit(context.bot, cid, game.game_msg_id, "🛑 牛牛已手动终止。", reply_markup=None)
            return


        # --- 老虎机连抽回调（绑定发起人） ---
        if data.startswith("lhj_spin_"):
            parts = data.split("_")
            try:
                count = int(parts[2]); owner = int(parts[3])
            except (ValueError, IndexError):
                await q.answer("无效操作", show_alert=True); return
            if uid != owner:
                await q.answer("这是别人的老虎机界面，请自己发送 /lhj", show_alert=True); return
            if count not in (1, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000):
                await q.answer("无效操作", show_alert=True); return
            ok, result_text = await run_slot_spins(context, cid, uid, count, answer=q.answer)
            if ok and q.message:
                # 抽奖成功后原地编辑为开奖结果（1 次 API，比删除+发送省一半请求）；编辑失败则直接发送
                edited = await safe_edit(context.bot, cid, q.message.message_id, result_text, reply_markup=None, parse_mode="HTML")
                if edited is None:
                    await safe_send(context.bot, cid, result_text, parse_mode="HTML")
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
            if not is_bot_admin(uid) and uid not in game.players:
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
        if data.startswith("season_"):
            if data == "season_signup":
                ok, key = await season_signup(context.application, cid, uid)
                if not ok:
                    await q.answer("你已被淘汰，无法报名", show_alert=True); return
                await render_season_lobby(context.application, cid)
                if key == "started":
                    await q.answer("🏆 报名已满，赛季自动开始！用 /排位 开局", show_alert=True)
                elif key == "joined_active":
                    await q.answer("✅ 已加入进行中的赛季")
                else:
                    await q.answer("✅ 已报名")
                return
            if data == "season_lobby_close":
                mid = season_lobby_msg.pop(cid, None)
                if mid: await safe_delete(context.bot, cid, mid)
                await q.answer("已关闭看板"); return
            if data == "season_rank_btn":
                if not season_active:
                    await q.answer("当前无进行中的赛季", show_alert=True); return
                lines = await season_standings_lines(context.application, cid, uid=uid)
                await safe_send_long(context.bot, cid, "\n".join(lines))
                await q.answer("已发送排位榜"); return
            await q.answer("未知操作", show_alert=True); return
        if data.startswith("texas_"):
            game = active_poker_games.get(cid)
            if data == "texas_reveal":
                await handle_texas_reveal(cid, uid, q, context); return
            if not game: await q.answer("德州游戏已结束", show_alert=True); return
            if data == "texas_hand":
                hand = game.hands.get(uid); await q.answer(f"你的手牌：{card_str(hand[0])}  {card_str(hand[1])}" if hand and uid not in game.folded else "当前无法查看手牌", show_alert=True); return
            if data == "texas_end":
                if not is_bot_admin(uid) and uid not in game.players:
                    await q.answer("权限不足", show_alert=True); return
                await refund_poker(game, context.application, "🛑 德州已终止，积分已退回。")
                await q.answer("本局已终止")
                return
            if game.phase == "waiting":
                if data == "texas_join":
                    if game.season:
                        if uid in season_eliminated.get(cid, set()):
                            await q.answer("已淘汰，无法加入", show_alert=True); return
                        if uid not in season_joined.get(cid, set()):
                            season_joined.setdefault(cid, set()).add(uid)
                            if uid not in season_points.get(cid, {}):
                                season_points[cid][uid] = SEASON_START_CHIPS
                                season_games[cid][uid] = 0
                                season_rebuy[cid][uid] = 0
                            save_data()
                        if season_points[cid][uid] <= 0:
                            await q.answer("排位分不足，无法加入", show_alert=True); return
                    else:
                        wallet = texas_chips
                        if wallet[cid][uid] < MIN_ENTRY_CHIPS:
                            await q.answer(f"进入德州至少需要 {MIN_ENTRY_CHIPS} 积分", show_alert=True); return
                    if game.add(uid):
                        await q.answer("已加入"); await update_poker_waiting(game, context.application)
                    else: await q.answer("你已在等待房间中。", show_alert=True)
                elif data == "texas_start" and uid == game.owner_id and game.start():
                    game.cancel_wait()
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
                if not is_bot_admin(uid) and uid not in game.players:
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
    # 外层 try 包命令分发；开头校验单独内层 try（消息结构异常属噪音，静默忽略）
    try:
        # 开头校验：无效消息静默跳过，不打扰用户
        try:
            message, user = update.effective_message, update.effective_user
            if not message or not message.text or not user or user.is_bot: return
            if message.date and (datetime.now(timezone.utc) - message.date).total_seconds() > STALE_TEXT_COMMAND_SECONDS:
                return
            cid, text = update.effective_chat.id, message.text.strip()
            _remember_name(update)
        except Exception:
            return

        # 不带 / 的命令直达：若首词是已知命令别名，按命令处理
        _words = text.split()
        if _words and _words[0] in CMD_ALIASES:
            await _dispatch_alias(_words[0], _words[1:], update, context)
            return
        
        # 深度防御：非命令的游戏交互（下注/落子/加注）仅在授权群内处理，
        # 与 on_button 对齐；命令分发仍在上面由各自 cmd_* 自行校验权限
        if not is_auth(cid):
            return
        
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
                    msg = await safe_send(context.bot, cid, await poker_waiting_text(poker, context.application), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("📥 加入游戏", callback_data="texas_join")], [InlineKeyboardButton("❌ 终止房间", callback_data="texas_end")]]))
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
            wallet = game_chips
            if wallet[cid][user.id] < amount:
                await message.reply_text(f"❌ 积分不足，你只有 {wallet[cid][user.id]}。"); return
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
            wallet = game_chips
            if wallet[cid][user.id] < amount:
                await message.reply_text(f"❌ 积分不足，你只有 {wallet[cid][user.id]}。"); return
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
            # 文字输入为 1 基坐标，转为 0 基（与按钮一致）
            r = (int(match.group(1)) if match.group(1) is not None else int(match.group(3))) - 1
            c = (int(match.group(2)) if match.group(2) is not None else int(match.group(4))) - 1
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
        # 命令分发异常不再静默：给用户明确反馈，便于排查而非毫无反应
        try:
            await message.reply_text("⚠️ 指令处理出错，请联系管理员。")
        except Exception:
            pass


# ---------- 定时任务与启动 ----------
async def daily_reset_scheduler(app):
    global last_business_date
    today = now_bj().strftime("%Y-%m-%d")
    # 第一次启动只记录业务日，避免因部署重启立刻重置玩家积分。
    if not last_business_date:
        last_business_date = today; save_data()
    while True:
        now = now_bj(); target = (now + timedelta(days=1)).replace(hour=0, minute=0, second=1, microsecond=0)
        await asyncio.sleep((target-now).total_seconds())
        today = now_bj().strftime("%Y-%m-%d")
        # 排位赛到点自动结算（end_ts 为开赛+7天的时间戳）
        if season_active and now_bj().timestamp() >= season_end_ts:
            await season_settle(app)
        # 午夜仅清理德州榜单（德州当日榜）；其他游戏榜单不清空，累计为总数
        poker_profit_by_date.clear()
        # 不重置正在进行正式德州或赛马中的玩家，避免跨日覆盖未结算状态。
        protected = set()
        for poker in active_poker_games.values():
            if poker.phase != "waiting":
                protected.update((poker.chat_id, uid) for uid in poker.players)
        # 仅 texas_chips 每日重置；赛马/21点/百家乐用 game_chips（永久不清零），
        # 故无需把它们的玩家加入保护集（原 race/bj/bjl 分支为无效死代码，已移除）
        for chat_id, users in texas_chips.items():
            for uid in users:
                if (chat_id, uid) not in protected:
                    users[uid] = STARTING_CHIPS
        for cid in race_daily_stats: race_daily_stats[cid] = [0] * HORSE_COUNT
        for cid in baccarat_daily_stats: baccarat_daily_stats[cid] = {"player": 0, "banker": 0, "tie": 0}
        archive_old_profit_data()
        daily_emergency_used.clear(); last_business_date = today; save_data()

async def leaderboard_scheduler(app):
    while True:
        now = now_bj(); target = now.replace(hour=23, minute=0, second=0, microsecond=0)
        if target <= now: target += timedelta(days=1)
        await asyncio.sleep((target-now).total_seconds())
        # 只推送并清空德州当日榜；其他游戏榜保留累计（总数）
        date = now_bj().strftime("%Y-%m-%d"); texas_snapshot = poker_profit_by_date.pop(date, {})
        for cid, data in texas_snapshot.items():
            if not data: continue
            lines = [f"🏆 德州当日排行榜（{date}）", "━"*14]
            for i, (uid, amount) in enumerate(sorted(data.items(), key=lambda x:x[1], reverse=True)[:50], 1): lines.append(f"{rank_marker(i)} {await get_name(app, uid)}：{amount:+d}")
            await safe_send_long(app.bot, cid, "\n".join(lines))
        # 排位赛每日推一次当前榜，给群友紧迫感
        if season_active:
            for cid in list(season_points.keys()):
                lines = await season_standings_lines(app, cid)
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


# ---------- 数据备份/恢复 ----------
async def cmd_backup(update, context):
    """管理员备份：把数据文件发送到管理员私聊。"""
    uid = update.effective_user.id
    if not is_bot_admin(uid):
        await update.message.reply_text("⛔ 仅管理员可用")
        return
    # 强制写盘，确保文件是最新的
    ok = await asyncio.to_thread(force_save_now)
    if not ok:
        await update.message.reply_text("⚠️ 写盘失败，请稍后再试")
        return
    if not os.path.exists(DATA_FILE):
        await update.message.reply_text("⚠️ 数据文件不存在")
        return
    try:
        with open(DATA_FILE, "rb") as f:
            await context.bot.send_document(
                chat_id=uid,
                document=f,
                filename=f"bot_backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
                caption="📦 数据备份完成",
            )
        # 在群里发的命令时，提示一下文件已发到私聊
        if update.effective_chat.id != uid:
            await update.message.reply_text("✅ 备份文件已发送到你的私聊")
    except Exception:
        logger.exception("备份失败")
        await update.message.reply_text("⚠️ 备份失败，请先私聊我发 /start 后再试")


async def cmd_restore(update, context):
    """管理员恢复：回复一个 JSON 备份文件来恢复数据，恢复后自动重启。"""
    global data_dirty
    uid = update.effective_user.id
    if not is_bot_admin(uid):
        await update.message.reply_text("⛔ 仅管理员可用")
        return
    replied = update.message.reply_to_message
    if not replied or not replied.document:
        await update.message.reply_text("⚠️ 请回复一个 JSON 备份文件，再发送 /restore\n\n用法：点开备份文件 → 回复 → 发送 /restore")
        return
    tmp_path = f"{DATA_FILE}.restore_tmp"
    try:
        # 下载并验证备份文件
        tg_file = await context.bot.get_file(replied.document.file_id)
        await tg_file.download_to_drive(tmp_path)
        with open(tmp_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            raise ValueError("备份文件格式错误：不是字典")
        # 验证通过：先阻止后台保存线程用旧数据覆盖新文件
        data_dirty = False
        if save_event is not None:
            save_event.clear()
        # 把当前数据另存一份，再写入新数据
        if os.path.exists(DATA_FILE):
            shutil.copy2(DATA_FILE, f"{DATA_FILE}.restore_bak")
        os.replace(tmp_path, DATA_FILE)
        await update.message.reply_text("✅ 数据恢复成功，正在重启加载新数据…")
        logger.warning("管理员 %s 执行了数据恢复，进程即将退出重启", uid)
        # 强制退出（不走 post_shutdown，避免内存旧数据覆盖）；Railway 会自动重启容器
        os._exit(1)
    except json.JSONDecodeError:
        await update.message.reply_text("⚠️ 文件不是有效的 JSON 格式，恢复已取消")
        if os.path.exists(tmp_path):
            os.remove(tmp_path)
    except Exception as e:
        logger.exception("恢复失败")
        await update.message.reply_text(f"⚠️ 恢复失败：{e}")
        if os.path.exists(tmp_path):
            os.remove(tmp_path)


async def post_init(app):
    background_tasks.update({
        asyncio.create_task(daily_reset_scheduler(app)), 
        asyncio.create_task(leaderboard_scheduler(app)), 
        asyncio.create_task(hourly_race_scheduler(app)),
        asyncio.create_task(data_save_worker()) 
    })
    # 注册 Telegram 原生命令菜单（仅支持拉丁字符命令，中文命令走自定义路由）。
    # 作用：群里打 / 能看到、能点；命令以 bot_command 实体发送，不受隐私模式影响，必定送达。
    try:
        menu = [
            BotCommand("start", "开始 / 菜单 / 帮助"),
            BotCommand("dz", "德州扑克"),
            BotCommand("rig", "德州控牌(测试)"),
            BotCommand("sm", "赛马"),
            BotCommand("wz", "五子棋"),
            BotCommand("sl", "扫雷"),
            BotCommand("lhj", "老虎机"),
            BotCommand("21", "21点"),
            BotCommand("bjl", "百家乐"),
            BotCommand("sb", "骰子"),
            BotCommand("nn", "牛牛"),
            BotCommand("end", "结束当前游戏"),
            BotCommand("add", "加积分"),
            BotCommand("adddz", "加德州积分"),
            BotCommand("reduce", "减积分"),
            BotCommand("cx", "盈亏查询"),
            BotCommand("ph", "排行榜"),
            BotCommand("sq", "授权群组"),
            BotCommand("qxshouquan", "取消授权"),
            BotCommand("addadmin", "添加机器人管理员"),
            BotCommand("deladmin", "移除机器人管理员"),
            BotCommand("adminlist", "查看管理员列表"),
            BotCommand("autosm", "切换整点自动赛马"),
            BotCommand("backup", "备份数据"),
            BotCommand("restore", "恢复数据"),
            BotCommand("season", "德州排位赛"),
            BotCommand("seasonjoin", "排位报名"),
            BotCommand("seasonrank", "排位榜"),
            BotCommand("seasonhelp", "排位赛帮助"),
            BotCommand("seasonstart", "排位强制开赛(管理员)"),
            BotCommand("seasonend", "排位提前结算(管理员)"),
            BotCommand("god", "赌神称号/荣誉墙"),
            BotCommand("godgrant", "封赌神(管理员)"),
            BotCommand("godrevoke", "撤赌神(管理员)"),
        ]
        await app.bot.set_my_commands(menu)
    except Exception:
        logger.warning("注册命令菜单失败（不影响主功能）")


async def post_shutdown(app):
    force_save_now()


async def cmd_rig(update, context):
    """管理员：控制德州控牌（测试用）。/rig 查看状态；/rig <id> 开启；/rig off 关闭。"""
    global RIGGED_PLAYER
    uid = update.effective_user.id
    if uid != ADMIN_USER_ID:
        await update.message.reply_text("⛔ 仅机器人所有者（默认管理员）可操作控牌")
        return
    args = context.args or []
    if not args:
        state = f"🎯 当前控牌已开启，目标用户：{RIGGED_PLAYER}" if RIGGED_PLAYER else "⚪ 当前控牌已关闭"
        await update.message.reply_text(
            f"{state}\n（目标用户加入德州本局后，起手牌+公牌配套并保证唯一获胜，测试用）\n\n"
            f"用法：\n/rig 用户ID   开启指定玩家控牌\n/rig off      关闭控牌"
        )
        return
    token = args[0].lower()
    if token in ("off", "关闭", "0"):
        RIGGED_PLAYER = 0
        save_data()
        await update.message.reply_text("✅ 德州控牌已关闭，全员恢复正常随机发牌。")
        return
    target = args[1] if (token in ("on", "开启") and len(args) >= 2) else args[0]
    try:
        pid = int(target)
    except ValueError:
        await update.message.reply_text("⚠️ 用户ID必须是数字，例如 /rig 5431975432")
        return
    if pid <= 0:
        RIGGED_PLAYER = 0
        save_data()
        await update.message.reply_text("✅ 德州控牌已关闭。")
        return
    RIGGED_PLAYER = pid
    save_data()
    await update.message.reply_text(
        f"✅ 已开启德州控牌，目标用户 {pid}：每局起手牌+公牌配套，保证其唯一获胜（测试用）。\n该用户需加入本局才生效；关闭用 /rig off。"
    )


# 命令路由：支持中文命令（Telegram 命令菜单只认拉丁字符，故用 MessageHandler 解析 /中文）
CMD_ALIASES = {
    # 中文命令
    "开始": cmd_start, "菜单": cmd_start, "帮助": cmd_start,
    "德州": cmd_dz, "德州扑克": cmd_dz, "控牌": cmd_rig,
    "赛马": cmd_sm,
    "五子棋": cmd_wz,
    "扫雷": cmd_sl,
    "老虎机": cmd_lhj,
    "21点": cmd_21, "二十一点": cmd_21,
    "百家乐": cmd_bjl,
    "结束": cmd_end,
    "加积分": cmd_add, "加分": cmd_add,
    "加德州": cmd_adddz,
    "减积分": cmd_reduce, "减分": cmd_reduce,
    "盈亏": cmd_cx, "查询": cmd_cx,
    "排行": cmd_ph, "排行榜": cmd_ph, "积分榜": cmd_ph, "积分": cmd_ph,
    "授权": cmd_sq,
    "取消授权": cmd_qxshouquan,
    "加管理员": cmd_addadmin,
    "减管理员": cmd_deladmin,
    "管理员列表": cmd_admin_list, "管理员": cmd_admin_list,
    "adminlist": cmd_admin_list, "admins": cmd_admin_list,
    "自动扫雷": cmd_autosm,
    "备份": cmd_backup,
    "恢复": cmd_restore,
    "骰子": cmd_sb,
    "牛牛": cmd_nn,
    "排位": cmd_season_play, "排位赛": cmd_season_play, "赛季": cmd_season_play, "赛季赛": cmd_season_play,
    "排位报名": cmd_season_join, "报名排位": cmd_season_join, "赛季报名": cmd_season_join,
    "排位榜": cmd_season_rank, "赛季榜": cmd_season_rank, "赛季排名": cmd_season_rank,
    "排位帮助": cmd_season_help, "排位说明": cmd_season_help, "排位赛帮助": cmd_season_help, "赛季帮助": cmd_season_help, "赛季说明": cmd_season_help, "赛季赛帮助": cmd_season_help,
    "排位开赛": cmd_season_start, "排位结束": cmd_season_end, "赛季开赛": cmd_season_start, "赛季结束": cmd_season_end,
    "赌神": cmd_god, "荣誉墙": cmd_god,
    "封赌神": cmd_god_grant, "撤赌神": cmd_god_revoke,
    # 旧英文/数字别名（保留兼容，仍可用）
    "start": cmd_start, "dz": cmd_dz, "sm": cmd_sm, "wz": cmd_wz, "sl": cmd_sl,
    "lhj": cmd_lhj, "21": cmd_21, "bjl": cmd_bjl, "gomoku": cmd_wz, "end": cmd_end, "rig": cmd_rig,
    "END": cmd_end, "add": cmd_add, "adddz": cmd_adddz, "reduce": cmd_reduce,
    "cx": cmd_cx, "ph": cmd_ph, "sq": cmd_sq, "qxshouquan": cmd_qxshouquan,
    "addadmin": cmd_addadmin, "deladmin": cmd_deladmin,
    "autosm": cmd_autosm, "backup": cmd_backup, "restore": cmd_restore,
    "sb": cmd_sb, "nn": cmd_nn,
    "season": cmd_season_play, "seasonplay": cmd_season_play,
    "seasonjoin": cmd_season_join, "seasonrank": cmd_season_rank,
    "seasonstart": cmd_season_start, "seasonend": cmd_season_end,
    "god": cmd_god, "godgrant": cmd_god_grant, "godrevoke": cmd_god_revoke,
}

async def _dispatch_alias(cmd, args, update, context):
    """根据命令别名（无论带不带 /）分发到对应处理函数，并填充 context.args。"""
    handler = CMD_ALIASES.get(cmd)
    if not handler:
        await update.message.reply_text("❓ 未知命令，发送 /开始 查看可用命令")
        return
    context.args = args
    await handler(update, context)


async def route_command(update, context):
    """把 /中文 或 /英文 命令路由到对应处理函数。"""
    if not update.message or not update.message.text:
        return
    _remember_name(update)
    parts = update.message.text.strip().split()
    if not parts or not parts[0].startswith("/"):
        return
    cmd = parts[0][1:]
    if "@" in cmd:
        cmd = cmd.split("@", 1)[0]
    await _dispatch_alias(cmd, parts[1:], update, context)


def main():
    global save_event
    token = os.environ.get("BOT_TOKEN")
    if not token: logger.error("未设置 BOT_TOKEN"); return
    
    # 在主循环启动前初始化 Event
    save_event = asyncio.Event()
    
    builder = Application.builder().token(token).concurrent_updates(True).post_init(post_init).post_shutdown(post_shutdown)
    if hasattr(builder, "max_concurrent_updates"):
        builder = builder.max_concurrent_updates(8)  # 新版 PTB：并发上限 8
    app = builder.build()  # 旧版 PTB：concurrent_updates(True) 默认上限 4

    app.add_handler(MessageHandler(filters.TEXT & filters.Regex(r'^/'), route_command))
    app.add_handler(CallbackQueryHandler(on_button)); app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & ~filters.Regex(r'^/'), on_text))
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)

if __name__ == "__main__": main()
