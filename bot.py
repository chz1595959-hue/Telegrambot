import asyncio
import json
import logging
import os
import random
import re
import shutil
import threading
import time
from collections import defaultdict
from datetime import datetime, timedelta, timezone

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.error import BadRequest, RetryAfter, TelegramError
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, MessageHandler, filters
from treys import Card, Evaluator

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger(__name__)

# ---------- 配置 ----------
STARTING_CHIPS = 20000
# 按用户要求保留该默认管理员 ID 配置，本次不处理该问题。
DEFAULT_ADMIN = 5431975432
ADMIN_USER_ID = int(os.environ.get("ADMIN_USER_ID", DEFAULT_ADMIN))
SMALL_BLIND, BIG_BLIND, ANTE = 200, 400, 100
TURN_TIMEOUT, AUTO_START_TIMEOUT, FIXED_MIN_RAISE = 60, 60, 100
HORSE_COUNT = 4
HORSE_NAMES = ["骏马", "战马", "独角兽", "斑马"]
HORSE_EMOJI = ["🐎", "🐴", "🦄", "🦓"]
FIXED_BET_AMOUNTS = [100, 200, 500, 1000]
RACE_AUTO_START, RACE_UPDATE_INTERVAL = 20, 30
RACE_ANIMATION_INTERVAL, RACE_TRACK_LENGTH = 1.5, 14
DATA_FILE = os.environ.get("DATA_FILE", "bot_data.json")
DATA_BACKUP_FILE, DATA_TEMP_FILE = f"{DATA_FILE}.bak", f"{DATA_FILE}.tmp"
BEIJING_TZ = timezone(timedelta(hours=8))
HAND_NAME_CN = {"High Card":"高牌", "Pair":"一对", "One Pair":"一对", "Two Pair":"两对", "Three of a Kind":"三条", "Straight":"顺子", "Flush":"同花", "Full House":"葫芦", "Four of a Kind":"四条", "Straight Flush":"同花顺", "Royal Flush":"皇家同花顺"}

# ---------- 数据 ----------
group_chips = defaultdict(lambda: defaultdict(lambda: STARTING_CHIPS))
AUTHORIZED_GROUPS = set()
race_history = defaultdict(list)
race_daily_stats = defaultdict(lambda: [0] * HORSE_COUNT)
# profit_by_date[业务日期][群ID][用户ID] = 德州 + 赛马合并盈亏
profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
race_jackpot = defaultdict(int)
hourly_race_enabled = defaultdict(lambda: False)
daily_emergency_used = defaultdict(lambda: defaultdict(bool))
# 已实扣的赛马下注，用于 Railway 重启时退款。
pending_horse_bets = defaultdict(lambda: defaultdict(int))
last_business_date = ""
active_poker_games, active_horse_races = {}, {}
background_tasks = set()
# 保护保存快照与原子替换；即使未来接入线程/执行器也不会出现文件写入交叉。
data_save_lock = threading.RLock()


def now_bj(): return datetime.now(BEIJING_TZ)
def race_id(ts): return datetime.fromtimestamp(ts, timezone.utc).astimezone(BEIJING_TZ).strftime("%Y%m%d-%H%M")
def business_date(now=None):
    now = now or now_bj()
    return (now + timedelta(days=1) if (now.hour, now.minute) >= (23, 50) else now).strftime("%Y-%m-%d")


def restore_nested(target, source):
    for cid, users in source.items():
        for uid, value in users.items(): target[int(cid)][int(uid)] = int(value)


def save_data():
    """在锁内生成快照并原子保存，保留最后一份成功版本。"""
    try:
        with data_save_lock:
            data = {
                "group_chips": {str(cid): dict(users) for cid, users in group_chips.items()},
                "profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in profit_by_date.items()},
                "authorized_groups": list(AUTHORIZED_GROUPS),
                "race_jackpot": {str(cid): value for cid, value in race_jackpot.items()},
                "hourly_race_enabled": {str(cid): value for cid, value in hourly_race_enabled.items()},
                "race_history": {str(cid): value[-10:] for cid, value in race_history.items()},
                "race_daily_stats": {str(cid): value for cid, value in race_daily_stats.items()},
                "daily_emergency_used": {str(cid): {str(uid): used for uid, used in users.items()} for cid, users in daily_emergency_used.items()},
                "last_business_date": last_business_date,
                "pending_horse_bets": {str(cid): dict(users) for cid, users in pending_horse_bets.items()},
            }
            os.makedirs(os.path.dirname(os.path.abspath(DATA_FILE)), exist_ok=True)
            with open(DATA_TEMP_FILE, "w", encoding="utf-8") as file:
                json.dump(data, file, ensure_ascii=False, indent=2)
                file.flush(); os.fsync(file.fileno())
            if os.path.exists(DATA_FILE): shutil.copy2(DATA_FILE, DATA_BACKUP_FILE)
            os.replace(DATA_TEMP_FILE, DATA_FILE)
        return True
    except Exception:
        logger.exception("保存数据失败")
        return False


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
        for date, chats in data.get("profit_by_date", {}).items(): restore_nested(profit_by_date[date], chats)
        AUTHORIZED_GROUPS.update(int(cid) for cid in data.get("authorized_groups", []))
        for cid, value in data.get("race_jackpot", {}).items(): race_jackpot[int(cid)] = int(value)
        for cid, value in data.get("hourly_race_enabled", {}).items(): hourly_race_enabled[int(cid)] = bool(value)
        for cid, value in data.get("race_history", {}).items(): race_history[int(cid)] = list(value)[-10:]
        for cid, value in data.get("race_daily_stats", {}).items(): race_daily_stats[int(cid)] = list(value)[:HORSE_COUNT]
        for cid, users in data.get("daily_emergency_used", {}).items():
            for uid, used in users.items(): daily_emergency_used[int(cid)][int(uid)] = bool(used)
        last_business_date = data.get("last_business_date", "")
        # 德州筹码只保存在局对象里且未实扣持久化余额；只有赛马需要退款。
        for cid, users in data.get("pending_horse_bets", {}).items():
            for uid, amount in users.items(): group_chips[int(cid)][int(uid)] += int(amount)
        pending_horse_bets.clear(); save_data()
    except Exception:
        logger.exception("恢复数据失败")


load_data()

# ---------- Telegram 工具 ----------
async def get_name(app, uid):
    try:
        chat = await app.bot.get_chat(uid)
        name = " ".join(part for part in (chat.first_name, chat.last_name) if part)
        return name or (f"@{chat.username}" if chat.username else f"玩家{uid}")
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
    if group_chips[cid][uid] != 0 or daily_emergency_used[cid][uid]: return False
    group_chips[cid][uid] = 1000
    if poker and uid in poker.chips: poker.chips[uid] += 1000
    daily_emergency_used[cid][uid] = True; save_data()
    await safe_send(app.bot, cid, f"🆘 {await get_name(app, uid)} 筹码归零，已赠送 1000 应急筹码（日限一次）。")
    return True


# ==================== 德州扑克 ====================
def side_pots(total_bets):
    ordered = sorted((uid, value) for uid, value in total_bets.items() if value > 0)
    result, previous = [], 0
    for _, level in ordered:
        if level <= previous: continue
        contributors = [uid for uid, amount in ordered if amount >= level]
        result.append(((level - previous) * len(contributors), contributors)); previous = level
    return result


def distribute_side_pots(total_bets, scores):
    payouts = defaultdict(lambda: {"amount": 0, "details": []})
    for index, (amount, contributors) in enumerate(side_pots(total_bets)):
        eligible = {uid: scores[uid] for uid in contributors if uid in scores}
        if not eligible: continue
        best = min(eligible.values()); winners = sorted(uid for uid, score in eligible.items() if score == best)
        share, remainder = divmod(amount, len(winners))
        for position, uid in enumerate(winners):
            won = share + (1 if position < remainder else 0)
            payouts[uid]["amount"] += won
            payouts[uid]["details"].append(("主池" if index == 0 else f"边池{index}", won))
    return payouts


class PokerGame:
    def __init__(self, cid, owner):
        self.chat_id, self.owner_id, self.phase = cid, owner, "waiting"
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
        self.players.append(uid); self.chips[uid] = group_chips[self.chat_id][uid]; self.total_bet[uid] = 0
        return True

    def start(self):
        if len(self.players) < 2: return False
        self.cancel_auto(); self.cancel_wait(); self.folded.clear(); self.all_in.clear(); self.acted.clear(); self.raise_locked.clear(); self.board = []; self.pot = 0; self.settled = False
        for uid in self.players:
            self.chips[uid] = group_chips[self.chat_id][uid]; self.initial_chips[uid] = self.chips[uid]
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
            if extra < FIXED_MIN_RAISE or paid > self.chips[uid] or new_total <= self.current_bet: return False, "筹码不足或加注无效"
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
        while len(self.board) < 5:
            self.deck.pop()
            if not self.board: self.board.extend([self.deck.pop() for _ in range(3)])
            else: self.board.append(self.deck.pop())
        alive = [uid for uid in self.players if uid not in self.folded]; self.showdown_order = alive.copy()
        if len(alive) == 1:
            winner = alive[0]; self.chips[winner] += self.pot
            for uid in self.players: group_chips[self.chat_id][uid] = self.chips[uid]
            save_data(); return [(winner, "最后赢家", self.pot, [("全部底池", self.pot)], {})]
        scores = {uid: self.evaluator.evaluate(self.hands[uid], self.board) for uid in alive}
        names = {uid: HAND_NAME_CN.get(self.evaluator.class_to_string(self.evaluator.get_rank_class(score)), "未知") for uid, score in scores.items()}
        payouts = distribute_side_pots(self.total_bet, scores)
        for uid, item in payouts.items(): self.chips[uid] += item["amount"]
        for uid in self.players: group_chips[self.chat_id][uid] = self.chips[uid]
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
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await poker_waiting_text(game, app), reply_markup=InlineKeyboardMarkup(rows))


async def poker_table_text(game, app):
    phase = {"preflop":"翻牌前", "flop":"翻牌圈", "turn":"转牌圈", "river":"河牌圈"}.get(game.phase, game.phase)
    lines = [
        f"🃏 积分德州｜{phase}",
        "",
        "━━━━━━━━━━━━━━━━━━━━",
        "",
        f"🂡 公牌：{' '.join(card_str(card) for card in game.board) or '未发牌'}",
        "",
        f"💰 奖池：{game.pot}｜当前下注：{game.current_bet}",
    ]
    current = game.current()
    if current:
        lines.extend(["", f"⏳ 当前行动：{await get_name(app, current)}｜需跟：{max(0, game.current_bet - game.round_bets[current])}"])
    lines.extend(["", "━━━━━━━━━━━━━━━━━━━━", "", "👥 玩家状态", ""])
    for index, uid in enumerate(game.players, 1):
        status = "❌ 弃牌" if uid in game.folded else "🔥 全下" if uid in game.all_in else "🟢 在局"
        lines.extend([f"{index}. {await get_name(app, uid)}", "", f"   {status}｜投入 {game.total_bet[uid]}｜余筹 {game.chips[uid]}", ""])
    return "\n".join(lines).rstrip()


def poker_buttons(game, uid):
    rows = [[InlineKeyboardButton("🂠 查看手牌", callback_data="texas_hand")]]
    if uid != game.current() or uid in game.folded or uid in game.all_in: return InlineKeyboardMarkup(rows)
    to_call = max(0, game.current_bet - game.round_bets[uid])
    rows.append([InlineKeyboardButton("❌ 弃牌", callback_data="texas_fold"), InlineKeyboardButton("✅ 过牌" if not to_call else f"✅ 跟注 {to_call}", callback_data="texas_check" if not to_call else "texas_call")])
    if uid not in game.raise_locked and game.chips[uid] >= to_call + FIXED_MIN_RAISE:
        rows.append([InlineKeyboardButton(f"🔼 加注 {FIXED_MIN_RAISE}", callback_data=f"texas_raise_{FIXED_MIN_RAISE}")])
    if game.chips[uid] > 0: rows.append([InlineKeyboardButton(f"🔥 全下 {game.chips[uid]}", callback_data="texas_allin")])
    return InlineKeyboardMarkup(rows)


async def update_poker_table(game, app):
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await poker_table_text(game, app))


async def start_turn_timer(game, app):
    game.cancel_timer()
    uid = game.current()
    if uid is None:
        if game.phase == "showdown": await settle_poker(game, app)
        return
    await safe_delete(app.bot, game.chat_id, game.action_msg_id)
    msg = await safe_send(app.bot, game.chat_id, f"{await poker_table_text(game, app)}\n\n⏰ {await get_name(app, uid)} 请在 {TURN_TIMEOUT} 秒内行动。", reply_markup=poker_buttons(game, uid))
    game.action_msg_id = msg.message_id if msg else None
    async def timeout():
        await asyncio.sleep(TURN_TIMEOUT)
        if game.phase in {"preflop", "flop", "turn", "river"} and game.current() == uid:
            ok, _ = game.action(uid, "fold")
            if not ok: return
            await safe_send(app.bot, game.chat_id, f"⏰ {await get_name(app, uid)} 超时自动弃牌。")
            if game.phase == "showdown": await settle_poker(game, app)
            else:
                await update_poker_table(game, app)
                await start_turn_timer(game, app)
    game.turn_task = asyncio.create_task(timeout())


async def start_wait_timeout(game, app):
    """首名玩家开房后，若 60 秒内仍无人加入则自动关闭等待房。"""
    game.cancel_wait()
    async def expire_waiting_room():
        await asyncio.sleep(AUTO_START_TIMEOUT)
        if game.phase == "waiting" and len(game.players) < 2 and active_poker_games.get(game.chat_id) is game:
            active_poker_games.pop(game.chat_id, None)
            await safe_edit(app.bot, game.chat_id, game.game_msg_id, "⌛ 德州等待 60 秒无人加入，本局已自动解散。", reply_markup=None)
    game.wait_task = asyncio.create_task(expire_waiting_room())


async def start_auto_game(game, app):
    game.cancel_auto()
    async def auto_start():
        await asyncio.sleep(AUTO_START_TIMEOUT)
        if game.phase == "waiting" and len(game.players) >= 2 and game.start():
            await update_poker_table(game, app)
            await start_turn_timer(game, app)
    game.auto_task = asyncio.create_task(auto_start())


async def settle_poker(game, app):
    if game.settled: return
    game.settled = True; game.cancel_timer(); game.cancel_auto(); game.cancel_wait()
    try:
        result = game.showdown()
        if not result: raise RuntimeError("德州摊牌未生成结算结果")
        date, hand_types = business_date(), result[0][4]
        name_ids = set(game.players) | set(game.showdown_order)
        names = {uid: await get_name(app, uid) for uid in name_ids}
        lines = ["🃏 德州结算", "━━━━━━━━━━━━━━━━━━━━", f"🂡 公牌：{' '.join(card_str(card) for card in game.board)}", "", "亮牌："]
        for uid in game.showdown_order:
            suffix = "（弃牌）" if uid in game.folded else ""
            lines.extend([f"{names[uid]}：{' '.join(card_str(card) for card in game.hands[uid])}｜{hand_types.get(uid, '')}{suffix}", ""])
        lines.append("派奖：")
        for uid, hand, amount, details, _ in sorted(result, key=lambda item: item[2], reverse=True):
            lines.extend([f"{names[uid]}：{hand}｜+{amount}（{'，'.join(f'{pool}+{value}' for pool, value in details)}）", ""])
        lines.append("投入 / 盈亏：")
        for uid in game.players:
            net = game.chips[uid] - game.initial_chips[uid]
            profit_by_date[date][game.chat_id][uid] += net
            lines.extend([f"{names[uid]}：投入 {game.total_bet[uid]}｜盈亏 {net:+d}", ""])
        rank = sorted(profit_by_date[date][game.chat_id].items(), key=lambda item: item[1], reverse=True)[:10]
        lines.extend(["🏆 当日德州累计盈利榜", *[f"{index}. {names.get(uid) or await get_name(app, uid)}：{amount:+d}" for index, (uid, amount) in enumerate(rank, 1)]])
        delivered = await safe_send_long(app.bot, game.chat_id, "\n".join(lines))
        if delivered is None:
            await safe_send(app.bot, game.chat_id, "⚠️ 德州已完成结算，但详细结算消息发送失败。筹码与当日盈亏已保存，可使用 /cx 查看排行榜。")
    except Exception:
        logger.exception("德州结算异常，群 %s", game.chat_id)
        await safe_send(app.bot, game.chat_id, "⚠️ 德州结算消息生成异常，请管理员检查日志；系统已保留结算状态并保存当前筹码。")
    finally:
        if active_poker_games.get(game.chat_id) is game: active_poker_games.pop(game.chat_id, None)
        for uid in game.players:
            await emergency_if_needed(game.chat_id, uid, app, game)
        save_data()


# ==================== 赛马 ====================
class HorseRace:
    def __init__(self, cid, owner, jackpot):
        self.chat_id, self.owner_id, self.jackpot = cid, owner, jackpot
        self.bets, self.total_bets, self.pool = defaultdict(dict), [0] * HORSE_COUNT, 0
        self.phase, self.create_time, self.positions, self.arrivals = "betting", time.time(), [0] * HORSE_COUNT, []
        self.notified, self.name_cache = set(), {}
        self.game_msg_id = self.animation_msg_id = None
        self.task, self.settled, self.cancelled, self.lock = None, False, False, asyncio.Lock()
        rates = [random.uniform(.18, .35) for _ in range(HORSE_COUNT)]; total = sum(rates)
        self.rates = [value / total for value in rates]

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
        if not 0 <= horse < HORSE_COUNT or amount <= 0 or amount > group_chips[self.chat_id][uid]: return False, "马号、金额或筹码无效"
        group_chips[self.chat_id][uid] -= amount; self.pool += amount; self.total_bets[horse] += amount
        self.bets[uid][horse] = self.bets[uid].get(horse, 0) + amount; pending_horse_bets[self.chat_id][uid] += amount
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
            "━" * 20,
            *[f"🏁{'━' * 13}{HORSE_EMOJI[i]}" for i in range(HORSE_COUNT)],
            "━" * 20,
            "📊 路书",
            f"最近10场: {history}",
            "📜 当日胜率:",
            "  " + " | ".join(f"{HORSE_EMOJI[i]} {stats[i]}胜" for i in range(HORSE_COUNT)),
            "  " + " | ".join(f"{HORSE_EMOJI[i]} {stats[i] / total_wins * 100:.0f}%" if total_wins else f"{HORSE_EMOJI[i]} 0%" for i in range(HORSE_COUNT)),
            "📊 投注情况:",
        ]
        for i, odd in enumerate(odds):
            lines.append(f"{HORSE_EMOJI[i]} {HORSE_NAMES[i]}: 胜率{self.rates[i] * 100:.0f}% | {self.total_bets[i]}积分 | 赔率 {odd:.2f}x")
        lines.append("━" * 20)
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
        lines = ["🏇 赛马进行中", "━" * 20]
        for i, pos in enumerate(self.positions):
            pos = min(pos, RACE_TRACK_LENGTH)
            track = "🏁" + (HORSE_EMOJI[i] + "━" * RACE_TRACK_LENGTH if pos >= RACE_TRACK_LENGTH else "━" * (RACE_TRACK_LENGTH - pos - 1) + HORSE_EMOJI[i] + "━" * pos)
            lines.append(track)
        if self.arrivals: lines.append("✅ 到达：" + " ".join(HORSE_EMOJI[i] for i in self.arrivals))
        return "\n".join(lines)

    async def run(self, app):
        try:
            thresholds = [value for value in (300, 180, 60, 30, 10) if value < RACE_AUTO_START]
            while self.phase == "betting" and not self.cancelled:
                remain = max(0, int(RACE_AUTO_START - (time.time() - self.create_time)))
                for threshold in thresholds:
                    if remain <= threshold and threshold not in self.notified:
                        self.notified.add(threshold); await safe_send(app.bot, self.chat_id, f"⏰ 赛马还剩 {threshold // 60} 分钟 {threshold % 60} 秒！")
                if not remain: break
                await safe_edit(app.bot, self.chat_id, self.game_msg_id, await self.view(app), reply_markup=self.buttons())
                await asyncio.sleep(min(RACE_UPDATE_INTERVAL, max(1, remain)))
            if self.cancelled: return
            self.phase = "racing"
            await safe_edit(app.bot, self.chat_id, self.game_msg_id, "🏇 比赛开始！", reply_markup=None)
            msg = await safe_send(app.bot, self.chat_id, "🏇 比赛开始！正在奔跑中……"); self.animation_msg_id = msg.message_id if msg else None
            while not self.cancelled and len(self.arrivals) < HORSE_COUNT:
                for i in range(HORSE_COUNT):
                    if self.positions[i] < RACE_TRACK_LENGTH:
                        self.positions[i] = min(RACE_TRACK_LENGTH, self.positions[i] + random.randint(1, 3))
                        if self.positions[i] >= RACE_TRACK_LENGTH and i not in self.arrivals: self.arrivals.append(i)
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
                winner, odd, date = self.arrivals[0], self.odds()[self.arrivals[0]], business_date()
                race_daily_stats[self.chat_id][winner] += 1
                race_history[self.chat_id] = (race_history[self.chat_id] + [winner])[-10:]
                lines = [f"🏆 赛马结果：{HORSE_EMOJI[winner]} {HORSE_NAMES[winner]}", "━━━━━━━━━━━━━━━━━━━━"]
                total_payout = 0
                for uid, bets in self.bets.items():
                    stake, payout = sum(bets.values()), int(bets.get(winner, 0) * odd)
                    group_chips[self.chat_id][uid] += payout; total_payout += payout
                    profit_by_date[date][self.chat_id][uid] += payout - stake
                    name = self.name_cache.get(uid) or await get_name(app, uid)
                    self.name_cache[uid] = name
                    lines.extend([f"{name}：投注 {stake}｜派彩 {payout}｜盈亏 {payout-stake:+d}", ""])
                race_jackpot[self.chat_id] = self.jackpot + self.pool if not total_payout else max(0, self.jackpot + self.pool - total_payout)
                payouts_applied = True
                if not total_payout: lines.append("🔄 无人押中，奖池滚入下一期。")
                rank = sorted(profit_by_date[date][self.chat_id].items(), key=lambda item: item[1], reverse=True)[:10]
                lines.extend(["", "🏆 当日赛马累计盈利榜"])
                for index, (uid, amount) in enumerate(rank, 1):
                    name = self.name_cache.get(uid) or await get_name(app, uid)
                    self.name_cache[uid] = name
                    lines.append(f"{index}. {name}：{amount:+d}")
                pending_horse_bets.pop(self.chat_id, None); self.phase = "finished"; save_data()
                delivered = await safe_send_long(app.bot, self.chat_id, "\n".join(lines))
                if delivered is None:
                    await safe_send(app.bot, self.chat_id, "⚠️ 赛马已完成结算，但详细结果消息发送失败。筹码与当日盈亏已保存，可使用 /cx 查看排行榜。")
            except Exception:
                logger.exception("赛马结算异常，群 %s", self.chat_id)
                await safe_send(app.bot, self.chat_id, "⚠️ 赛马结算异常，请管理员检查日志；本局将退款以保护玩家筹码。")
                for uid, bets in self.bets.items():
                    group_chips[self.chat_id][uid] += sum(bets.values())
                pending_horse_bets.pop(self.chat_id, None); race_jackpot[self.chat_id] = self.jackpot; save_data()
            finally:
                await safe_delete(app.bot, self.chat_id, self.animation_msg_id)
                if active_horse_races.get(self.chat_id) is self: active_horse_races.pop(self.chat_id, None)
                for uid in self.bets: await emergency_if_needed(self.chat_id, uid, app)

    async def refund(self, app, notice):
        async with self.lock:
            if self.cancelled: return
            self.cancelled, self.phase = True, "cancelled"
            for uid, bets in self.bets.items(): group_chips[self.chat_id][uid] += sum(bets.values())
            pending_horse_bets.pop(self.chat_id, None); race_jackpot[self.chat_id] += self.jackpot; save_data()
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

async def cmd_start(update, context): await update.message.reply_text("使用 /dz 发起德州扑克，/sm 发起赛马。")

async def cmd_dz(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id; game = active_poker_games.get(cid)
    if game:
        if game.phase != "waiting": await update.message.reply_text("当前已有进行中的德州扑克。"); return
        if game.add(uid):
            await update_poker_waiting(game, context.application); await update.message.reply_text("已加入当前等待房间。")
            if len(game.players) >= 2:
                game.cancel_wait()
                await start_auto_game(game, context.application)
        else: await update.message.reply_text("你已在等待房间中。")
        return
    game = PokerGame(cid, uid); game.add(uid); active_poker_games[cid] = game
    msg = await safe_send(context.bot, cid, await poker_waiting_text(game, context.application), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("加入游戏", callback_data="texas_join")]]))
    if msg:
        game.game_msg_id = msg.message_id
        await start_wait_timeout(game, context.application)

async def cmd_sm(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id
    if cid in active_horse_races: await update.message.reply_text("当前已有赛马进行中。"); return
    race = HorseRace(cid, update.effective_user.id, race_jackpot.pop(cid, 0)); active_horse_races[cid] = race
    msg = await safe_send(context.bot, cid, await race.view(context.application), reply_markup=race.buttons())
    if msg: race.game_msg_id = msg.message_id
    race.task = asyncio.create_task(race.run(context.application)); save_data()

async def refund_poker(game, app, notice):
    """终止未结算牌局时，按开局筹码退还全部 ante、盲注和后续下注。"""
    game.cancel_timer(); game.cancel_auto(); game.cancel_wait()
    for player_id in game.players:
        # 德州下注只在局对象中暂扣；显式恢复开局余额，避免后续改动破坏退款语义。
        group_chips[game.chat_id][player_id] = game.initial_chips.get(player_id, group_chips[game.chat_id][player_id])
    game.phase = "cancelled"
    if active_poker_games.get(game.chat_id) is game:
        active_poker_games.pop(game.chat_id, None)
    await safe_delete(app.bot, game.chat_id, game.action_msg_id)
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, notice, reply_markup=None)
    save_data()


async def cmd_end(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id; poker, race = active_poker_games.get(cid), active_horse_races.get(cid)
    owner = poker.owner_id if poker else (race.owner_id if race else None)
    if owner is None: await update.message.reply_text("当前没有进行中的游戏。"); return
    # 按需求，群管理员不自动越权；仅 bot 管理员或发起人。
    if uid != ADMIN_USER_ID and uid != owner: await update.message.reply_text("❌ 仅 Bot 管理员或本局发起人可终止。"); return
    notices = []
    if poker:
        await refund_poker(poker, context.application, "🛑 德州扑克已终止，已退还本局全部底注、盲注和下注。")
        notices.append("德州已退款")
    if race:
        if race.phase == "betting":
            if race.task and not race.task.done(): race.task.cancel(); await asyncio.gather(race.task, return_exceptions=True)
            await race.refund(context.application, "🛑 赛马已终止，所有下注已退款。"); notices.append("赛马已退款")
        else: notices.append("赛马已进入赛跑/结算阶段，为避免半结算，系统将继续完成结算")
    save_data(); await update.message.reply_text("；".join(notices))

def player_is_busy(cid, uid):
    poker = active_poker_games.get(cid)
    if poker and poker.phase != "waiting" and uid in poker.players:
        return True
    race = active_horse_races.get(cid)
    return bool(race and race.phase in {"betting", "racing", "settling"} and uid in race.bets)


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
    lines = ["📊 当日综合盈亏榜", "━"*20]
    for i, (uid, value) in enumerate(sorted(data.items(), key=lambda x:x[1], reverse=True)[:10], 1): lines.append(f"{i}. {await get_name(context.application, uid)}：{value:+d}")
    await safe_send_long(context.bot, cid, "\n".join(lines))

async def cmd_ph(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id; lines = ["💰 当前筹码榜", "━"*20]
    for i, (uid, value) in enumerate(sorted(group_chips[cid].items(), key=lambda x:x[1], reverse=True)[:20], 1): lines.append(f"{i}. {await get_name(context.application, uid)}：{value}")
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
    q = update.callback_query
    if not q or not q.message:
        if q: await q.answer("该操作已过期", show_alert=True)
        return
    cid, uid, data = q.message.chat.id, q.from_user.id, q.data or ""
    if not is_auth(cid): await q.answer("未授权", show_alert=True); return
    if data.startswith("texas_"):
        game = active_poker_games.get(cid)
        if not game: await q.answer("德州游戏已结束", show_alert=True); return
        if data == "texas_hand":
            hand = game.hands.get(uid); await q.answer(f"你的手牌：{card_str(hand[0])} {card_str(hand[1])}" if hand and uid not in game.folded else "当前无法查看手牌", show_alert=True); return
        if game.phase == "waiting":
            if data == "texas_join" and game.add(uid):
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

async def on_text(update, context):
    message, user = update.effective_message, update.effective_user
    if not message or not message.text or not user or user.is_bot: return
    cid, text = update.effective_chat.id, message.text.strip()
    match = re.fullmatch(r"下注\s+(\d+)\s+(\d+)", text); race = active_horse_races.get(cid)
    if match and race:
        horse, amount = int(match.group(1))-1, int(match.group(2)); ok, desc = race.bet(user.id, horse, amount)
        if not ok: await message.reply_text(f"❌ {desc}"); return
        race.name_cache[user.id] = await get_name(context.application, user.id); await action_notice(cid, context.application, user.id, f"下注 {amount} 于 {HORSE_EMOJI[horse]}")
        await safe_edit(context.bot, cid, race.game_msg_id, await race.view(context.application), reply_markup=race.buttons()); return
    match = re.fullmatch(r"加注\s*(\d+)", text); game = active_poker_games.get(cid)
    if match and game and user.id == game.current():
        ok, desc = game.action(user.id, "raise", int(match.group(1)))
        if not ok: await message.reply_text(f"❌ {desc}"); return
        await action_notice(cid, context.application, user.id, desc)
        if game.phase == "showdown": await settle_poker(game, context.application)
        else: await update_poker_table(game, context.application); await start_turn_timer(game, context.application)


# ---------- 定时任务与启动 ----------
async def daily_reset_scheduler():
    global last_business_date
    today = now_bj().strftime("%Y-%m-%d")
    # 第一次启动只记录业务日，避免因部署重启立刻重置玩家筹码。
    if not last_business_date:
        last_business_date = today; save_data()
    while True:
        now = now_bj(); target = (now + timedelta(days=1)).replace(hour=0, minute=0, second=1, microsecond=0)
        await asyncio.sleep((target-now).total_seconds())
        today = now_bj().strftime("%Y-%m-%d")
        # 不重置正在进行德州或赛马中的玩家，避免跨日覆盖未结算状态。
        protected = set()
        for poker in active_poker_games.values():
            if poker.phase != "waiting":
                protected.update((poker.chat_id, uid) for uid in poker.players)
        for race in active_horse_races.values():
            if race.phase in {"betting", "racing", "settling"}:
                protected.update((race.chat_id, uid) for uid in race.bets)
        for chat_id, users in group_chips.items():
            for uid in users:
                if (chat_id, uid) not in protected:
                    users[uid] = STARTING_CHIPS
        for cid in race_daily_stats: race_daily_stats[cid] = [0] * HORSE_COUNT
        daily_emergency_used.clear(); last_business_date = today; save_data()

async def leaderboard_scheduler(app):
    while True:
        now = now_bj(); target = now.replace(hour=23, minute=50, second=0, microsecond=0)
        if target <= now: target += timedelta(days=1)
        await asyncio.sleep((target-now).total_seconds())
        date = now_bj().strftime("%Y-%m-%d"); snapshot = profit_by_date.pop(date, {})
        for cid, data in snapshot.items():
            if not data: continue
            lines = [f"🏆 今日综合排行榜（{date}）", "━"*20]
            for i, (uid, amount) in enumerate(sorted(data.items(), key=lambda x:x[1], reverse=True)[:10], 1): lines.append(f"{i}. {await get_name(app, uid)}：{amount:+d}")
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
                race = HorseRace(cid, ADMIN_USER_ID, race_jackpot.pop(cid, 0)); active_horse_races[cid] = race
                msg = await safe_send(app.bot, cid, await race.view(app), reply_markup=race.buttons())
                if msg: race.game_msg_id = msg.message_id
                race.task = asyncio.create_task(race.run(app)); save_data()
        next_minute = (now + timedelta(minutes=1)).replace(second=0, microsecond=0)
        await asyncio.sleep(max(1, (next_minute-now).total_seconds()))

async def post_init(app):
    background_tasks.update({asyncio.create_task(daily_reset_scheduler()), asyncio.create_task(leaderboard_scheduler(app)), asyncio.create_task(hourly_race_scheduler(app))})

async def post_shutdown(app):
    save_data()

def main():
    token = os.environ.get("BOT_TOKEN")
    if not token: logger.error("未设置 BOT_TOKEN"); return
    app = Application.builder().token(token).post_init(post_init).post_shutdown(post_shutdown).build()
    for command, handler in [("start",cmd_start),("dz",cmd_dz),("sm",cmd_sm),("end",cmd_end),("add",cmd_add),("reduce",cmd_reduce),("cx",cmd_cx),("ph",cmd_ph),("sq",cmd_sq),("qxshouquan",cmd_qxshouquan),("autosm",cmd_autosm)]: app.add_handler(CommandHandler(command, handler))
    app.add_handler(CallbackQueryHandler(on_button)); app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)

if __name__ == "__main__": main()
