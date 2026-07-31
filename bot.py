import random, os, asyncio, logging, traceback, re
from collections import defaultdict
from datetime import datetime, timedelta
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, MessageHandler, filters, ContextTypes
from treys import Card, Evaluator

# ---------- 日志 ----------
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger(__name__)

# ---------- 通用配置 ----------
STARTING_CHIPS = 10000
DEFAULT_ADMIN = 5431975432
ADMIN_USER_ID = int(os.environ.get("ADMIN_USER_ID", DEFAULT_ADMIN))

# ---------- 每日重置筹码配置 ----------
DAILY_RESET_TIME = (0, 0)   # (hour, minute) 服务器本地时间 0 点
RESET_TO_CHIPS = 20000

# ---------- 德州配置 ----------
SMALL_BLIND = 100
BIG_BLIND = 200
TURN_TIMEOUT = 60
FIXED_MIN_RAISE = 100
AUTO_START_TIMEOUT = 60

# ---------- 炸金花配置 ----------
ZJH_ANTE = 100
ZJH_MIN_RAISE = 100
ZJH_SEEN_MULTIPLIER = 2

# ---------- 21点配置 ----------
BJ_MIN_BET = 100

# ---------- 梭哈配置 ----------
SHOW_HAND_ANTE = 100

# ---------- 牛牛配置 ----------
NIU_BET = 100

# ---------- 牌型中英文映射（德州、梭哈） ----------
HAND_NAME_CN = {
    "High Card": "高牌", "Pair": "一对", "One Pair": "一对", "Two Pair": "两对",
    "Three of a Kind": "三条", "Straight": "顺子", "Flush": "同花", "Full House": "葫芦",
    "Four of a Kind": "四条", "Straight Flush": "同花顺", "Royal Flush": "皇家同花顺",
}

# ---------- 内存存储 ----------
group_chips = defaultdict(lambda: defaultdict(lambda: STARTING_CHIPS))
AUTHORIZED_GROUPS = set()

# ---------- 卡牌美化（花色在前） ----------
def card_str(card_int):
    raw = Card.int_to_pretty_str(card_int)
    inner = raw.strip('[]')
    suit_map = {'♠': '♠️', '♥': '♥️', '♦': '♦️', '♣': '♣️'}
    rank = inner[:-1].replace('T', '10')
    suit = inner[-1]
    return f"{suit_map.get(suit, suit)}{rank}"

async def get_name(app, user_id):
    try:
        chat = await app.bot.get_chat(user_id)
        return chat.first_name or str(user_id)
    except:
        return str(user_id)

# ---------- 边池计算（德州） ----------
def compute_side_pots(all_bets):
    if not all_bets: return []
    sorted_bets = sorted(all_bets.items(), key=lambda x: x[1])
    layers = []
    prev = 0
    for uid, bet in sorted_bets:
        if bet > prev:
            contrib = bet - prev
            eligible = [u for u, b in sorted_bets if b >= bet]
            layers.append({'amount': contrib * len(eligible), 'eligible': eligible})
            prev = bet
    return layers

def distribute_side_pots(layers, alive_scores):
    dist = {uid: 0 for uid in alive_scores}
    for layer in layers:
        eligible_scores = {uid: alive_scores[uid] for uid in layer['eligible'] if uid in alive_scores}
        if not eligible_scores: continue
        best = min(eligible_scores.values())
        winners = [uid for uid, s in eligible_scores.items() if s == best]
        share = layer['amount'] // len(winners)
        rem = layer['amount'] % len(winners)
        for uid in winners:
            dist[uid] += share
        if rem:
            dist[winners[0]] += rem
    return dist

# ---------- 临时提示 ----------
async def action_notify(chat_id, app, user_id, desc):
    name = await get_name(app, user_id)
    msg = await app.bot.send_message(chat_id, f"🎲 {name} {desc}")
    asyncio.create_task(auto_delete(msg, 10))

async def auto_delete(message, delay):
    await asyncio.sleep(delay)
    try:
        await message.delete()
    except:
        pass

# ==================== 每日重置筹码任务 ====================
async def daily_reset_chips():
    while True:
        now = datetime.now()
        target = now.replace(hour=DAILY_RESET_TIME[0], minute=DAILY_RESET_TIME[1], second=0, microsecond=0)
        if target <= now:
            target += timedelta(days=1)
        wait_seconds = (target - now).total_seconds()
        await asyncio.sleep(wait_seconds)
        # 重置所有群组的所有玩家筹码
        for chat_id in group_chips:
            for uid in group_chips[chat_id]:
                group_chips[chat_id][uid] = RESET_TO_CHIPS
        logger.info("每日筹码重置完成，所有玩家筹码恢复至 20000")
        
# ==================== 德州扑克（完整优化版） ====================
class PokerGame:
    def __init__(self, chat_id, owner_id):
        self.chat_id = chat_id
        self.owner_id = owner_id
        self.players = []
        self.chips = {}
        self.initial_chips = {}
        self.total_bet = {}
        self.hands = {}
        self.folded = set()
        self.all_in = set()
        self.deck = []
        self.board = []
        self.pot = 0
        self.phase = 'waiting'
        self.active_players = []
        self.actor_idx = 0
        self.current_bet = 0
        self.round_bets = {}
        self.min_raise = FIXED_MIN_RAISE
        self.acted_this_round = set()
        self.last_aggressor = None
        self.dealer_idx = 0
        self.game_msg_id = None
        self.action_msg_id = None
        self.evaluator = Evaluator()
        self.turn_task = None
        self.auto_start_task = None
        self.showdown_order = []

    def add_player(self, uid):
        if uid not in self.players and self.phase == 'waiting':
            if uid not in group_chips[self.chat_id]:
                group_chips[self.chat_id][uid] = STARTING_CHIPS
            self.chips[uid] = group_chips[self.chat_id][uid]
            self.total_bet[uid] = 0
            self.players.append(uid)
            return True
        return False

    def start_game(self):
        if len(self.players) < 2:
            return False
        for uid in self.players:
            self.chips[uid] = group_chips[self.chat_id].get(uid, STARTING_CHIPS)
            self.total_bet[uid] = 0
        self.initial_chips = self.chips.copy()
        self.phase = 'preflop'
        self.deck = [Card.new(r + s) for r in "23456789TJQKA" for s in "shdc"]
        random.shuffle(self.deck)
        for uid in self.players:
            self.hands[uid] = [self.deck.pop(), self.deck.pop()]
            self.round_bets[uid] = 0
        self.dealer_idx = len(self.players) - 1
        sb_idx = (self.dealer_idx + 1) % len(self.players)
        bb_idx = (self.dealer_idx + 2) % len(self.players)
        self._post_blind(self.players[sb_idx], SMALL_BLIND)
        self._post_blind(self.players[bb_idx], BIG_BLIND)
        self.current_bet = BIG_BLIND
        self.active_players = self.players.copy()
        self.actor_idx = (bb_idx + 1) % len(self.players)
        self.acted_this_round.clear()
        self.last_aggressor = None
        self.showdown_order.clear()
        self.cancel_auto_start()
        return True

    def _post_blind(self, uid, amount):
        actual = min(amount, self.chips[uid])
        self.chips[uid] -= actual
        self.round_bets[uid] += actual
        self.pot += actual
        self.total_bet[uid] += actual
        if self.chips[uid] == 0:
            self.all_in.add(uid)

    def current_player(self):
        if not self.active_players or self.actor_idx >= len(self.active_players):
            return None
        for _ in range(len(self.active_players)):
            uid = self.active_players[self.actor_idx]
            if uid not in self.folded and uid not in self.all_in:
                return uid
            self.actor_idx = (self.actor_idx + 1) % len(self.active_players)
        return None

    def next_player(self):
        start = self.actor_idx
        while True:
            self.actor_idx = (self.actor_idx + 1) % len(self.active_players)
            if self.actor_idx == start:
                return None
            uid = self.active_players[self.actor_idx]
            if uid not in self.folded and uid not in self.all_in and uid not in self.acted_this_round:
                return uid
        return None

    def all_acted_or_allin(self):
        for uid in self.active_players:
            if uid not in self.folded and uid not in self.all_in and uid not in self.acted_this_round:
                return False
        return True

    def handle_action(self, uid, action, amount=None):
        if uid != self.current_player():
            return False, "还没轮到你"
        if uid in self.acted_this_round:
            return False, "本轮已行动"
        if uid in self.all_in:
            return False, "已全下，无法行动"

        if action == 'fold':
            self.folded.add(uid)
            self.active_players.remove(uid)
            if self.actor_idx >= len(self.active_players):
                self.actor_idx = 0
            desc = "弃牌"
        elif action == 'check':
            if self.current_bet > self.round_bets[uid]:
                return False, "必须跟注或加注"
            self.acted_this_round.add(uid)
            desc = "过牌"
        elif action == 'call':
            call_amt = self.current_bet - self.round_bets[uid]
            actual = min(call_amt, self.chips[uid])
            self.chips[uid] -= actual
            self.round_bets[uid] += actual
            self.pot += actual
            self.total_bet[uid] += actual
            if self.chips[uid] == 0:
                self.all_in.add(uid)
            self.acted_this_round.add(uid)
            desc = f"跟注 {actual}"
        elif action == 'allin':
            total = self.chips[uid]
            self.chips[uid] = 0
            self.round_bets[uid] += total
            self.pot += total
            self.total_bet[uid] += total
            if total > self.current_bet:
                self.current_bet = self.round_bets[uid]
            self.all_in.add(uid)
            self.acted_this_round.add(uid)
            desc = f"全下 {total}"
        elif action == 'raise':
            call_amt = self.current_bet - self.round_bets[uid]
            total_raise = call_amt + amount
            if total_raise <= 0 or total_raise > self.chips[uid]:
                return False, "筹码不足或无效加注额"
            new_total = self.round_bets[uid] + total_raise
            if new_total <= self.current_bet:
                return False, f"加注后总额必须大于当前下注 {self.current_bet}"
            if new_total - self.current_bet < FIXED_MIN_RAISE:
                return False, f"最小加注为 {FIXED_MIN_RAISE}，请至少加注 {call_amt + FIXED_MIN_RAISE}"
            self.chips[uid] -= total_raise
            self.round_bets[uid] += total_raise
            self.pot += total_raise
            self.total_bet[uid] += total_raise
            self.current_bet = new_total
            self.acted_this_round = {uid}
            self.last_aggressor = uid
            desc = f"加注 {total_raise}"
        else:
            return False, "未知操作"

        alive = [p for p in self.active_players if p not in self.folded]
        if len(alive) == 1 or all(p in self.all_in for p in alive):
            self.phase = 'showdown'
            return True, desc

        if self.all_acted_or_allin():
            self._end_round()
            return True, desc

        self.next_player()
        if self.current_player() is None or self.all_acted_or_allin():
            self._end_round()
        return True, desc

    def _end_round(self):
        for uid in self.round_bets:
            self.round_bets[uid] = 0
        self.current_bet = 0
        self.acted_this_round.clear()

        if self.phase == 'preflop':
            self.phase = 'flop'
            self.board.extend([self.deck.pop() for _ in range(3)])
        elif self.phase == 'flop':
            self.phase = 'turn'
            self.board.append(self.deck.pop())
        elif self.phase == 'turn':
            self.phase = 'river'
            self.board.append(self.deck.pop())
        elif self.phase == 'river':
            self.phase = 'showdown'
            return

        start_idx = (self.dealer_idx + 1) % len(self.players)
        for i in range(len(self.players)):
            uid = self.players[(start_idx + i) % len(self.players)]
            if uid in self.active_players and uid not in self.folded:
                self.actor_idx = self.active_players.index(uid)
                break

    def showdown(self):
        while len(self.board) < 5:
            if len(self.board) == 0:
                self.board.extend([self.deck.pop() for _ in range(3)])
            elif len(self.board) == 3:
                self.board.append(self.deck.pop())
            elif len(self.board) == 4:
                self.board.append(self.deck.pop())
            else:
                break

        alive = [p for p in self.active_players if p not in self.folded]

        if self.last_aggressor and self.last_aggressor in alive:
            start = self.last_aggressor
        else:
            start = None
            for i in range(1, len(self.players)):
                uid = self.players[(self.dealer_idx + i) % len(self.players)]
                if uid in alive:
                    start = uid
                    break
            if start is None:
                start = alive[0]
        idx = alive.index(start)
        self.showdown_order = alive[idx:] + alive[:idx]

        if len(alive) == 1:
            winner = alive[0]
            pot_amount = self.pot
            self.chips[winner] += pot_amount
            self.pot = 0
            self._save_chips()
            return [(winner, "最后赢家", pot_amount, {})]

        scores = {}
        hand_types = {}
        for uid in alive:
            hand = self.hands[uid]
            if self.board:
                score = self.evaluator.evaluate(hand, self.board)
            else:
                score = self.evaluator.evaluate(hand, [])
            scores[uid] = score
            rank_class = self.evaluator.get_rank_class(score)
            hand_en = self.evaluator.class_to_string(rank_class)
            hand_types[uid] = HAND_NAME_CN.get(hand_en, hand_en)

        best = min(scores.values())
        overall_winners = {uid for uid in alive if scores[uid] == best}

        all_bets = {uid: self.total_bet[uid] for uid in self.players}
        layers = compute_side_pots(all_bets)
        dist = distribute_side_pots(layers, scores)

        for uid in alive:
            self.chips[uid] += dist[uid]
            self.pot -= dist[uid]
        if self.pot > 0:
            first = next(iter(overall_winners))
            self.chips[first] += self.pot
            dist[first] += self.pot
            self.pot = 0

        self._save_chips()
        desc_en = self.evaluator.class_to_string(self.evaluator.get_rank_class(best))
        desc_cn = HAND_NAME_CN.get(desc_en, desc_en)
        return [(uid, desc_cn, dist[uid], hand_types) for uid in overall_winners]

    def _save_chips(self):
        for uid in self.chips:
            group_chips[self.chat_id][uid] = self.chips[uid]

    def cancel_timer(self):
        if self.turn_task:
            self.turn_task.cancel()
            self.turn_task = None

    def cancel_auto_start(self):
        if self.auto_start_task:
            self.auto_start_task.cancel()
            self.auto_start_task = None

# ---------- 德州界面构建 ----------
async def build_action_view(game, app, uid):
    board_str = " ".join(card_str(c) for c in game.board) if game.board else "无"
    lines = []
    for idx, pid in enumerate(game.players, 1):
        name = await get_name(app, pid)
        if pid in game.folded:
            s = "弃牌"
        elif pid in game.all_in:
            s = "全下"
        else:
            s = "在局"
        lines.append(f"{idx}. {name} {s} 投入:{game.total_bet.get(pid, 0)}")
    to_call = game.current_bet - game.round_bets.get(uid, 0)
    if to_call < 0: to_call = 0
    return (
        f"公牌: {board_str}\n"
        f"奖池: {game.pot}  当前下注: {game.current_bet}\n"
        f"你需跟注: {to_call}\n\n玩家:\n" + "\n".join(lines) +
        f"\n\n轮到 {await get_name(app, uid)} 行动"
    )

async def build_table_view(game, app):
    lines = []
    for idx, pid in enumerate(game.players, 1):
        name = await get_name(app, pid)
        if pid in game.folded:
            s = "弃牌"
        elif pid in game.all_in:
            s = "全下"
        else:
            s = "在局"
        lines.append(f"|- {idx}. {name}  {s}  投入:{game.total_bet.get(pid, 0)}")
    board_str = " ".join(card_str(c) for c in game.board) if game.board else "无"
    board_display = f"|--------------------+\n| {board_str}\n|--------------------+"
    phase_cn = {'preflop':'翻牌前','flop':'翻牌圈','turn':'转牌圈','river':'河牌圈','showdown':'摊牌'}.get(game.phase, game.phase)
    cur = game.current_player()
    cur_text = ""
    if cur and game.phase in ('preflop','flop','turn','river'):
        to_call = game.current_bet - game.round_bets.get(cur, 0)
        if to_call < 0: to_call = 0
        cur_text = f"|- 当前：{await get_name(app, cur)}  需跟注：{to_call}"
    return (
        f"|- 积分德州牌桌\n\n|- 状态：{phase_cn}\n\n|- 公牌：\n{board_display}\n\n"
        f"|- 奖池：{game.pot}  当前下注：{game.current_bet}\n\n{cur_text}\n\n|- 玩家：\n\n" +
        "\n".join(lines) + "\n"
    )

async def update_table_msg(game, app):
    text = await build_table_view(game, app)
    try:
        await app.bot.edit_message_text(chat_id=game.chat_id, message_id=game.game_msg_id, text=text)
    except:
        pass

async def start_turn_timer(game, app):
    game.cancel_timer()
    uid = game.current_player()
    if not uid:
        alive = [p for p in game.active_players if p not in game.folded]
        if alive and all(p in game.all_in for p in alive):
            game.phase = 'showdown'
            await settle_game(game, app)
        return

    if game.action_msg_id:
        try: await app.bot.delete_message(game.chat_id, game.action_msg_id)
        except: pass
        game.action_msg_id = None

    keyboard = get_buttons(game, uid)
    text = await build_action_view(game, app, uid)
    msg = await app.bot.send_message(game.chat_id, text, reply_markup=keyboard)
    game.action_msg_id = msg.message_id

    async def timeout():
        await asyncio.sleep(TURN_TIMEOUT)
        if game.phase in ('preflop','flop','turn','river') and game.current_player() == uid:
            game.handle_action(uid, 'fold')
            await app.bot.send_message(game.chat_id, f"⏰ {await get_name(app, uid)} 超时未操作，自动弃牌")
            if game.action_msg_id:
                try: await app.bot.delete_message(game.chat_id, game.action_msg_id)
                except: pass
            if game.phase == 'showdown':
                await settle_game(game, app)
            else:
                await update_table_msg(game, app)
                await start_turn_timer(game, app)
    game.turn_task = asyncio.create_task(timeout())

async def start_auto_start(game, app):
    game.cancel_auto_start()
    async def auto():
        await asyncio.sleep(AUTO_START_TIMEOUT)
        if game.phase == 'waiting' and len(game.players) >= 2:
            if game.start_game():
                await update_table_msg(game, app)
                await start_turn_timer(game, app)
    game.auto_start_task = asyncio.create_task(auto())

def get_buttons(game, uid):
    if uid not in game.active_players or uid in game.folded or uid in game.all_in or uid != game.current_player():
        return InlineKeyboardMarkup([[InlineKeyboardButton("🂠 查看手牌", callback_data="texas_hand")]])

    to_call = game.current_bet - game.round_bets.get(uid, 0)
    if to_call < 0: to_call = 0

    row1 = [InlineKeyboardButton("❌ 弃牌", callback_data="texas_fold")]
    if to_call == 0:
        row1.append(InlineKeyboardButton("✅ 过牌", callback_data="texas_check"))
    else:
        row1.append(InlineKeyboardButton(f"✅ 跟注 {to_call}", callback_data="texas_call"))

    btns = [[InlineKeyboardButton("🂠 查看手牌", callback_data="texas_hand")], row1]

    if game.chips[uid] > 0:
        raise_extra = FIXED_MIN_RAISE
        total_need = to_call + raise_extra
        if game.chips[uid] >= total_need:
            btns.append([InlineKeyboardButton(f"🔼 加注 {raise_extra}", callback_data=f"texas_raise_{raise_extra}")])
        btns.append([InlineKeyboardButton(f"🔥 全下 {game.chips[uid]}", callback_data="texas_allin")])
        btns.append([InlineKeyboardButton("✏️ 自定义加注", callback_data="texas_custom_raise")])
    return InlineKeyboardMarkup(btns)

async def settle_game(game, app):
    game.cancel_timer()
    game.cancel_auto_start()
    if game.action_msg_id:
        try: await app.bot.delete_message(game.chat_id, game.action_msg_id)
        except: pass
    if game.game_msg_id:
        try: await app.bot.delete_message(game.chat_id, game.game_msg_id)
        except: pass

    result = game.showdown()
    if not result:
        return
    hand_types = result[0][3] if len(result[0]) > 3 else {}
    only_survivor = (len(result) == 1 and result[0][1] == "最后赢家")

    board_str = " ".join(card_str(c) for c in game.board) if game.board else "无"
    board_display = f"|--------------------+\n| {board_str}\n|--------------------+"

    card_lines = []
    if not only_survivor:
        for uid in game.showdown_order:
            name = await get_name(app, uid)
            if uid in game.all_in:
                hand = game.hands.get(uid, [])
                hand_str = " ".join(card_str(c) for c in hand) if hand else "无"
                hand_cn = hand_types.get(uid, "")
                if hand_cn:
                    card_lines.append(f"{name}：{hand_str} / {hand_cn} (全下)")
                else:
                    card_lines.append(f"{name}：{hand_str} (全下)")
            else:
                hand = game.hands.get(uid, [])
                hand_str = " ".join(card_str(c) for c in hand) if hand else "无"
                cn = hand_types.get(uid, "")
                card_lines.append(f"{name}：{hand_str} / {cn}" if cn else f"{name}：{hand_str}")
    else:
        uid = game.showdown_order[0] if game.showdown_order else result[0][0]
        card_lines.append(f"{await get_name(app, uid)}：未亮牌")

    for uid in game.players:
        if uid in game.folded:
            card_lines.append(f"{await get_name(app, uid)}：弃牌")

    total_pot = sum(game.total_bet.values())
    prize_lines = []
    for wid, desc, amt, _ in result:
        name = await get_name(app, wid)
        prize_lines.append(f"{name} +{amt}" if only_survivor else f"{name} +{amt} ({desc})")

    profit_lines = []
    for uid in game.players:
        name = await get_name(app, uid)
        start = game.initial_chips.get(uid, STARTING_CHIPS)
        end = game.chips.get(uid, 0)
        net = end - start
        profit_lines.append(f"{name}  投入:{game.total_bet.get(uid,0)}  盈亏:{net:+d}")

    broke = [uid for uid in game.players if game.chips[uid] == 0]
    broke_text = ""
    if broke:
        names = [await get_name(app, uid) for uid in broke]
        broke_text = f"\n⚠️ 以下玩家筹码归零: {', '.join(names)}，使用 /add 补充"

    win_text = (
        f"积分德州已结算\n\n|- 积分德州牌桌\n\n|- 状态：摊牌\n\n|- 公牌：\n{board_display}\n\n"
        f"|- 奖池：{total_pot}\n\n结果：摊牌结算\n\n牌型：\n" + "\n".join(card_lines) +
        f"\n\n派奖：\n" + "\n".join(prize_lines) + f"\n\n投入/盈亏：\n" + "\n".join(profit_lines) + broke_text
    )
    await app.bot.send_message(game.chat_id, win_text)


# ==================== 炸金花（完整） ====================
class ZhaJinHuaGame:
    def __init__(self, chat_id, owner_id):
        self.chat_id = chat_id
        self.owner_id = owner_id
        self.players = []
        self.chips = {}
        self.hands = {}
        self.seen = set()
        self.folded = set()
        self.deck = []
        self.pot = 0
        self.current_bet = 0
        self.total_bet = defaultdict(int)
        self.phase = 'waiting'
        self.players_in_game = []
        self.actor_idx = 0
        self.game_msg_id = None
        self.turn_task = None

    def add_player(self, uid):
        if uid not in self.players and self.phase == 'waiting':
            if uid not in group_chips[self.chat_id]:
                group_chips[self.chat_id][uid] = STARTING_CHIPS
            self.chips[uid] = group_chips[self.chat_id][uid]
            self.players.append(uid)
            return True
        return False

    def start_game(self):
        if len(self.players) < 2: return False
        for uid in list(self.players):
            ante = min(ZJH_ANTE, self.chips[uid])
            self.chips[uid] -= ante
            self.pot += ante
            self.total_bet[uid] += ante
            if self.chips[uid] == 0:
                self.folded.add(uid)
                self.players.remove(uid)
        if len(self.players) < 2:
            survivor = self.players[0]
            self.chips[survivor] += self.pot
            self.pot = 0
            return False
        self.phase = 'playing'
        self.players_in_game = self.players.copy()
        self.deck = [Card.new(r + s) for r in "23456789TJQKA" for s in "shdc"]
        random.shuffle(self.deck)
        for uid in self.players_in_game:
            self.hands[uid] = [self.deck.pop() for _ in range(3)]
        self.actor_idx = random.randrange(len(self.players_in_game))
        self.current_bet = 0
        return True

    def get_buttons(self, uid):
        buttons = []
        if uid in self.hands and uid not in self.folded:
            buttons.append([InlineKeyboardButton("🂠 查看手牌", callback_data="zjh_hand")])
        if uid not in self.players_in_game or uid in self.folded or uid != self.current_player_id():
            return InlineKeyboardMarkup(buttons)

        multiplier = ZJH_SEEN_MULTIPLIER if uid in self.seen else 1
        if uid not in self.seen:
            buttons.append([InlineKeyboardButton("👁️ 看牌", callback_data="zjh_see")])
        else:
            buttons.append([InlineKeyboardButton("🙈 已看牌", callback_data="zjh_seen_info")])
        buttons.append([InlineKeyboardButton("👋 弃牌", callback_data="zjh_fold")])
        needed = self.current_bet * multiplier - self.total_bet[uid]
        if needed < 0: needed = 0
        if self.current_bet == 0:
            buttons.append([InlineKeyboardButton("✅ 跟注 (底)", callback_data="zjh_call")])
        else:
            buttons.append([InlineKeyboardButton(f"✅ 跟注 {needed}", callback_data="zjh_call")])
        buttons.append([InlineKeyboardButton("⬆️ 加注", callback_data="zjh_raise_menu")])
        alive = [p for p in self.players_in_game if p != uid and p not in self.folded]
        if alive:
            buttons.append([InlineKeyboardButton("⚔️ 比牌", callback_data="zjh_compare_menu")])
        return InlineKeyboardMarkup(buttons)

    def current_player_id(self):
        if not self.players_in_game or self.actor_idx >= len(self.players_in_game):
            return None
        return self.players_in_game[self.actor_idx]

    def next_player(self):
        start = self.actor_idx
        while True:
            self.actor_idx = (self.actor_idx + 1) % len(self.players_in_game)
            if self.actor_idx == start: break
            uid = self.players_in_game[self.actor_idx]
            if uid not in self.folded: return uid
        return None

    def handle_action(self, uid, action, amount=None, target=None):
        if uid != self.current_player_id(): return False, "还没轮到你"
        if action == 'see':
            if uid in self.seen: return False, "已看过牌"
            self.seen.add(uid)
            return True, "看牌"
        elif action == 'fold':
            self.folded.add(uid)
            self.players_in_game.remove(uid)
            if self.actor_idx >= len(self.players_in_game):
                self.actor_idx = 0
            alive = [p for p in self.players_in_game if p not in self.folded]
            if len(alive) == 1: self.phase = 'showdown'
            else: self.next_player()
            return True, "弃牌"
        elif action == 'call':
            multiplier = ZJH_SEEN_MULTIPLIER if uid in self.seen else 1
            bet_amount = self.current_bet * multiplier
            if bet_amount == 0: bet_amount = ZJH_MIN_RAISE * multiplier
            actual = min(bet_amount, self.chips[uid])
            self.chips[uid] -= actual
            self.pot += actual
            self.total_bet[uid] += actual
            if self.chips[uid] == 0:
                self.folded.add(uid)
                self.players_in_game.remove(uid)
            if self.current_bet == 0: self.current_bet = ZJH_MIN_RAISE
            alive = [p for p in self.players_in_game if p not in self.folded]
            if len(alive) == 1: self.phase = 'showdown'
            else: self.next_player()
            return True, f"跟注 {actual}"
        elif action == 'raise':
            multiplier = ZJH_SEEN_MULTIPLIER if uid in self.seen else 1
            min_raise = ZJH_MIN_RAISE * multiplier
            if amount < min_raise: return False, f"最小加注为 {min_raise}"
            if amount > self.chips[uid]: return False, "筹码不足"
            self.chips[uid] -= amount
            self.pot += amount
            self.total_bet[uid] += amount
            self.current_bet = amount // multiplier
            alive = [p for p in self.players_in_game if p not in self.folded]
            if len(alive) == 1: self.phase = 'showdown'
            else: self.next_player()
            return True, f"加注 {amount}"
        elif action == 'compare':
            if target not in self.players_in_game or target == uid or target in self.folded:
                return False, "无效的对手"
            multiplier = ZJH_SEEN_MULTIPLIER if uid in self.seen else 1
            cost = self.current_bet * multiplier
            if cost > self.chips[uid]: return False, "筹码不足无法比牌"
            self.chips[uid] -= cost
            self.pot += cost
            self.total_bet[uid] += cost
            result = compare_zjh(self.hands[uid], self.hands[target])
            loser = target if result > 0 else uid
            self.folded.add(loser)
            self.players_in_game.remove(loser)
            if self.actor_idx >= len(self.players_in_game):
                self.actor_idx = 0
            alive = [p for p in self.players_in_game if p not in self.folded]
            if len(alive) == 1: self.phase = 'showdown'
            else: self.next_player()
            return True, loser
        return False, "未知操作"

    def showdown(self):
        alive = [p for p in self.players_in_game if p not in self.folded]
        if len(alive) == 1:
            winner = alive[0]
            self.chips[winner] += self.pot
            self.pot = 0
            for uid in self.chips: group_chips[self.chat_id][uid] = self.chips[uid]
            return [(winner, "最后存活")]
        return []

# 炸金花比较辅助函数
def parse_card(card_int):
    raw = Card.int_to_str(card_int)
    RANK_VALUES = {'2':2,'3':3,'4':4,'5':5,'6':6,'7':7,'8':8,'9':9,'T':10,'J':11,'Q':12,'K':13,'A':14}
    return RANK_VALUES.get(raw[0], 0), raw[1]

def get_zjh_hand_type(cards):
    ranks, suits = [], []
    for c in cards:
        r, s = parse_card(c)
        ranks.append(r); suits.append(s)
    ranks.sort(reverse=True)
    is_flush = len(set(suits)) == 1
    is_straight = len(set(ranks)) == 3 and (max(ranks)-min(ranks)==2)
    if set(ranks) == {14,2,3}:
        is_straight = True
        ranks = [3,2,14]
    if len(set(ranks)) == 1: return (6, "豹子")
    if is_flush and is_straight: return (5, "同花顺")
    if is_flush: return (4, "同花")
    if is_straight: return (3, "顺子")
    if len(set(ranks)) == 2: return (2, "对子")
    if set(ranks) == {2,3,5}: return (0, "特殊235")
    return (1, "单张")

def compare_zjh(hand1, hand2):
    t1, _ = get_zjh_hand_type(hand1)
    t2, _ = get_zjh_hand_type(hand2)
    if t1 == 0 and t2 == 6: return 1
    if t2 == 0 and t1 == 6: return -1
    if t1 > t2: return 1
    if t2 > t1: return -1
    def cmp_ranks(h):
        r = sorted([parse_card(c)[0] for c in h], reverse=True)
        if set(r) == {14,2,3}: r = [3,2,14]
        if len(set(r)) == 2:
            for val in r:
                if r.count(val) == 2: return (val, [x for x in r if x != val][0])
        return tuple(r)
    r1, r2 = cmp_ranks(hand1), cmp_ranks(hand2)
    if r1 > r2: return 1
    if r1 < r2: return -1
    return 0

# ==================== 21点 ====================
class BlackjackGame:
    def __init__(self, chat_id, owner_id):
        self.chat_id = chat_id
        self.owner_id = owner_id
        self.players = {}
        self.dealer_hand = []
        self.deck = []
        self.phase = 'betting'
        self.game_msg_id = None

    def add_player(self, uid, bet):
        if uid not in self.players:
            if uid not in group_chips[self.chat_id]:
                group_chips[self.chat_id][uid] = STARTING_CHIPS
            if bet > group_chips[self.chat_id][uid]: return False, "筹码不足"
            group_chips[self.chat_id][uid] -= bet
            self.players[uid] = {'bet': bet, 'hands': [], 'stayed': [False], 'busted': [False]}
            return True, "已加入"
        return False, "已在游戏中"

    def start_game(self):
        self.deck = [Card.new(r + s) for r in "23456789TJQKA" for s in "shdc"] * 2
        random.shuffle(self.deck)
        for uid in self.players:
            self.players[uid]['hands'] = [[self.deck.pop(), self.deck.pop()]]
            self.players[uid]['stayed'] = [False]
            self.players[uid]['busted'] = [False]
        self.dealer_hand = [self.deck.pop(), self.deck.pop()]
        self.phase = 'playing'

    def hit(self, uid):
        if self.phase != 'playing': return False, "已结束"
        if uid not in self.players: return False
        hand = self.players[uid]['hands'][0]
        if self.players[uid]['stayed'][0] or self.players[uid]['busted'][0]:
            return False, "已停牌或爆牌"
        hand.append(self.deck.pop())
        if self._hand_value(hand) > 21: self.players[uid]['busted'][0] = True
        return True, None

    def stay(self, uid):
        if self.phase != 'playing': return False
        if uid not in self.players: return False
        self.players[uid]['stayed'][0] = True
        return True, None

    def dealer_play(self):
        while self._hand_value(self.dealer_hand) < 17:
            self.dealer_hand.append(self.deck.pop())

    def _hand_value(self, hand):
        val, aces = 0, 0
        for c in hand:
            rank = Card.int_to_str(c)[0]
            if rank in '23456789': val += int(rank)
            elif rank in 'TJQK': val += 10
            else: val += 11; aces += 1
        while val > 21 and aces > 0:
            val -= 10; aces -= 1
        return val

    def settle(self):
        self.dealer_play()
        dealer_val = self._hand_value(self.dealer_hand)
        results = []
        for uid, data in self.players.items():
            hand = data['hands'][0]
            player_val = self._hand_value(hand)
            bet = data['bet']
            if data['busted'][0]: outcome = -bet
            elif dealer_val > 21: outcome = bet
            elif player_val > dealer_val: outcome = bet
            elif player_val == dealer_val: outcome = 0
            else: outcome = -bet
            group_chips[self.chat_id][uid] += (bet + outcome)
            results.append((uid, bet, outcome, player_val, dealer_val))
        self.phase = 'finished'
        return results

# ==================== 梭哈（简化版 Show Hand） ====================
class ShowHandGame:
    def __init__(self, chat_id, owner_id):
        self.chat_id = chat_id
        self.owner_id = owner_id
        self.players = []
        self.chips = {}
        self.hands = {}
        self.folded = set()
        self.deck = []
        self.pot = 0
        self.phase = 'waiting'
        self.players_in_game = []
        self.actor_idx = 0
        self.current_bet = 0
        self.round_bets = {}
        self.acted_this_round = set()
        self.game_msg_id = None

    def add_player(self, uid):
        if uid not in self.players and self.phase == 'waiting':
            if uid not in group_chips[self.chat_id]:
                group_chips[self.chat_id][uid] = STARTING_CHIPS
            self.chips[uid] = group_chips[self.chat_id][uid]
            self.players.append(uid)
            return True
        return False

    def start_game(self):
        if len(self.players) < 2: return False
        for uid in self.players:
            self.chips[uid] = group_chips[self.chat_id].get(uid, STARTING_CHIPS)
        self.phase = 'playing'
        self.deck = [Card.new(r + s) for r in "23456789TJQKA" for s in "shdc"]
        random.shuffle(self.deck)
        for uid in self.players:
            self.hands[uid] = [self.deck.pop() for _ in range(5)]  # 直接发5张，简化
        self.players_in_game = self.players.copy()
        self.current_bet = SHOW_HAND_ANTE
        self.actor_idx = 0
        self.acted_this_round.clear()
        return True

    def showdown(self):
        # 比较五张牌的牌型（简化：只比较一对或高牌）
        alive = [p for p in self.players_in_game if p not in self.folded]
        # 使用 treys 评估最佳五张牌
        evaluator = Evaluator()
        scores = {}
        for uid in alive:
            hand = self.hands[uid]
            score = evaluator.evaluate(hand, [])
            scores[uid] = score
        best = min(scores.values())
        winners = [uid for uid in alive if scores[uid] == best]
        for uid in winners:
            self.chips[uid] += self.pot // len(winners)
        for uid in self.chips:
            group_chips[self.chat_id][uid] = self.chips[uid]
        return winners

# ==================== 牛牛 ====================
class NiuNiuGame:
    def __init__(self, chat_id, owner_id):
        self.chat_id = chat_id
        self.owner_id = owner_id
        self.players = []
        self.bets = {}
        self.hands = {}
        self.deck = []
        self.phase = 'waiting'

    def add_player(self, uid, bet):
        if uid not in self.players and self.phase == 'waiting':
            if uid not in group_chips[self.chat_id]:
                group_chips[self.chat_id][uid] = STARTING_CHIPS
            if bet > group_chips[self.chat_id][uid]: return False, "筹码不足"
            group_chips[self.chat_id][uid] -= bet
            self.players.append(uid)
            self.bets[uid] = bet
            return True
        return False

    def start_game(self):
        if len(self.players) < 2: return False
        self.deck = [Card.new(r + s) for r in "23456789TJQKA" for s in "shdc"]
        random.shuffle(self.deck)
        for uid in self.players:
            self.hands[uid] = [self.deck.pop() for _ in range(5)]
        self.phase = 'showdown'

    def evaluate_hand(self, cards):
        values = []
        for c in cards:
            rank = Card.int_to_str(c)[0]
            if rank in '23456789': values.append(int(rank))
            else: values.append(10)
        for i in range(5):
            for j in range(i+1,5):
                for k in range(j+1,5):
                    if (values[i]+values[j]+values[k]) % 10 == 0:
                        remainder = (sum(values)-values[i]-values[j]-values[k]) % 10
                        if remainder == 0: return 3, "牛牛"
                        return 2, f"牛{remainder}"
        return 1, "无牛"

    def settle(self):
        dealer_uid = self.players[0]
        dealer_cards = self.hands[dealer_uid]
        dealer_multi, _ = self.evaluate_hand(dealer_cards)
        results = []
        for uid in self.players[1:]:
            player_multi, desc = self.evaluate_hand(self.hands[uid])
            if player_multi > dealer_multi: win = self.bets[uid]
            elif player_multi == dealer_multi: win = 0
            else: win = -self.bets[uid]
            group_chips[self.chat_id][uid] += (self.bets[uid] + win)
            results.append((uid, self.bets[uid], win, desc))
        return results

# ==================== 全局游戏管理 ====================
active_games = {}

def is_auth(chat_id):
    return chat_id in AUTHORIZED_GROUPS

async def need_auth(update, context):
    if not is_auth(update.effective_chat.id):
        await update.effective_message.reply_text("❌ 此群组未授权，请联系管理员。")
        return False
    return True

# ---------- 命令处理（需整合） ----------
async def cmd_start(update, context):
    await update.message.reply_text("/dz 德州 /zjh 炸金花 /bj 21点 /showhand 梭哈 /niuniu 牛牛")


# ---------- 命令处理：德州扑克 ----------
async def cmd_dz(update, context):
    if not await need_auth(update, context): return
    chat_id = update.effective_chat.id
    if chat_id in active_games and hasattr(active_games[chat_id], 'phase') and active_games[chat_id].phase != 'waiting':
        await update.message.reply_text("当前已有进行中的游戏，请等待结束。")
        return
    game = PokerGame(chat_id, update.effective_user.id)
    game.add_player(update.effective_user.id)
    active_games[chat_id] = game
    plist = [f"{i}. {await get_name(context.application, uid)}" for i, uid in enumerate(game.players, 1)]
    kb = [[InlineKeyboardButton("加入游戏", callback_data="texas_join")]]
    if len(game.players) >= 2:
        kb.append([InlineKeyboardButton("开始游戏", callback_data="texas_start")])
    msg = await update.message.reply_text(
        f"🃏 新一局德州扑克！\n发起人: {await get_name(context.application, update.effective_user.id)}\n\n"
        f"已加入玩家:\n" + "\n".join(plist) + "\n\n点击按钮加入或开始",
        reply_markup=InlineKeyboardMarkup(kb)
    )
    game.game_msg_id = msg.message_id

async def cmd_zjh(update, context):
    if not await need_auth(update, context): return
    chat_id = update.effective_chat.id
    if chat_id in active_games and active_games[chat_id].phase != 'waiting':
        await update.message.reply_text("当前已有进行中的游戏，请等待结束。")
        return
    game = ZhaJinHuaGame(chat_id, update.effective_user.id)
    game.add_player(update.effective_user.id)
    active_games[chat_id] = game
    plist = [f"{i}. {await get_name(context.application, uid)}" for i, uid in enumerate(game.players, 1)]
    kb = [[InlineKeyboardButton("加入游戏", callback_data="zjh_join")]]
    if len(game.players) >= 2:
        kb.append([InlineKeyboardButton("开始游戏", callback_data="zjh_start")])
    msg = await update.message.reply_text(
        f"🃏 炸金花房间！\n发起人: {await get_name(context.application, update.effective_user.id)}\n\n"
        f"已加入玩家:\n" + "\n".join(plist) + "\n\n点击按钮加入或开始",
        reply_markup=InlineKeyboardMarkup(kb)
    )
    game.game_msg_id = msg.message_id

async def cmd_bj(update, context):
    if not await need_auth(update, context): return
    chat_id = update.effective_chat.id
    # 21点使用简单流程：玩家直接发送 /bj 下注金额 加入
    try:
        bet = int(context.args[0]) if context.args else BJ_MIN_BET
    except:
        bet = BJ_MIN_BET
    if chat_id not in active_games or active_games[chat_id].phase != 'betting':
        game = BlackjackGame(chat_id, update.effective_user.id)
        active_games[chat_id] = game
        msg = await update.message.reply_text(f"21点桌已创建，发送 /bj 金额 加入，至少2人后自动开始")
        game.game_msg_id = msg.message_id
    game = active_games[chat_id]
    ok, info = game.add_player(update.effective_user.id, bet)
    if not ok:
        await update.message.reply_text(info)
    else:
        await update.message.reply_text(f"✅ {await get_name(context.application, update.effective_user.id)} 已下注 {bet}")
        if len(game.players) >= 2:
            game.start_game()
            await context.bot.edit_message_text(chat_id=chat_id, message_id=game.game_msg_id, text="21点开始！请使用 /hit 或 /stay 操作")

async def cmd_hit(update, context):
    chat_id = update.effective_chat.id
    game = active_games.get(chat_id)
    if not isinstance(game, BlackjackGame): return
    ok, info = game.hit(update.effective_user.id)
    if not ok: await update.message.reply_text(info)
    else: await update.message.reply_text("发牌")

async def cmd_stay(update, context):
    chat_id = update.effective_chat.id
    game = active_games.get(chat_id)
    if not isinstance(game, BlackjackGame): return
    ok, info = game.stay(update.effective_user.id)
    if not ok: await update.message.reply_text(info)
    # 简单处理：不自动结算，由玩家手动 /settle
    await update.message.reply_text("已停牌，输入 /settle 结算")

async def cmd_settle(update, context):
    chat_id = update.effective_chat.id
    game = active_games.get(chat_id)
    if not isinstance(game, BlackjackGame): return
    results = game.settle()
    text = "21点结算:\n"
    for uid, bet, outcome, pval, dval in results:
        name = await get_name(context.application, uid)
        text += f"{name}: 投注{bet} 结果{outcome:+d} (玩家{pval} 庄家{dval})\n"
    await update.message.reply_text(text)
    del active_games[chat_id]

async def cmd_showhand(update, context):
    if not await need_auth(update, context): return
    chat_id = update.effective_chat.id
    game = ShowHandGame(chat_id, update.effective_user.id)
    game.add_player(update.effective_user.id)
    active_games[chat_id] = game
    await update.message.reply_text("梭哈房间已创建，发送 /join 加入，满2人后自动开始")

async def cmd_niuniu(update, context):
    if not await need_auth(update, context): return
    chat_id = update.effective_chat.id
    try:
        bet = int(context.args[0]) if context.args else NIU_BET
    except:
        bet = NIU_BET
    game = NiuNiuGame(chat_id, update.effective_user.id)
    ok, info = game.add_player(update.effective_user.id, bet)
    if not ok:
        await update.message.reply_text(info)
        return
    active_games[chat_id] = game
    await update.message.reply_text(f"牛牛房间已创建，下注{bet}，发送 /join 加入")
    # 简化：直接开始
    game.start_game()
    results = game.settle()
    text = "牛牛结算:\n"
    for uid, bet, win, desc in results:
        name = await get_name(context.application, uid)
        text += f"{name}: {desc} 投注{bet} 盈亏{win:+d}\n"
    await update.message.reply_text(text)
    del active_games[chat_id]

async def cmd_end(update, context):
    if not await need_auth(update, context): return
    chat_id = update.effective_chat.id
    game = active_games.pop(chat_id, None)
    if not game:
        await update.message.reply_text("当前没有进行中的游戏。")
        return
    if isinstance(game, PokerGame):
        game.cancel_timer()
        game.cancel_auto_start()
    await update.message.reply_text("游戏已被手动终止。")
    try:
        await context.bot.delete_message(chat_id, game.game_msg_id)
    except:
        pass

async def cmd_add(update, context):
    if not await need_auth(update, context): return
    chat_id = update.effective_chat.id
    target = None
    amt = 0
    if context.args and len(context.args) >= 2:
        a1 = context.args[0]
        if update.message.entities:
            for e in update.message.entities:
                if e.type == 'text_mention': target = e.user.id
                elif e.type == 'mention':
                    try: target = (await context.bot.get_chat(a1.lstrip('@'))).id
                    except: pass
        if not target:
            try: target = int(a1)
            except: pass
        try: amt = int(context.args[1])
        except: pass
    elif context.args and len(context.args) == 1:
        try: amt = int(context.args[0])
        except: pass
        if update.message.reply_to_message:
            target = update.message.reply_to_message.from_user.id
    if not target or amt <= 0:
        await update.message.reply_text("用法: /add @用户名 数量")
        return
    group_chips[chat_id][target] = group_chips[chat_id].get(target, STARTING_CHIPS) + amt
    name = await get_name(context.application, target)
    await update.message.reply_text(f"✅ 已给 {name} 增加 {amt} 筹码，当前: {group_chips[chat_id][target]}")

async def cmd_ph(update, context):
    if not await need_auth(update, context): return
    chat_id = update.effective_chat.id
    chips = group_chips.get(chat_id, {})
    if not chips:
        await update.message.reply_text("无筹码记录")
        return
    lines = [f"{i}. {await get_name(context.application, u)}: {c}" for i, (u, c) in enumerate(chips.items(), 1)]
    await update.message.reply_text("💰 当前筹码:\n" + "\n".join(lines))

async def cmd_shouquan(update, context):
    if update.effective_user.id != ADMIN_USER_ID:
        await update.message.reply_text("❌ 仅管理员可用")
        return
    cid = update.effective_chat.id if update.effective_chat.type != "private" else int(context.args[0]) if context.args else None
    if not cid:
        await update.message.reply_text("用法: /shouquan 群组ID"); return
    AUTHORIZED_GROUPS.add(cid)
    await update.message.reply_text(f"✅ 群组 {cid} 已授权")

async def cmd_qxshouquan(update, context):
    if update.effective_user.id != ADMIN_USER_ID:
        await update.message.reply_text("❌ 仅管理员可用")
        return
    cid = update.effective_chat.id if update.effective_chat.type != "private" else int(context.args[0]) if context.args else None
    if not cid:
        await update.message.reply_text("用法: /qxshouquan 群组ID"); return
    AUTHORIZED_GROUPS.discard(cid)
    await update.message.reply_text(f"✅ 群组 {cid} 已取消授权")

# ---------- 按钮回调 ----------
async def on_button(update, context):
    q = update.callback_query
    data = q.data
    chat_id = q.message.chat.id
    if not is_auth(chat_id):
        await q.answer("未授权", show_alert=True); return
    game = active_games.get(chat_id)
    if not game:
        await q.edit_message_text("游戏不存在"); return

    # 德州按钮
    if isinstance(game, PokerGame):
        if game.phase == 'showdown':
            await settle_game(game, context.application)
            active_games.pop(chat_id, None); return

        if data == 'texas_hand':
            user = q.from_user
            if user.id in game.hands and user.id not in game.folded and game.phase != 'showdown':
                hand = game.hands[user.id]
                await q.answer(f"你的手牌: {card_str(hand[0])}  {card_str(hand[1])}", show_alert=True)
            else:
                await q.answer("无法查看手牌", show_alert=True)
            return

        await q.answer()
        user = q.from_user

        if game.phase == 'waiting':
            if data == 'texas_join':
                if game.add_player(user.id):
                    plist = [f"{i}. {await get_name(context.application, u)}" for i, u in enumerate(game.players, 1)]
                    kb = [[InlineKeyboardButton("加入游戏", callback_data="texas_join")]]
                    if len(game.players) >= 2:
                        kb.append([InlineKeyboardButton("开始游戏", callback_data="texas_start")])
                    await q.edit_message_text("已加入玩家:\n" + "\n".join(plist) + "\n\n点击按钮加入或开始", reply_markup=InlineKeyboardMarkup(kb))
                    if len(game.players) >= 2:
                        await start_auto_start(game, context.application)
                else:
                    await q.answer("加入失败", show_alert=True)
            elif data == 'texas_start':
                if user.id != game.owner_id:
                    await q.answer("只有发起人可以开始", show_alert=True); return
                if len(game.players) < 2:
                    await q.answer("至少需要2人", show_alert=True); return
                if any(game.chips[u] <= 0 for u in game.players):
                    await q.answer("有玩家筹码不足", show_alert=True); return
                if game.start_game():
                    await update_table_msg(game, context.application)
                    await start_turn_timer(game, context.application)
                else:
                    await q.edit_message_text("开始失败")
            return

        if game.phase in ('preflop','flop','turn','river'):
            if user.id != game.current_player():
                await q.answer("还没轮到你", show_alert=True); return
            if data == 'texas_fold': ok, desc = game.handle_action(user.id, 'fold')
            elif data == 'texas_check': ok, desc = game.handle_action(user.id, 'check')
            elif data == 'texas_call': ok, desc = game.handle_action(user.id, 'call')
            elif data == 'texas_allin': ok, desc = game.handle_action(user.id, 'allin')
            elif data.startswith('texas_raise_'):
                try:
                    amt = int(data.split('_')[2])
                    ok, desc = game.handle_action(user.id, 'raise', amount=amt)
                except:
                    await q.answer("无效加注额", show_alert=True); return
            elif data == 'texas_custom_raise':
                await q.answer("请回复此消息输入“加注XXX”来额外加注", show_alert=True); return
            else: return

            if not ok:
                await q.answer(desc, show_alert=True); return
            if game.action_msg_id:
                try: await context.bot.delete_message(chat_id, game.action_msg_id)
                except: pass
            await action_notify(chat_id, context.application, user.id, desc)
            if game.phase == 'showdown':
                await settle_game(game, context.application)
                active_games.pop(chat_id, None); return
            await update_table_msg(game, context.application)
            await start_turn_timer(game, context.application)
        return

    # 炸金花按钮
    if isinstance(game, ZhaJinHuaGame):
        await q.answer()
        user = q.from_user
        if game.phase == 'waiting':
            if data == 'zjh_join':
                if game.add_player(user.id):
                    plist = [f"{i}. {await get_name(context.application, u)}" for i, u in enumerate(game.players, 1)]
                    kb = [[InlineKeyboardButton("加入游戏", callback_data="zjh_join")]]
                    if len(game.players) >= 2:
                        kb.append([InlineKeyboardButton("开始游戏", callback_data="zjh_start")])
                    await q.edit_message_text("已加入玩家:\n" + "\n".join(plist) + "\n\n点击按钮加入或开始", reply_markup=InlineKeyboardMarkup(kb))
                else:
                    await q.answer("加入失败", show_alert=True)
            elif data == 'zjh_start':
                if user.id != game.owner_id:
                    await q.answer("只有发起人可以开始", show_alert=True); return
                if len(game.players) < 2:
                    await q.answer("至少需要2人", show_alert=True); return
                if game.start_game():
                    await context.bot.edit_message_text(chat_id=chat_id, message_id=game.game_msg_id, text="炸金花开始！")
                    # 可启动定时器，这里省略
                else:
                    await q.edit_message_text("开始失败")
            return
        # 游戏阶段按钮
        # 此处省略详细炸金花按钮处理，可使用之前对话中的炸金花按钮逻辑
        return

# ---------- 文字命令处理 ----------
async def on_text(update, context):
    msg = update.effective_message
    if not msg or not msg.text: return
    user = update.effective_user
    if user.is_bot: return
    chat_id = update.effective_chat.id
    game = active_games.get(chat_id)

    # 德州文字加注
    if isinstance(game, PokerGame) and game.phase in ('preflop','flop','turn','river'):
        if user.id != game.current_player(): return
        m = re.match(r'^加注\s*(\d+)$', msg.text.strip())
        if not m:
            if msg.reply_to_message and msg.reply_to_message.message_id == game.game_msg_id:
                m = re.match(r'^加注\s*(\d+)$', msg.text.strip())
            if not m: return
        amt = int(m.group(1))
        ok, desc = game.handle_action(user.id, 'raise', amount=amt)
        if not ok: await msg.reply_text(f"❌ {desc}"); return
        if game.action_msg_id:
            try: await context.bot.delete_message(chat_id, game.action_msg_id)
            except: pass
        await action_notify(chat_id, context.application, user.id, desc)
        if game.phase == 'showdown':
            await settle_game(game, context.application)
            active_games.pop(chat_id, None); return
        await update_table_msg(game, context.application)
        await start_turn_timer(game, context.application)

# ---------- 主函数 ----------
def main():
    TOKEN = os.environ.get("BOT_TOKEN")
    if not TOKEN:
        logger.error("未设置 BOT_TOKEN"); return
    app = Application.builder().token(TOKEN).build()
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("dz", cmd_dz))
    app.add_handler(CommandHandler("zjh", cmd_zjh))
    app.add_handler(CommandHandler("bj", cmd_bj))
    app.add_handler(CommandHandler("hit", cmd_hit))
    app.add_handler(CommandHandler("stay", cmd_stay))
    app.add_handler(CommandHandler("settle", cmd_settle))
    app.add_handler(CommandHandler("showhand", cmd_showhand))
    app.add_handler(CommandHandler("niuniu", cmd_niuniu))
    app.add_handler(CommandHandler("end", cmd_end))
    app.add_handler(CommandHandler("add", cmd_add))
    app.add_handler(CommandHandler("ph", cmd_ph))
    app.add_handler(CommandHandler("shouquan", cmd_shouquan))
    app.add_handler(CommandHandler("qxshouquan", cmd_qxshouquan))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.add_handler(CallbackQueryHandler(on_button))

    # 启动每日重置筹码任务
    loop = asyncio.get_event_loop()
    loop.create_task(daily_reset_chips())

    logger.info("Bot 启动...")
    while True:
        try:
            app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)
        except Exception as e:
            logger.error(f"Polling 错误: {traceback.format_exc()}")
            asyncio.sleep(5)

if __name__ == "__main__":
    main()
