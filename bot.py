import random, os, asyncio, logging, traceback, re, time
from collections import defaultdict
from datetime import datetime, timedelta
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, MessageHandler, filters, ContextTypes
from treys import Card, Evaluator

# ---------- 日志 ----------
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger(__name__)

# ---------- 通用配置 ----------
STARTING_CHIPS = 20000
DEFAULT_ADMIN = 5431975432
ADMIN_USER_ID = int(os.environ.get("ADMIN_USER_ID", DEFAULT_ADMIN))

DAILY_RESET_TIME = (0, 0)
RESET_TO_CHIPS = 20000

# ---------- 德州配置 ----------
SMALL_BLIND = 200
BIG_BLIND = 500
TURN_TIMEOUT = 60
FIXED_MIN_RAISE = 100
AUTO_START_TIMEOUT = 60

# ---------- 赛马配置 ----------
HORSE_COUNT = 4
HORSE_NAMES = ["骏马", "战马", "独角兽", "斑马"]
HORSE_EMOJI = ["🐎", "🐴", "🦄", "🦓"]
FIXED_BET_AMOUNTS = [100, 200, 500, 1000]
RACE_AUTO_START = 60           # 开赛倒计时（秒）
RACE_UPDATE_INTERVAL = 10      # 主界面更新间隔（秒）
RACE_ANIMATION_INTERVAL = 1.5  # 动画更新间隔（秒）
RACE_TRACK_LENGTH = 20         # 赛道长度

# ---------- 牌型中英文映射 ----------
HAND_NAME_CN = {
    "High Card": "高牌", "Pair": "一对", "One Pair": "一对", "Two Pair": "两对",
    "Three of a Kind": "三条", "Straight": "顺子", "Flush": "同花", "Full House": "葫芦",
    "Four of a Kind": "四条", "Straight Flush": "同花顺", "Royal Flush": "皇家同花顺",
}

# ---------- 内存存储 ----------
group_chips = defaultdict(lambda: defaultdict(lambda: STARTING_CHIPS))
AUTHORIZED_GROUPS = set()
race_history = defaultdict(list)
race_daily_stats = defaultdict(lambda: [0] * HORSE_COUNT)
horse_profit = defaultdict(lambda: defaultdict(int))
race_jackpot = defaultdict(int)

# ---------- 卡牌美化 ----------
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

# ---------- 边池计算 ----------
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

# ---------- 每日重置筹码 ----------
async def daily_reset_chips():
    while True:
        now = datetime.now()
        target = now.replace(hour=DAILY_RESET_TIME[0], minute=DAILY_RESET_TIME[1], second=0, microsecond=0)
        if target <= now:
            target += timedelta(days=1)
        wait_seconds = (target - now).total_seconds()
        await asyncio.sleep(wait_seconds)
        for chat_id in group_chips:
            for uid in group_chips[chat_id]:
                group_chips[chat_id][uid] = RESET_TO_CHIPS
        for chat_id in race_daily_stats:
            race_daily_stats[chat_id] = [0] * HORSE_COUNT
        logger.info("每日筹码重置完成")

# ==================== 德州扑克（完全不变） ====================
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
        if len(self.players) < 2: return False
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
        if self.chips[uid] == 0: self.all_in.add(uid)

    def current_player(self):
        if not self.active_players or self.actor_idx >= len(self.active_players): return None
        for _ in range(len(self.active_players)):
            uid = self.active_players[self.actor_idx]
            if uid not in self.folded and uid not in self.all_in: return uid
            self.actor_idx = (self.actor_idx + 1) % len(self.active_players)
        return None

    def next_player(self):
        start = self.actor_idx
        while True:
            self.actor_idx = (self.actor_idx + 1) % len(self.active_players)
            if self.actor_idx == start: return None
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
        if uid != self.current_player(): return False, "还没轮到你"
        if uid in self.acted_this_round: return False, "本轮已行动"
        if uid in self.all_in: return False, "已全下，无法行动"

        if action == 'fold':
            self.folded.add(uid)
            self.active_players.remove(uid)
            if self.actor_idx >= len(self.active_players): self.actor_idx = 0
            desc = "弃牌"
        elif action == 'check':
            if self.current_bet > self.round_bets[uid]: return False, "必须跟注或加注"
            self.acted_this_round.add(uid)
            desc = "过牌"
        elif action == 'call':
            call_amt = self.current_bet - self.round_bets[uid]
            actual = min(call_amt, self.chips[uid])
            self.chips[uid] -= actual
            self.round_bets[uid] += actual
            self.pot += actual
            self.total_bet[uid] += actual
            if self.chips[uid] == 0: self.all_in.add(uid)
            self.acted_this_round.add(uid)
            desc = f"跟注 {actual}"
        elif action == 'allin':
            total = self.chips[uid]
            self.chips[uid] = 0
            self.round_bets[uid] += total
            self.pot += total
            self.total_bet[uid] += total
            if total > self.current_bet: self.current_bet = self.round_bets[uid]
            self.all_in.add(uid)
            self.acted_this_round.add(uid)
            desc = f"全下 {total}"
        elif action == 'raise':
            call_amt = self.current_bet - self.round_bets[uid]
            total_raise = call_amt + amount
            if total_raise <= 0 or total_raise > self.chips[uid]: return False, "筹码不足或无效加注额"
            new_total = self.round_bets[uid] + total_raise
            if new_total <= self.current_bet: return False, f"加注后总额必须大于当前下注 {self.current_bet}"
            if new_total - self.current_bet < FIXED_MIN_RAISE: return False, f"最小加注为 {FIXED_MIN_RAISE}"
            self.chips[uid] -= total_raise
            self.round_bets[uid] += total_raise
            self.pot += total_raise
            self.total_bet[uid] += total_raise
            self.current_bet = new_total
            self.acted_this_round = {uid}
            self.last_aggressor = uid
            desc = f"加注 {total_raise}"
        else: return False, "未知操作"

        alive = [p for p in self.active_players if p not in self.folded]
        if len(alive) == 1 or all(p in self.all_in for p in alive):
            self.phase = 'showdown'; return True, desc
        if self.all_acted_or_allin():
            self._end_round(); return True, desc
        self.next_player()
        if self.current_player() is None or self.all_acted_or_allin():
            self._end_round()
        return True, desc

    def _end_round(self):
        for uid in self.round_bets: self.round_bets[uid] = 0
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
            if len(self.board) == 0: self.board.extend([self.deck.pop() for _ in range(3)])
            elif len(self.board) == 3: self.board.append(self.deck.pop())
            elif len(self.board) == 4: self.board.append(self.deck.pop())
            else: break
        alive = [p for p in self.active_players if p not in self.folded]
        if self.last_aggressor and self.last_aggressor in alive: start = self.last_aggressor
        else:
            start = None
            for i in range(1, len(self.players)):
                uid = self.players[(self.dealer_idx + i) % len(self.players)]
                if uid in alive: start = uid; break
            if start is None: start = alive[0]
        idx = alive.index(start)
        self.showdown_order = alive[idx:] + alive[:idx]
        if len(alive) == 1:
            winner = alive[0]
            pot_amount = self.pot
            self.chips[winner] += pot_amount
            self.pot = 0
            self._save_chips()
            return [(winner, "最后赢家", pot_amount, {})]
        scores, hand_types = {}, {}
        for uid in alive:
            hand = self.hands[uid]
            score = self.evaluator.evaluate(hand, self.board) if self.board else self.evaluator.evaluate(hand, [])
            scores[uid] = score
            rank_class = self.evaluator.get_rank_class(score)
            hand_en = self.evaluator.class_to_string(rank_class)
            hand_types[uid] = HAND_NAME_CN.get(hand_en, hand_en)
        best = min(scores.values())
        overall_winners = {uid for uid in alive if scores[uid] == best}
        all_bets = {uid: self.total_bet[uid] for uid in self.players}
        layers = compute_side_pots(all_bets)
        dist = distribute_side_pots(layers, scores)
        for uid in alive: self.chips[uid] += dist[uid]; self.pot -= dist[uid]
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
        for uid in self.chips: group_chips[self.chat_id][uid] = self.chips[uid]

    def cancel_timer(self):
        if self.turn_task: self.turn_task.cancel(); self.turn_task = None

    def cancel_auto_start(self):
        if self.auto_start_task: self.auto_start_task.cancel(); self.auto_start_task = None

# ---------- 德州界面 ----------
async def build_action_view(game, app, uid):
    board_str = " ".join(card_str(c) for c in game.board) if game.board else "无"
    lines = []
    for idx, pid in enumerate(game.players, 1):
        name = await get_name(app, pid)
        s = "弃牌" if pid in game.folded else "全下" if pid in game.all_in else "在局"
        lines.append(f"{idx}. {name} {s} 投入:{game.total_bet.get(pid, 0)}")
    to_call = game.current_bet - game.round_bets.get(uid, 0)
    if to_call < 0: to_call = 0
    return f"公牌: {board_str}\n奖池: {game.pot}  当前下注: {game.current_bet}\n你需跟注: {to_call}\n\n玩家:\n" + "\n".join(lines) + f"\n\n轮到 {await get_name(app, uid)} 行动"

async def build_table_view(game, app):
    lines = []
    for idx, pid in enumerate(game.players, 1):
        name = await get_name(app, pid)
        s = "弃牌" if pid in game.folded else "全下" if pid in game.all_in else "在局"
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
    return f"|- 积分德州牌桌\n\n|- 状态：{phase_cn}\n\n|- 公牌：\n{board_display}\n\n|- 奖池：{game.pot}  当前下注：{game.current_bet}\n\n{cur_text}\n\n|- 玩家：\n\n" + "\n".join(lines) + "\n"

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
        try:
            await app.bot.delete_message(game.chat_id, game.action_msg_id)
        except:
            pass
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
                try:
                    await app.bot.delete_message(game.chat_id, game.action_msg_id)
                except:
                    pass
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
    if to_call == 0: row1.append(InlineKeyboardButton("✅ 过牌", callback_data="texas_check"))
    else: row1.append(InlineKeyboardButton(f"✅ 跟注 {to_call}", callback_data="texas_call"))
    btns = [[InlineKeyboardButton("🂠 查看手牌", callback_data="texas_hand")], row1]
    if game.chips[uid] > 0:
        raise_extra = FIXED_MIN_RAISE
        total_need = to_call + raise_extra
        if game.chips[uid] >= total_need:
            btns.append([InlineKeyboardButton(f"🔼 加注 {raise_extra}", callback_data=f"texas_raise_{raise_extra}")])
        btns.append([InlineKeyboardButton(f"🔥 全下 {game.chips[uid]}", callback_data="texas_allin")])
    return InlineKeyboardMarkup(btns)

async def settle_game(game, app):
    game.cancel_timer()
    game.cancel_auto_start()
    if game.action_msg_id:
        try:
            await app.bot.delete_message(game.chat_id, game.action_msg_id)
        except:
            pass
    if game.game_msg_id:
        try:
            await app.bot.delete_message(game.chat_id, game.game_msg_id)
        except:
            pass
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

# ==================== 赛马（修复异步调用，增加倒计时提醒、动画独立消息） ====================
class HorseRace:
    def __init__(self, chat_id, owner_id, initial_pool=0):
        self.chat_id = chat_id
        self.owner_id = owner_id
        self.bets = {}
        self.total_bets = [0] * HORSE_COUNT
        self.pool = initial_pool
        self.phase = 'betting'
        self.game_msg_id = None          # 下注界面消息ID
        self.animation_msg_id = None     # 动画消息ID（比赛开始后新发）
        self.create_time = time.time()
        self.update_task = None
        self.countdown_task = None
        self.animation_task = None
        self.positions = [0] * HORSE_COUNT
        self.arrival_order = []
        self.app = None
        self.fixed_rates = self._generate_rates()
        self._sent_30 = False
        self._sent_20 = False
        self._sent_10 = False

    def _generate_rates(self):
        weights = [random.randint(1, 100) for _ in range(HORSE_COUNT)]
        total = sum(weights)
        return [w / total for w in weights]

    def set_app(self, app):
        self.app = app

    def place_bet(self, user_id, horse_idx, amount):
        if self.phase != 'betting':
            return False, "当前不是下注阶段"
        if horse_idx < 0 or horse_idx >= HORSE_COUNT:
            return False, "无效的马号"
        if user_id not in group_chips[self.chat_id]:
            group_chips[self.chat_id][user_id] = STARTING_CHIPS
        chips = group_chips[self.chat_id][user_id]
        if amount <= 0 or amount > chips:
            return False, f"筹码不足或无效金额（余额:{chips}）"
        group_chips[self.chat_id][user_id] -= amount
        if user_id not in self.bets:
            self.bets[user_id] = {}
        self.bets[user_id][horse_idx] = self.bets[user_id].get(horse_idx, 0) + amount
        self.total_bets[horse_idx] += amount
        self.pool += amount
        return True, f"成功下注 {amount} 筹码于 {HORSE_EMOJI[horse_idx]} {HORSE_NAMES[horse_idx]}"

    def get_odds(self):
        """赔率 = (1/固定胜率) * (总奖池/该马下注额)"""
        odds = []
        for i in range(HORSE_COUNT):
            rate = self.fixed_rates[i] if self.fixed_rates[i] > 0 else 0.01
            if self.total_bets[i] > 0:
                base_odds = 1.0 / rate
                market_factor = self.pool / self.total_bets[i]
                odds.append(base_odds * market_factor)
            else:
                odds.append(float('inf'))
        return odds

    async def start_race(self):   # 修复：改为异步方法，直接 await
        if self.phase != 'betting':
            return False
        self.phase = 'racing'
        self.winner = -1
        self.positions = [0] * HORSE_COUNT
        self.arrival_order = []
        # 取消倒计时和界面刷新任务
        if self.update_task:
            self.update_task.cancel()
            self.update_task = None
        if self.countdown_task:
            self.countdown_task.cancel()
            self.countdown_task = None
        # 发送动画消息（使用 await）
        if self.app:
            await self.app.bot.send_message(self.chat_id, "🏇 比赛开始！正在奔跑中……")
            msg = await self.app.bot.send_message(self.chat_id, "加载中...")
            self.animation_msg_id = msg.message_id
        self.animation_task = asyncio.create_task(self._run_animation())
        return True

    async def _run_animation(self):
        if not self.app or not self.animation_msg_id:
            return
        while self.phase == 'racing':
            for i in range(HORSE_COUNT):
                if self.positions[i] < RACE_TRACK_LENGTH:
                    step = random.randint(1, 3)
                    self.positions[i] = min(RACE_TRACK_LENGTH, self.positions[i] + step)
                    if self.positions[i] >= RACE_TRACK_LENGTH and i not in self.arrival_order:
                        self.arrival_order.append(i)
            try:
                text = self._build_animation_view()
                await self.app.bot.edit_message_text(
                    chat_id=self.chat_id,
                    message_id=self.animation_msg_id,
                    text=text
                )
            except Exception:
                pass
            if len(self.arrival_order) == HORSE_COUNT:
                self.winner = self.arrival_order[0]
                race_daily_stats[self.chat_id][self.winner] += 1
                history = race_history[self.chat_id]
                history.append(self.winner)
                if len(history) > 10:
                    race_history[self.chat_id] = history[-10:]
                self.phase = 'finished'
                asyncio.create_task(settle_race(self, self.app, self.chat_id))
                return
            await asyncio.sleep(RACE_ANIMATION_INTERVAL)

    def _build_animation_view(self):
        race_id = datetime.fromtimestamp(self.create_time).strftime("%Y%m%d-%H%M")
        lines = [f"🏇 {race_id} 实况", "━" * 20]
        for i in range(HORSE_COUNT):
            pos = self.positions[i]
            if pos < RACE_TRACK_LENGTH:
                track = '━' * pos + HORSE_EMOJI[i] + '━' * (RACE_TRACK_LENGTH - pos - 1) + '🏁'
            else:
                track = '━' * RACE_TRACK_LENGTH + HORSE_EMOJI[i] + '🏁'
            lines.append(track)
        lines.append("━" * 20)
        if self.arrival_order:
            arrived = [f"{HORSE_EMOJI[i]}{HORSE_NAMES[i]}" for i in self.arrival_order]
            lines.append("✅ 已到达: " + " ".join(arrived))
        return "\n".join(lines)

    def payout(self):
        if self.phase != 'finished':
            return None
        total_win_bets = self.total_bets[self.winner]
        pool = self.pool
        if total_win_bets == 0:
            return {
                'winner': self.winner,
                'winner_name': HORSE_NAMES[self.winner],
                'total_pool': pool,
                'win_bets': 0,
                'payouts': [],
                'refund': True
            }
        payouts = []
        for uid, bets_per_user in self.bets.items():
            if self.winner in bets_per_user:
                user_win_bet = bets_per_user[self.winner]
                share = pool * (user_win_bet / total_win_bets)
                group_chips[self.chat_id][uid] += int(share)
                payouts.append((uid, int(share), user_win_bet))
        return {
            'winner': self.winner,
            'winner_name': HORSE_NAMES[self.winner],
            'total_pool': pool,
            'win_bets': total_win_bets,
            'payouts': payouts,
            'refund': False
        }

    def cancel_tasks(self):
        if self.update_task:
            self.update_task.cancel()
            self.update_task = None
        if self.countdown_task:
            self.countdown_task.cancel()
            self.countdown_task = None
        if self.animation_task:
            self.animation_task.cancel()
            self.animation_task = None

# ---------- 赛马界面 ----------
def build_race_view(race):
    now = time.time()
    elapsed = now - race.create_time
    remaining = max(0, RACE_AUTO_START - elapsed)
    minutes = int(remaining // 60)
    seconds = int(remaining % 60)
    race_id = datetime.fromtimestamp(race.create_time).strftime("%Y%m%d-%H%M")
    odds = race.get_odds()
    history = race_history.get(race.chat_id, [])[-10:]
    daily_stats = race_daily_stats[race.chat_id]
    total_wins = sum(daily_stats) or 1

    lines = [f"🏇 赛马大赛 {race_id} 🏇", "━" * 20]
    for emoji in HORSE_EMOJI:
        lines.append(f"{emoji}{'━' * (RACE_TRACK_LENGTH - 1)}🏁")
    lines.append("━" * 20)

    jackpot = race_jackpot.get(race.chat_id, 0)
    lines.append(f"💰 本期总奖池：{race.pool} 积分 (含累积彩池 {jackpot})")

    if history:
        lines.append(f"📊 路书\n最近10场: {''.join([HORSE_EMOJI[i] for i in history])}")

    hist_lines = []
    for i in range(HORSE_COUNT):
        wins = daily_stats[i]
        rate = (wins / total_wins * 100) if total_wins > 0 else 0
        hist_lines.append(f"  {HORSE_EMOJI[i]} {wins}胜 | {rate:.0f}%")
    lines.append("📜 历史胜率:\n" + "\n".join(hist_lines))

    lines.append("📊 综合数据 (下注 | 胜率 | 实时赔率):")
    for i in range(HORSE_COUNT):
        bet = race.total_bets[i]
        fixed_rate = race.fixed_rates[i] * 100
        odd = odds[i]
        odd_str = f"{odd:.2f}x" if odd != float('inf') else "∞"
        lines.append(f"{HORSE_EMOJI[i]} {HORSE_NAMES[i]}: 下注 {bet} | 胜率 {fixed_rate:.0f}% | 赔率 {odd_str}")

    if race.phase == 'betting':
        if remaining > 0:
            lines.append(f"\n⏰ 距离开赛还有 {minutes} 分 {seconds} 秒")
        else:
            lines.append("\n⏰ 即将开赛...")
        lines.append("🔒 开赛后无法投注")
    return "\n".join(lines)

def get_race_buttons():
    btns = []
    for amt in FIXED_BET_AMOUNTS:
        row = []
        for i in range(HORSE_COUNT):
            row.append(InlineKeyboardButton(f"{HORSE_EMOJI[i]} {amt}", callback_data=f"horsebet_{i}_{amt}"))
        btns.append(row)
    btns.append([InlineKeyboardButton("🏁 开始比赛", callback_data="horse_start")])
    return InlineKeyboardMarkup(btns)

# ---------- 赛马后台任务 ----------
async def start_race_tasks(race, app):
    race.cancel_tasks()
    race.set_app(app)
    race._sent_30 = False
    race._sent_20 = False
    race._sent_10 = False

    # 界面刷新任务（每10秒）
    async def update_loop():
        while race.phase == 'betting':
            view = build_race_view(race)
            try:
                await app.bot.edit_message_text(
                    chat_id=race.chat_id,
                    message_id=race.game_msg_id,
                    text=view,
                    reply_markup=get_race_buttons()
                )
            except Exception:
                pass
            await asyncio.sleep(RACE_UPDATE_INTERVAL)

    # 倒计时轮询任务（每秒检查）
    async def countdown_loop():
        logger.info(f"赛马倒计时任务启动，chat_id={race.chat_id}")
        while race.phase == 'betting':
            now = time.time()
            elapsed = now - race.create_time
            remaining = RACE_AUTO_START - elapsed

            if remaining <= 0:
                if race.phase == 'betting':
                    await app.bot.send_message(race.chat_id, "⏰ 倒计时结束，比赛自动开始！")
                    await race.start_race()  # 修复：使用 await
                break

            if remaining <= 30 and not race._sent_30:
                await app.bot.send_message(race.chat_id, "⏰ 赛马即将在 30 秒后开始，开赛后无法押注！")
                race._sent_30 = True
            if remaining <= 20 and not race._sent_20:
                await app.bot.send_message(race.chat_id, "⏰ 赛马即将在 20 秒后开始，开赛后无法押注！")
                race._sent_20 = True
            if remaining <= 10 and not race._sent_10:
                await app.bot.send_message(race.chat_id, "⏰ 赛马即将在 10 秒后开始，开赛后无法押注！")
                race._sent_10 = True

            await asyncio.sleep(1)

    race.update_task = asyncio.create_task(update_loop())
    race.countdown_task = asyncio.create_task(countdown_loop())

# ---------- 赛马结算 ----------
async def settle_race(race, app, chat_id):
    race.cancel_tasks()
    # 删除动画消息
    if race.animation_msg_id:
        try:
            await app.bot.delete_message(chat_id, race.animation_msg_id)
        except Exception:
            pass
    result = race.payout()
    if not result:
        return
    race_id = datetime.fromtimestamp(race.create_time).strftime("%Y%m%d-%H%M")
    lines = [f"🏆 赛马大赛 {race_id} 结果 🏆", "━" * 20]
    order = race.arrival_order if race.arrival_order else sorted(range(HORSE_COUNT), key=lambda i: race.total_bets[i], reverse=True)
    medals = ["🥇", "🥈", "🥉"]
    for idx, horse_idx in enumerate(order):
        if idx < 3:
            lines.append(f"{medals[idx]} {HORSE_EMOJI[horse_idx]} {HORSE_NAMES[horse_idx]}")
        else:
            lines.append(f"{idx+1}️⃣ {HORSE_EMOJI[horse_idx]} {HORSE_NAMES[horse_idx]}")
    lines.append("")

    if result['refund']:
        pool_to_roll = result['total_pool']
        race_jackpot[chat_id] += pool_to_roll
        lines.append(f"🔄 无人押中，所有下注 ({pool_to_roll} 积分) 已滚入下一期彩池！")
    else:
        lines.append("💰 获胜玩家:")
        for uid, share, bet in result['payouts']:
            name = await get_name(app, uid)
            profit = share - bet
            lines.append(f"{name}: 投注{bet} → 获得{share} (+{profit})")
            horse_profit[chat_id][uid] += profit

    if horse_profit[chat_id]:
        sorted_rank = sorted(horse_profit[chat_id].items(), key=lambda x: x[1], reverse=True)
        total_profit = sum(v for v in horse_profit[chat_id].values())
        lines.append("\n🏆 赛马大赛排行榜 🏆")
        lines.append("━" * 20)
        for idx, (uid, profit) in enumerate(sorted_rank[:10], 1):
            name = await get_name(app, uid)
            percentage = (profit / total_profit * 100) if total_profit > 0 else 0
            if idx == 1:
                lines.append(f"🥇 {name}: +{profit} 积分 ({percentage:.2f}%)")
            elif idx == 2:
                lines.append(f"🥈 {name}: +{profit} 积分 ({percentage:.2f}%)")
            elif idx == 3:
                lines.append(f"🥉 {name}: +{profit} 积分 ({percentage:.2f}%)")
            else:
                lines.append(f"{idx}. {name}: +{profit} 积分 ({percentage:.2f}%)")

    await app.bot.send_message(chat_id, "\n".join(lines))
    # 删除下注消息
    if race.game_msg_id:
        try:
            await app.bot.delete_message(chat_id, race.game_msg_id)
        except Exception:
            pass
    active_games.pop(chat_id, None)

# ---------- 全局游戏管理 ----------
active_games = {}

def is_auth(chat_id): return chat_id in AUTHORIZED_GROUPS
async def need_auth(update, context):
    if not is_auth(update.effective_chat.id):
        await update.effective_message.reply_text("❌ 此群组未授权，请联系管理员。")
        return False
    return True

def has_active_game(chat_id):
    game = active_games.get(chat_id)
    if game is None:
        return False
    if isinstance(game, PokerGame) and game.phase not in ('waiting', 'showdown'):
        return True
    if isinstance(game, HorseRace) and game.phase not in ('waiting', 'finished'):
        return True
    return False

# ---------- 命令 ----------
async def cmd_start(update, context):
    await update.message.reply_text("使用 /DZ 开始德州扑克，/SM 开始赛马")

async def cmd_dz(update, context):
    if not await need_auth(update, context): return
    chat_id = update.effective_chat.id
    if has_active_game(chat_id):
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
        f"🃏 新一局德州扑克！\n发起人: {await get_name(context.application, update.effective_user.id)}\n\n已加入玩家:\n" + "\n".join(plist) + "\n\n点击按钮加入或开始",
        reply_markup=InlineKeyboardMarkup(kb)
    )
    game.game_msg_id = msg.message_id

async def cmd_sm(update, context):
    if not await need_auth(update, context): return
    chat_id = update.effective_chat.id
    if has_active_game(chat_id):
        await update.message.reply_text("当前已有进行中的游戏，请等待结束。")
        return
    jackpot = race_jackpot.get(chat_id, 0)
    race = HorseRace(chat_id, update.effective_user.id, initial_pool=jackpot)
    if jackpot > 0:
        race_jackpot[chat_id] = 0
    active_games[chat_id] = race
    view = build_race_view(race)
    msg = await update.message.reply_text(view, reply_markup=get_race_buttons())
    race.game_msg_id = msg.message_id
    start_race_tasks(race, context.application)

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
    elif isinstance(game, HorseRace):
        game.cancel_tasks()
    await update.message.reply_text("游戏已被手动终止。")
    try:
        await context.bot.delete_message(chat_id, game.game_msg_id)
    except Exception:
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
                if e.type == 'text_mention':
                    target = e.user.id
                elif e.type == 'mention':
                    try:
                        target = (await context.bot.get_chat(a1.lstrip('@'))).id
                    except:
                        pass
        if not target:
            try:
                target = int(a1)
            except:
                pass
        try:
            amt = int(context.args[1])
        except:
            pass
    elif context.args and len(context.args) == 1:
        try:
            amt = int(context.args[0])
        except:
            pass
        if update.message.reply_to_message:
            target = update.message.reply_to_message.from_user.id
    if not target or amt <= 0:
        await update.message.reply_text("用法: /add @用户名 数量")
        return
    group_chips[chat_id][target] = group_chips[chat_id].get(target, STARTING_CHIPS) + amt
    await update.message.reply_text(f"✅ 已给 {await get_name(context.application, target)} 增加 {amt} 筹码，当前: {group_chips[chat_id][target]}")

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
        await update.message.reply_text("用法: /shouquan 群组ID")
        return
    AUTHORIZED_GROUPS.add(cid)
    await update.message.reply_text(f"✅ 群组 {cid} 已授权")

async def cmd_qxshouquan(update, context):
    if update.effective_user.id != ADMIN_USER_ID:
        await update.message.reply_text("❌ 仅管理员可用")
        return
    cid = update.effective_chat.id if update.effective_chat.type != "private" else int(context.args[0]) if context.args else None
    if not cid:
        await update.message.reply_text("用法: /qxshouquan 群组ID")
        return
    AUTHORIZED_GROUPS.discard(cid)
    await update.message.reply_text(f"✅ 群组 {cid} 已取消授权")

# ---------- 按钮回调 ----------
async def on_button(update, context):
    q = update.callback_query
    data = q.data
    chat_id = q.message.chat.id
    if not is_auth(chat_id):
        await q.answer("未授权", show_alert=True)
        return
    game = active_games.get(chat_id)
    if not game:
        await q.edit_message_text("游戏不存在")
        return

    if isinstance(game, HorseRace):
        await horse_button(update, context, game, q, data)
    else:
        await poker_button(update, context, game, q, data)

async def poker_button(update, context, game, q, data):
    if game.phase == 'showdown':
        await settle_game(game, context.application)
        active_games.pop(game.chat_id, None)
        return
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
                await q.edit_message_text(
                    "已加入玩家:\n" + "\n".join(plist) + "\n\n点击按钮加入或开始",
                    reply_markup=InlineKeyboardMarkup(kb)
                )
                if len(game.players) >= 2:
                    await start_auto_start(game, context.application)
            else:
                await q.answer("加入失败", show_alert=True)
        elif data == 'texas_start':
            if user.id != game.owner_id:
                await q.answer("只有发起人可以开始", show_alert=True)
                return
            if len(game.players) < 2:
                await q.answer("至少需要2人", show_alert=True)
                return
            if any(game.chips[u] <= 0 for u in game.players):
                await q.answer("有玩家筹码不足", show_alert=True)
                return
            if game.start_game():
                await update_table_msg(game, context.application)
                await start_turn_timer(game, context.application)
            else:
                await q.edit_message_text("开始失败")
        return
    if game.phase in ('preflop','flop','turn','river'):
        if user.id != game.current_player():
            await q.answer("还没轮到你", show_alert=True)
            return
        if data == 'texas_fold':
            ok, desc = game.handle_action(user.id, 'fold')
        elif data == 'texas_check':
            ok, desc = game.handle_action(user.id, 'check')
        elif data == 'texas_call':
            ok, desc = game.handle_action(user.id, 'call')
        elif data == 'texas_allin':
            ok, desc = game.handle_action(user.id, 'allin')
        elif data.startswith('texas_raise_'):
            try:
                amt = int(data.split('_')[2])
                ok, desc = game.handle_action(user.id, 'raise', amount=amt)
            except:
                await q.answer("无效加注额", show_alert=True)
                return
        else:
            return
        if not ok:
            await q.answer(desc, show_alert=True)
            return
        if game.action_msg_id:
            try:
                await context.bot.delete_message(game.chat_id, game.action_msg_id)
            except:
                pass
        await action_notify(game.chat_id, context.application, user.id, desc)
        if game.phase == 'showdown':
            await settle_game(game, context.application)
            active_games.pop(game.chat_id, None)
            return
        await update_table_msg(game, context.application)
        await start_turn_timer(game, context.application)

async def horse_button(update, context, race, q, data):
    await q.answer()
    user = q.from_user
    if race.phase != 'betting':
        await q.answer("当前不是下注阶段", show_alert=True)
        return
    if data.startswith('horsebet_'):
        _, horse_idx_str, amt_str = data.split('_')
        horse_idx = int(horse_idx_str)
        amt = int(amt_str)
        ok, msg = race.place_bet(user.id, horse_idx, amt)
        if not ok:
            await q.answer(msg, show_alert=True)
            return
        view = build_race_view(race)
        await q.edit_message_text(view, reply_markup=get_race_buttons())
        await action_notify(race.chat_id, context.application, user.id, f"下注 {amt} 于 {HORSE_EMOJI[horse_idx]} {HORSE_NAMES[horse_idx]}")
    elif data == 'horse_start':
        if user.id != race.owner_id:
            await q.answer("只有发起人可以开始比赛", show_alert=True)
            return
        race.set_app(context.application)
        if await race.start_race():  # 修复：await
            await q.answer("比赛开始！", show_alert=False)
        else:
            await q.answer("比赛无法开始", show_alert=True)

# ---------- 文字命令 ----------
async def on_text(update, context):
    msg = update.effective_message
    if not msg or not msg.text:
        return
    user = update.effective_user
    if user.is_bot:
        return
    chat_id = update.effective_chat.id
    game = active_games.get(chat_id)

    if isinstance(game, HorseRace) and game.phase == 'betting':
        m = re.match(r'^下注\s+(\d+)\s+(\d+)$', msg.text.strip())
        if not m:
            if msg.reply_to_message and msg.reply_to_message.message_id == game.game_msg_id:
                m = re.match(r'^下注\s+(\d+)\s+(\d+)$', msg.text.strip())
            if not m:
                return
        horse_idx = int(m.group(1)) - 1
        amt = int(m.group(2))
        ok, desc = game.place_bet(user.id, horse_idx, amt)
        if not ok:
            await msg.reply_text(f"❌ {desc}")
            return
        await action_notify(chat_id, context.application, user.id, f"下注 {amt} 于 {HORSE_EMOJI[horse_idx]} {HORSE_NAMES[horse_idx]}")
        return

    if isinstance(game, PokerGame) and game.phase in ('preflop','flop','turn','river'):
        if user.id != game.current_player():
            return
        m = re.match(r'^加注\s*(\d+)$', msg.text.strip())
        if not m:
            if msg.reply_to_message and msg.reply_to_message.message_id == game.game_msg_id:
                m = re.match(r'^加注\s*(\d+)$', msg.text.strip())
            if not m:
                return
        amt = int(m.group(1))
        ok, desc = game.handle_action(user.id, 'raise', amount=amt)
        if not ok:
            await msg.reply_text(f"❌ {desc}")
            return
        if game.action_msg_id:
            try:
                await context.bot.delete_message(chat_id, game.action_msg_id)
            except:
                pass
        await action_notify(chat_id, context.application, user.id, desc)
        if game.phase == 'showdown':
            await settle_game(game, context.application)
            active_games.pop(chat_id, None)
            return
        await update_table_msg(game, context.application)
        await start_turn_timer(game, context.application)

# ---------- 主函数 ----------
def main():
    TOKEN = os.environ.get("BOT_TOKEN")
    if not TOKEN:
        logger.error("未设置 BOT_TOKEN")
        return
    app = Application.builder().token(TOKEN).build()
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("dz", cmd_dz))
    app.add_handler(CommandHandler("sm", cmd_sm))
    app.add_handler(CommandHandler("end", cmd_end))
    app.add_handler(CommandHandler("add", cmd_add))
    app.add_handler(CommandHandler("ph", cmd_ph))
    app.add_handler(CommandHandler("shouquan", cmd_shouquan))
    app.add_handler(CommandHandler("qxshouquan", cmd_qxshouquan))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.add_handler(CallbackQueryHandler(on_button))

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
