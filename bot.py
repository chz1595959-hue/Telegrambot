import random, os, asyncio, logging, traceback, re
from collections import defaultdict
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, MessageHandler, filters, ContextTypes
from treys import Card, Evaluator
import asyncpg

# ---------- 日志 ----------
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger(__name__)

# ---------- 配置 ----------
STARTING_CHIPS = 10000
SMALL_BLIND = 100
BIG_BLIND = 200
TURN_TIMEOUT = 60
DEFAULT_ADMIN = 5431975432
ADMIN_USER_ID = int(os.environ.get("ADMIN_USER_ID", DEFAULT_ADMIN))

ZJH_ANTE = 100
ZJH_MIN_RAISE = 100
ZJH_SEEN_MULTIPLIER = 2

# ---------- 数据库 ----------
db_pool = None

async def init_db():
    global db_pool
    DATABASE_URL = os.environ.get("DATABASE_URL")
    if not DATABASE_URL:
        logger.warning("DATABASE_URL 未设置")
        return
    try:
        db_pool = await asyncpg.create_pool(DATABASE_URL, min_size=1, max_size=5)
        async with db_pool.acquire() as conn:
            await conn.execute('''
                CREATE TABLE IF NOT EXISTS chips (
                    chat_id BIGINT, user_id BIGINT, chips INT DEFAULT 0,
                    PRIMARY KEY (chat_id, user_id)
                );
            ''')
            await conn.execute('''
                CREATE TABLE IF NOT EXISTS auth (
                    chat_id BIGINT PRIMARY KEY
                );
            ''')
            await conn.execute('''
                CREATE TABLE IF NOT EXISTS history (
                    id SERIAL PRIMARY KEY,
                    chat_id BIGINT, user_id BIGINT,
                    game_time TIMESTAMP DEFAULT NOW(),
                    game_type TEXT,
                    net_profit INT, final_chips INT
                );
            ''')
        logger.info("数据库初始化成功")
    except Exception as e:
        logger.error(f"数据库连接失败: {e}")
        db_pool = None

async def load_chips(chat_id):
    if not db_pool: return {}
    async with db_pool.acquire() as conn:
        rows = await conn.fetch("SELECT user_id, chips FROM chips WHERE chat_id=$1", chat_id)
        return {r['user_id']: r['chips'] for r in rows}

async def save_chips(chat_id, chips_dict):
    if not db_pool: return
    async with db_pool.acquire() as conn:
        for uid, chips in chips_dict.items():
            await conn.execute('''
                INSERT INTO chips (chat_id, user_id, chips) VALUES ($1,$2,$3)
                ON CONFLICT (chat_id, user_id) DO UPDATE SET chips=$3
            ''', chat_id, uid, chips)

async def load_auth():
    if not db_pool: return set()
    async with db_pool.acquire() as conn:
        rows = await conn.fetch("SELECT chat_id FROM auth")
        return {r['chat_id'] for r in rows}

async def save_auth(chat_id):
    if not db_pool: return
    async with db_pool.acquire() as conn:
        await conn.execute("INSERT INTO auth (chat_id) VALUES ($1) ON CONFLICT DO NOTHING", chat_id)

async def delete_auth(chat_id):
    if not db_pool: return
    async with db_pool.acquire() as conn:
        await conn.execute("DELETE FROM auth WHERE chat_id=$1", chat_id)

async def save_history(chat_id, user_id, net_profit, final_chips, game_type):
    if not db_pool: return
    async with db_pool.acquire() as conn:
        await conn.execute('''
            INSERT INTO history (chat_id, user_id, net_profit, final_chips, game_type)
            VALUES ($1,$2,$3,$4,$5)
        ''', chat_id, user_id, net_profit, final_chips, game_type)

# ---------- 卡牌美化 ----------
def card_str(card_int):
    raw = Card.int_to_pretty_str(card_int)
    suit_map = {'♠': '♠️', '♥': '♥️', '♦': '♦️', '♣': '♣️'}
    rank = raw[:-1].replace('T', '10')
    suit = raw[-1]
    return f"{rank}{suit_map.get(suit, suit)}"

async def get_name(app, user_id):
    try:
        chat = await app.bot.get_chat(user_id)
        return chat.first_name or str(user_id)
    except:
        return str(user_id)

# ---------- 边池计算 ----------
def compute_side_pots(players_total_bet):
    if not players_total_bet: return []
    sorted_bets = sorted(players_total_bet.items(), key=lambda x: x[1])
    layers = []
    prev = 0
    for uid, bet in sorted_bets:
        if bet > prev:
            layer_contribution = bet - prev
            eligible = [u for u, b in sorted_bets if b >= bet]
            layers.append({'amount': layer_contribution * len(eligible), 'eligible': eligible})
            prev = bet
    return layers

def distribute_side_pots(side_pots, scores, winners_set):
    distribution = {uid: 0 for uid in scores}
    for layer in side_pots:
        eligible_scores = {uid: scores[uid] for uid in layer['eligible'] if uid in scores}
        if not eligible_scores: continue
        best_score = min(eligible_scores.values())
        layer_winners = [uid for uid, s in eligible_scores.items() if s == best_score]
        share = layer['amount'] // len(layer_winners)
        rem = layer['amount'] % len(layer_winners)
        for uid in layer_winners:
            distribution[uid] += share
        if rem:
            distribution[layer_winners[0]] += rem
    return distribution

# ---------- 德州游戏类 ----------
class TexasGame:
    def __init__(self, chat_id, owner_id, chips_dict):
        self.chat_id = chat_id
        self.owner_id = owner_id
        self.players = []
        self.chips = {}
        self.chips_dict = chips_dict
        self.starting_chips_snapshot = {}
        self.total_bet = {}
        self.hands = {}
        self.folded = set()
        self.all_in = set()
        self.deck = []
        self.board = []
        self.pot = 0
        self.phase = 'waiting'
        self.players_in_hand = []
        self.actor_idx = 0
        self.current_bet = 0
        self.round_bets = {}
        self.min_raise = BIG_BLIND
        self.acted_this_round = set()
        self.last_aggressor = None
        self.dealer_idx = 0
        self.game_msg_id = None
        self.evaluator = Evaluator()
        self.turn_task = None
        self.hand_revealed = set()

    def add_player(self, user_id):
        if user_id not in self.players and self.phase == 'waiting':
            if user_id not in self.chips_dict:
                self.chips_dict[user_id] = STARTING_CHIPS
            self.chips[user_id] = self.chips_dict[user_id]
            self.total_bet[user_id] = 0
            self.players.append(user_id)
            return True
        return False

    def start_game(self):
        if len(self.players) < 2:
            return False
        for uid in self.players:
            self.chips[uid] = self.chips_dict.get(uid, STARTING_CHIPS)
            self.total_bet[uid] = 0
        self.starting_chips_snapshot = self.chips.copy()
        self.phase = 'preflop'
        self.deck = [Card.new(r + s) for r in "23456789TJQKA" for s in "shdc"]
        random.shuffle(self.deck)
        for uid in self.players:
            self.hands[uid] = [self.deck.pop(), self.deck.pop()]
            self.round_bets[uid] = 0
        self.dealer_idx = len(self.players) - 1
        sb_idx = (self.dealer_idx + 1) % len(self.players)
        bb_idx = (self.dealer_idx + 2) % len(self.players)
        sb = self.players[sb_idx]
        bb = self.players[bb_idx]
        self._post_blind(sb, SMALL_BLIND)
        self._post_blind(bb, BIG_BLIND)
        self.current_bet = BIG_BLIND
        self.players_in_hand = self.players.copy()
        self.actor_idx = (bb_idx + 1) % len(self.players)
        self.acted_this_round = set()
        return True

    def _update_total_bet(self, uid, amount):
        self.total_bet[uid] += amount

    def _post_blind(self, uid, amount):
        actual = min(amount, self.chips[uid])
        self.chips[uid] -= actual
        self.round_bets[uid] += actual
        self.pot += actual
        self._update_total_bet(uid, actual)
        if self.chips[uid] == 0:
            self.all_in.add(uid)

    def get_buttons(self, uid):
        buttons = []
        if uid in self.hands and uid not in self.folded and self.phase != 'showdown':
            if uid in self.hand_revealed:
                buttons.append([InlineKeyboardButton("✅ 已查看手牌", callback_data="texas_hand")])
            else:
                buttons.append([InlineKeyboardButton("🂠 查看手牌", callback_data="texas_hand")])

        if uid not in self.players_in_hand or uid in self.folded or uid in self.all_in or uid != self.current_player_id():
            return InlineKeyboardMarkup(buttons)

        to_call = self.current_bet - self.round_bets[uid]
        if to_call < 0: to_call = 0
        buttons.append([InlineKeyboardButton("❌ 弃牌", callback_data="texas_fold")])
        if to_call == 0:
            buttons.append([InlineKeyboardButton("✅ 过牌", callback_data="texas_check")])
        else:
            buttons.append([InlineKeyboardButton(f"✅ 跟注 {to_call}", callback_data="texas_call")])
        if self.chips[uid] > to_call:
            min_raise_total = self.current_bet + self.min_raise
            min_raise_needed = min_raise_total - self.round_bets[uid]
            if self.chips[uid] >= min_raise_needed:
                buttons.append([InlineKeyboardButton(f"🔼 加注至 {min_raise_total} (最小)", callback_data=f"texas_raise_{min_raise_needed}")])
            half_pot = (self.pot + to_call) // 2 + to_call
            if self.chips[uid] >= half_pot and half_pot > to_call:
                buttons.append([InlineKeyboardButton(f"🔼 加注至 {half_pot} (半池)", callback_data=f"texas_raise_{half_pot}")])
            full_pot = self.pot + to_call * 2
            if self.chips[uid] >= full_pot and full_pot > to_call:
                buttons.append([InlineKeyboardButton(f"🔼 加注至 {full_pot} (满池)", callback_data=f"texas_raise_{full_pot}")])
            all_in_amount = self.chips[uid]
            if all_in_amount > to_call:
                buttons.append([InlineKeyboardButton(f"🔥 全下 {all_in_amount}", callback_data=f"texas_raise_{all_in_amount}")])
            # 自定义加注提示
            buttons.append([InlineKeyboardButton("✏️ 自定义加注", callback_data="texas_custom_raise")])
        return InlineKeyboardMarkup(buttons)

    def current_player_id(self):
        if not self.players_in_hand or self.actor_idx >= len(self.players_in_hand):
            return None
        return self.players_in_hand[self.actor_idx]

    def next_player(self):
        start = self.actor_idx
        while True:
            self.actor_idx = (self.actor_idx + 1) % len(self.players_in_hand)
            if self.actor_idx == start:
                return None
            uid = self.players_in_hand[self.actor_idx]
            if uid not in self.folded and uid not in self.all_in and uid not in self.acted_this_round:
                return uid
        return None

    def all_players_acted_or_allin(self):
        for uid in self.players_in_hand:
            if uid not in self.folded and uid not in self.all_in and uid not in self.acted_this_round:
                return False
        return True

    def handle_action(self, uid, action, amount=None):
        if uid != self.current_player_id():
            return False, "not your turn"
        if uid in self.acted_this_round:
            return False, "already acted this round"

        if action == 'fold':
            self.folded.add(uid)
            self.players_in_hand.remove(uid)
            if self.actor_idx >= len(self.players_in_hand):
                self.actor_idx = 0
        elif action == 'check':
            if self.current_bet > self.round_bets[uid]:
                return False, "must call or raise"
            self.acted_this_round.add(uid)
        elif action == 'call':
            call_amount = self.current_bet - self.round_bets[uid]
            actual = min(call_amount, self.chips[uid])
            self.chips[uid] -= actual
            self.round_bets[uid] += actual
            self.pot += actual
            self._update_total_bet(uid, actual)
            if self.chips[uid] == 0:
                self.all_in.add(uid)
            self.acted_this_round.add(uid)
        elif action == 'raise':
            needed = amount
            if needed <= 0 or self.chips[uid] < needed:
                return False, "invalid raise amount"
            new_total = self.round_bets[uid] + needed
            if new_total <= self.current_bet:
                return False, f"raise must be > current bet ({self.current_bet})"
            if new_total - self.current_bet < self.min_raise:
                return False, f"min raise is {self.min_raise}"
            self.chips[uid] -= needed
            self.round_bets[uid] += needed
            self.pot += needed
            self._update_total_bet(uid, needed)
            self.current_bet = new_total
            self.min_raise = new_total - (self.current_bet - self.min_raise)
            if self.chips[uid] == 0:
                self.all_in.add(uid)
            self.acted_this_round = {uid}
            self.last_aggressor = uid
        else:
            return False, "unknown action"

        alive = [p for p in self.players_in_hand if p not in self.folded]
        if len(alive) == 1:
            self.phase = 'showdown'
            return True, None

        if self.all_players_acted_or_allin():
            self._end_round()
            return True, None

        self.next_player()
        if self.current_player_id() is None or self.all_players_acted_or_allin():
            self._end_round()
        return True, None

    def _end_round(self):
        for uid in self.round_bets:
            self.round_bets[uid] = 0
        self.current_bet = 0
        self.min_raise = BIG_BLIND
        self.acted_this_round.clear()
        self.last_aggressor = None

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
            test_uid = self.players[(start_idx + i) % len(self.players)]
            if test_uid in self.players_in_hand and test_uid not in self.folded:
                self.actor_idx = self.players_in_hand.index(test_uid)
                break

    def showdown(self):
        alive = [p for p in self.players_in_hand if p not in self.folded]
        if len(alive) == 1:
            winner = alive[0]
            self.chips[winner] += self.pot
            self.pot = 0
            for uid in self.chips:
                self.chips_dict[uid] = self.chips[uid]
            return [(winner, "最后存活", self.pot)]

        scores = {}
        for uid in alive:
            hand = self.hands[uid]
            if self.board:
                scores[uid] = self.evaluator.evaluate(hand, self.board)
            else:
                scores[uid] = self.evaluator.evaluate(hand, [])

        best_score = min(scores.values())
        overall_winners = {uid for uid in alive if scores[uid] == best_score}
        total_bets = {uid: self.total_bet[uid] for uid in alive}
        side_pots = compute_side_pots(total_bets)
        distribution = distribute_side_pots(side_pots, scores, overall_winners)

        for uid in alive:
            self.chips[uid] += distribution[uid]
            self.pot -= distribution[uid]
        self.pot = 0

        for uid in self.chips:
            self.chips_dict[uid] = self.chips[uid]

        desc = self.evaluator.class_to_string(self.evaluator.get_rank_class(best_score))
        return [(uid, desc, distribution[uid]) for uid in overall_winners]

    def cancel_timer(self):
        if self.turn_task:
            self.turn_task.cancel()
            self.turn_task = None

# ---------- 炸金花游戏类 ----------
class ZhaJinHuaGame:
    def __init__(self, chat_id, owner_id, chips_dict):
        self.chat_id = chat_id
        self.owner_id = owner_id
        self.players = []
        self.chips = {}
        self.chips_dict = chips_dict
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

    def add_player(self, user_id):
        if user_id not in self.players and self.phase == 'waiting':
            if user_id not in self.chips_dict:
                self.chips_dict[user_id] = STARTING_CHIPS
            self.chips[user_id] = self.chips_dict[user_id]
            self.players.append(user_id)
            return True
        return False

    def start_game(self):
        if len(self.players) < 2:
            return False
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
            if self.actor_idx == start:
                break
            uid = self.players_in_game[self.actor_idx]
            if uid not in self.folded:
                return uid
        return None

    def handle_action(self, uid, action, amount=None, target=None):
        if uid != self.current_player_id():
            return False, "还没轮到你"
        if action == 'see':
            if uid in self.seen:
                return False, "已看过牌"
            self.seen.add(uid)
            return True, None
        elif action == 'fold':
            self.folded.add(uid)
            self.players_in_game.remove(uid)
            if self.actor_idx >= len(self.players_in_game):
                self.actor_idx = 0
            alive = [p for p in self.players_in_game if p not in self.folded]
            if len(alive) == 1:
                self.phase = 'showdown'
                return True, None
            self.next_player()
            return True, None
        elif action == 'call':
            multiplier = ZJH_SEEN_MULTIPLIER if uid in self.seen else 1
            bet_amount = self.current_bet * multiplier
            if bet_amount == 0:
                bet_amount = ZJH_MIN_RAISE * multiplier
            actual = min(bet_amount, self.chips[uid])
            self.chips[uid] -= actual
            self.pot += actual
            self.total_bet[uid] += actual
            if self.chips[uid] == 0:
                self.folded.add(uid)
                self.players_in_game.remove(uid)
            if self.current_bet == 0:
                self.current_bet = ZJH_MIN_RAISE
            alive = [p for p in self.players_in_game if p not in self.folded]
            if len(alive) == 1:
                self.phase = 'showdown'
                return True, None
            self.next_player()
            return True, None
        elif action == 'raise':
            multiplier = ZJH_SEEN_MULTIPLIER if uid in self.seen else 1
            min_raise = ZJH_MIN_RAISE * multiplier
            if amount < min_raise:
                return False, f"最小加注为 {min_raise}"
            if amount > self.chips[uid]:
                return False, "筹码不足"
            self.chips[uid] -= amount
            self.pot += amount
            self.total_bet[uid] += amount
            self.current_bet = amount // multiplier
            alive = [p for p in self.players_in_game if p not in self.folded]
            if len(alive) == 1:
                self.phase = 'showdown'
                return True, None
            self.next_player()
            return True, None
        elif action == 'compare':
            target_id = target
            if target_id not in self.players_in_game or target_id == uid or target_id in self.folded:
                return False, "无效的对手"
            multiplier = ZJH_SEEN_MULTIPLIER if uid in self.seen else 1
            cost = self.current_bet * multiplier
            if cost > self.chips[uid]:
                return False, "筹码不足无法比牌"
            self.chips[uid] -= cost
            self.pot += cost
            self.total_bet[uid] += cost
            result = compare_zjh_hands(self.hands[uid], self.hands[target_id])
            loser = target_id if result > 0 else uid
            self.folded.add(loser)
            self.players_in_game.remove(loser)
            if self.actor_idx >= len(self.players_in_game):
                self.actor_idx = 0
            alive = [p for p in self.players_in_game if p not in self.folded]
            if len(alive) == 1:
                self.phase = 'showdown'
            else:
                self.next_player()
            return True, loser
        return False, "未知操作"

    def showdown(self):
        alive = [p for p in self.players_in_game if p not in self.folded]
        if len(alive) == 1:
            winner = alive[0]
            self.chips[winner] += self.pot
            self.pot = 0
            for uid in self.chips:
                self.chips_dict[uid] = self.chips[uid]
            return [(winner, "最后存活")]
        return []

    def cancel_timer(self):
        if self.turn_task:
            self.turn_task.cancel()
            self.turn_task = None

# ---------- 炸金花比较 ----------
def parse_card(card_int):
    raw = Card.int_to_str(card_int)
    rank_char = raw[0]
    suit = raw[1]
    RANK_VALUES = {'2':2,'3':3,'4':4,'5':5,'6':6,'7':7,'8':8,'9':9,'T':10,'J':11,'Q':12,'K':13,'A':14}
    rank = RANK_VALUES.get(rank_char, 0)
    return rank, suit

def get_zjh_hand_type(cards):
    ranks = []
    suits = []
    for c in cards:
        r, s = parse_card(c)
        ranks.append(r)
        suits.append(s)
    ranks.sort(reverse=True)
    is_flush = len(set(suits)) == 1
    is_straight = False
    if len(set(ranks)) == 3 and (max(ranks)-min(ranks)==2):
        is_straight = True
    if set(ranks) == {14,2,3}:
        is_straight = True
        ranks = [3,2,14]
    if len(set(ranks)) == 1:
        return (6, "豹子")
    if is_flush and is_straight:
        return (5, "同花顺")
    if is_flush:
        return (4, "同花")
    if is_straight:
        return (3, "顺子")
    if len(set(ranks)) == 2:
        return (2, "对子")
    if set(ranks) == {2,3,5}:
        return (0, "特殊235")
    return (1, "单张")

def compare_zjh_hands(hand1, hand2):
    type1, _ = get_zjh_hand_type(hand1)
    type2, _ = get_zjh_hand_type(hand2)
    if type1 == 0 and type2 == 6:
        return 1
    if type2 == 0 and type1 == 6:
        return -1
    if type1 > type2:
        return 1
    if type2 > type1:
        return -1
    def cmp_ranks(h):
        r = sorted([parse_card(c)[0] for c in h], reverse=True)
        if set(r) == {14,2,3}: r = [3,2,14]
        if len(set(r)) == 2:
            for val in r:
                if r.count(val) == 2:
                    pair = val
                    kicker = [x for x in r if x != val][0]
                    return (pair, kicker)
        return tuple(r)
    r1 = cmp_ranks(hand1)
    r2 = cmp_ranks(hand2)
    if r1 > r2:
        return 1
    elif r1 < r2:
        return -1
    return 0

# ---------- 界面 ----------
async def build_texas_text(game, app):
    player_lines = []
    for idx, uid in enumerate(game.players, 1):
        name = await get_name(app, uid)
        if uid in game.folded:
            status = "弃牌"
        elif uid in game.all_in:
            status = "全下"
        else:
            status = "在局"
        invested = game.total_bet.get(uid, 0)
        player_lines.append(f"|- {idx}. {name}  {status}  投入:{invested}")

    board_str = " ".join(card_str(c) for c in game.board) if game.board else "无"
    board_display = f"|--------------------+\n| {board_str}\n|--------------------+"

    phase_cn = {'preflop':'翻牌前','flop':'翻牌圈','turn':'转牌圈','river':'河牌圈','showdown':'摊牌'}.get(game.phase, game.phase)

    current = game.current_player_id()
    current_text = ""
    if current and game.phase in ('preflop','flop','turn','river'):
        to_call = game.current_bet - game.round_bets[current]
        if to_call < 0: to_call = 0
        cur_name = await get_name(app, current)
        current_text = f"|- 当前：{cur_name}  需跟注：{to_call}"

    text = (
        f"|- 积分德州牌桌\n"
        f"|- 状态：{phase_cn}\n"
        f"|- 公牌：\n{board_display}\n"
        f"|- 奖池：{game.pot}  当前下注：{game.current_bet}\n"
        f"{current_text}\n"
        f"|- 玩家：\n" + "\n".join(player_lines)
    )
    return text

async def build_zjh_text(game, app):
    player_lines = []
    for idx, uid in enumerate(game.players, 1):
        name = await get_name(app, uid)
        if uid in game.folded:
            status = "弃牌"
        else:
            status = "在局" + ("(已看)" if uid in game.seen else "(未看)")
        invested = game.total_bet.get(uid, 0)
        player_lines.append(f"|- {idx}. {name}  {status}  投入:{invested}")
    current = game.current_player_id()
    current_text = ""
    if current:
        cur_name = await get_name(app, current)
        current_text = f"|- 当前：{cur_name}"
    text = (
        f"|- 炸金花牌桌\n"
        f"|- 底注：{ZJH_ANTE}\n"
        f"|- 奖池：{game.pot}  当前下注：{game.current_bet}\n"
        f"{current_text}\n"
        f"|- 玩家：\n" + "\n".join(player_lines)
    )
    return text

async def update_texas_message(game, app):
    text = await build_texas_text(game, app)
    keyboard = None
    if game.phase in ('preflop','flop','turn','river') and game.current_player_id():
        keyboard = game.get_buttons(game.current_player_id())
    try:
        await app.bot.edit_message_text(chat_id=game.chat_id, message_id=game.game_msg_id, text=text, reply_markup=keyboard)
    except Exception as e:
        logger.error(f"德州更新错误: {e}")

async def update_zjh_message(game, app):
    text = await build_zjh_text(game, app)
    keyboard = None
    if game.phase == 'playing' and game.current_player_id():
        keyboard = game.get_buttons(game.current_player_id())
    try:
        await app.bot.edit_message_text(chat_id=game.chat_id, message_id=game.game_msg_id, text=text, reply_markup=keyboard)
    except Exception as e:
        logger.error(f"炸金花更新错误: {e}")

async def start_texas_timer(game, app):
    game.cancel_timer()
    uid = game.current_player_id()
    if not uid: return
    async def timeout():
        await asyncio.sleep(TURN_TIMEOUT)
        if game.phase in ('preflop','flop','turn','river') and game.current_player_id() == uid:
            game.handle_action(uid, 'fold')
            name = await get_name(app, uid)
            await app.bot.send_message(game.chat_id, f"⏰ {name} 超时未操作，自动弃牌")
            if game.phase == 'showdown':
                await finish_texas(game, app)
            else:
                await update_texas_message(game, app)
                await start_texas_timer(game, app)
    game.turn_task = asyncio.create_task(timeout())

async def start_zjh_timer(game, app):
    game.cancel_timer()
    uid = game.current_player_id()
    if not uid: return
    async def timeout():
        await asyncio.sleep(TURN_TIMEOUT)
        if game.phase == 'playing' and game.current_player_id() == uid:
            game.handle_action(uid, 'fold')
            name = await get_name(app, uid)
            await app.bot.send_message(game.chat_id, f"⏰ {name} 超时未操作，自动弃牌")
            if game.phase == 'showdown':
                await finish_zjh(game, app)
            else:
                await update_zjh_message(game, app)
                await start_zjh_timer(game, app)
    game.turn_task = asyncio.create_task(timeout())

async def finish_texas(game, app):
    game.cancel_timer()
    winners = game.showdown()
    board_str = " ".join(card_str(c) for c in game.board) if game.board else "无"
    board_display = f"|--------------------+\n| {board_str}\n|--------------------+"
    card_lines = []
    for uid in game.players:
        name = await get_name(app, uid)
        if uid in game.folded:
            card_lines.append(f"{name}：弃牌")
        elif uid in game.all_in:
            hand = game.hands.get(uid, [])
            hand_str = " ".join(card_str(c) for c in hand) if hand else "无"
            card_lines.append(f"{name}：{hand_str} (全下)")
        else:
            hand = game.hands.get(uid, [])
            hand_str = " ".join(card_str(c) for c in hand) if hand else "无"
            card_lines.append(f"{name}：{hand_str}")
    total_pot = sum(game.total_bet.values())
    prize_lines = []
    for wid, desc, amount in winners:
        name = await get_name(app, wid)
        prize_lines.append(f"{name} +{amount} ({desc})")
    profit_lines = []
    for uid in game.players:
        name = await get_name(app, uid)
        start = game.starting_chips_snapshot.get(uid, STARTING_CHIPS)
        end = game.chips.get(uid, 0)
        net = end - start
        invested = game.total_bet.get(uid, 0)
        profit_lines.append(f"{name}  投入:{invested}  盈亏:{net:+d}")
    for uid in game.players:
        start = game.starting_chips_snapshot.get(uid, STARTING_CHIPS)
        end = game.chips.get(uid, 0)
        net = end - start
        await save_history(game.chat_id, uid, net, end, '德州')
    await save_chips(game.chat_id, game.chips_dict)
    broke = [uid for uid in game.players if game.chips[uid] == 0]
    broke_text = ""
    if broke:
        names = [await get_name(app, uid) for uid in broke]
        broke_text = f"\n⚠️ 以下玩家筹码归零: {', '.join(names)}，使用 /add 补充"
    win_text = (
        f"积分德州已结算\n\n"
        f"|- 积分德州牌桌\n"
        f"|- 状态：摊牌\n"
        f"|- 公牌：\n{board_display}\n"
        f"|- 奖池：{total_pot}\n"
        f"结果：摊牌结算\n\n"
        f"牌型：\n" + "\n".join(card_lines) + "\n\n"
        f"派奖：\n" + "\n".join(prize_lines) + "\n\n"
        f"投入/盈亏：\n" + "\n".join(profit_lines) + broke_text
    )
    try:
        await app.bot.edit_message_text(chat_id=game.chat_id, message_id=game.game_msg_id, text=win_text)
    except Exception as e:
        logger.error(f"结算编辑失败: {e}")

async def finish_zjh(game, app):
    game.cancel_timer()
    winners = game.showdown()
    if not winners: return
    wid, _ = winners[0]
    name = await get_name(app, wid)
    board = game.hands.get(wid, [])
    board_str = " ".join(card_str(c) for c in board) if board else "无"
    hand_lines = []
    for uid in game.players:
        uname = await get_name(app, uid)
        if uid in game.folded:
            hand_lines.append(f"{uname}：弃牌")
        else:
            hand_str = " ".join(card_str(c) for c in game.hands.get(uid, []))
            hand_lines.append(f"{uname}：{hand_str}")
    for uid in game.players:
        start = game.chips_dict.get(uid, STARTING_CHIPS)
        end = game.chips.get(uid, 0)
        net = end - start
        await save_history(game.chat_id, uid, net, end, '炸金花')
    await save_chips(game.chat_id, game.chips_dict)
    text = (
        f"炸金花已结算\n\n"
        f"|- 获胜玩家：{name}\n"
        f"|- 手牌：{board_str}\n"
        f"|- 奖池：{sum(game.total_bet.values())}\n"
        f"牌型：\n" + "\n".join(hand_lines)
    )
    try:
        await app.bot.edit_message_text(chat_id=game.chat_id, message_id=game.game_msg_id, text=text)
    except:
        pass

# ---------- 全局管理 ----------
active_games = {}
AUTHORIZED_GROUPS = set()

async def init_auth():
    global AUTHORIZED_GROUPS
    db_auth = await load_auth()
    if db_auth:
        AUTHORIZED_GROUPS = db_auth
        logger.info(f"已加载 {len(AUTHORIZED_GROUPS)} 个授权群组")

def is_authorized(chat_id):
    return chat_id in AUTHORIZED_GROUPS

async def check_auth(update, context):
    chat_id = update.effective_chat.id
    if not is_authorized(chat_id):
        await update.effective_message.reply_text("❌ 此群组未授权，请联系管理员。")
        return False
    return True

# ---------- 命令 ----------
async def start_cmd(update, context):
    await update.message.reply_text("使用 /DZ 德州扑克, /ZJH 炸金花")

async def dz(update, context):
    if not await check_auth(update, context): return
    chat_id = update.effective_chat.id
    user = update.effective_user
    if chat_id in active_games and active_games[chat_id].phase != 'waiting':
        await update.message.reply_text("当前已有进行中的游戏，请等待结束。")
        return
    chips_dict = await load_chips(chat_id)
    game = TexasGame(chat_id, user.id, chips_dict)
    game.add_player(user.id)
    active_games[chat_id] = game
    player_list = [f"{i}. {await get_name(context.application, uid)}" for i, uid in enumerate(game.players, 1)]
    keyboard = [[InlineKeyboardButton("加入游戏", callback_data="texas_join")]]
    if len(game.players) >= 2:
        keyboard.append([InlineKeyboardButton("开始游戏", callback_data="texas_start")])
    msg = await update.message.reply_text(
        f"🃏 新一局德州扑克！\n发起人: {await get_name(context.application, user.id)}\n\n"
        f"已加入玩家:\n" + "\n".join(player_list) + "\n\n点击按钮加入或开始",
        reply_markup=InlineKeyboardMarkup(keyboard)
    )
    game.game_msg_id = msg.message_id

async def zjh(update, context):
    if not await check_auth(update, context): return
    chat_id = update.effective_chat.id
    user = update.effective_user
    if chat_id in active_games and active_games[chat_id].phase != 'waiting':
        await update.message.reply_text("当前已有进行中的游戏，请等待结束。")
        return
    chips_dict = await load_chips(chat_id)
    game = ZhaJinHuaGame(chat_id, user.id, chips_dict)
    game.add_player(user.id)
    active_games[chat_id] = game
    player_list = [f"{i}. {await get_name(context.application, uid)}" for i, uid in enumerate(game.players, 1)]
    keyboard = [[InlineKeyboardButton("加入游戏", callback_data="zjh_join")]]
    if len(game.players) >= 2:
        keyboard.append([InlineKeyboardButton("开始游戏", callback_data="zjh_start")])
    msg = await update.message.reply_text(
        f"🃏 炸金花房间！\n发起人: {await get_name(context.application, user.id)}\n\n"
        f"已加入玩家:\n" + "\n".join(player_list) + "\n\n点击按钮加入或开始",
        reply_markup=InlineKeyboardMarkup(keyboard)
    )
    game.game_msg_id = msg.message_id

async def end_game(update, context):
    if not await check_auth(update, context): return
    chat_id = update.effective_chat.id
    game = active_games.pop(chat_id, None)
    if not game:
        await update.message.reply_text("当前没有进行中的游戏。")
        return
    game.cancel_timer()
    if isinstance(game, TexasGame):
        game.save_chips()
        await save_chips(chat_id, game.chips_dict)
    else:
        await save_chips(chat_id, game.chips_dict)
    await update.message.reply_text("游戏已被手动终止。")
    try:
        await context.bot.edit_message_text(chat_id=chat_id, message_id=game.game_msg_id, text="游戏已被手动终止。")
    except:
        pass

async def add_chips(update, context):
    if not await check_auth(update, context): return
    chat_id = update.effective_chat.id
    target_id = None
    amount = 0
    if context.args and len(context.args) >= 2:
        arg1 = context.args[0]
        if update.message.entities:
            for ent in update.message.entities:
                if ent.type == 'text_mention':
                    target_id = ent.user.id
                elif ent.type == 'mention':
                    username = arg1.lstrip('@')
                    try:
                        target_chat = await context.bot.get_chat(f"@{username}")
                        target_id = target_chat.id
                    except:
                        pass
        if target_id is None:
            try:
                target_id = int(arg1)
            except ValueError:
                pass
        try:
            amount = int(context.args[1])
        except ValueError:
            amount = 0
    elif context.args and len(context.args) == 1:
        try:
            amount = int(context.args[0])
        except ValueError:
            amount = 0
        if update.message.reply_to_message:
            target_id = update.message.reply_to_message.from_user.id

    if target_id is None and update.message.reply_to_message:
        target_id = update.message.reply_to_message.from_user.id
        if context.args and len(context.args) >= 1:
            try:
                amount = int(context.args[0])
            except ValueError:
                amount = 0

    if target_id is None or amount <= 0:
        await update.message.reply_text("用法: /add @用户名 数量  或  /add 用户ID 数量\n也可回复某人后 /add 数量")
        return

    chips_dict = await load_chips(chat_id)
    if target_id not in chips_dict:
        chips_dict[target_id] = STARTING_CHIPS
    chips_dict[target_id] += amount
    await save_chips(chat_id, chips_dict)

    if chat_id in active_games and isinstance(active_games[chat_id], TexasGame) and active_games[chat_id].phase == 'waiting':
        game = active_games[chat_id]
        if target_id in game.chips:
            game.chips[target_id] = chips_dict[target_id]
    name = await get_name(context.application, target_id)
    await update.message.reply_text(f"✅ 已给 {name} 增加 {amount} 筹码，当前筹码: {chips_dict[target_id]}")

async def chips(update, context):
    if not await check_auth(update, context): return
    chat_id = update.effective_chat.id
    chips_dict = await load_chips(chat_id)
    if not chips_dict:
        await update.message.reply_text("当前群组无筹码记录。")
        return
    lines = [f"{i}. {await get_name(context.application, uid)}: {amt}" for i, (uid, amt) in enumerate(chips_dict.items(), 1)]
    await update.message.reply_text("💰 当前筹码:\n" + "\n".join(lines))

async def history(update, context):
    if not await check_auth(update, context): return
    chat_id = update.effective_chat.id
    user = update.effective_user
    if not db_pool:
        await update.message.reply_text("数据库未连接，无法查询历史。")
        return
    async with db_pool.acquire() as conn:
        rows = await conn.fetch(
            "SELECT game_time, net_profit, final_chips, game_type FROM history WHERE chat_id=$1 AND user_id=$2 ORDER BY game_time DESC LIMIT 10",
            chat_id, user.id
        )
    if not rows:
        await update.message.reply_text("无历史记录。")
        return
    lines = [f"{r['game_type']} {r['game_time'].strftime('%m-%d %H:%M')}  盈利:{r['net_profit']:+d}  余额:{r['final_chips']}" for r in rows]
    await update.message.reply_text("📊 最近10局战绩:\n" + "\n".join(lines))

async def shouquan(update, context):
    user = update.effective_user
    if user.id != ADMIN_USER_ID:
        await update.message.reply_text("❌ 只有机器人管理员可以执行此操作。")
        return
    chat_id = None
    if update.effective_chat.type == "private":
        if context.args and len(context.args) >= 1:
            try:
                chat_id = int(context.args[0])
            except ValueError:
                await update.message.reply_text("群组ID无效。")
                return
        else:
            await update.message.reply_text("用法: /shouquan 群组ID")
            return
    else:
        chat_id = update.effective_chat.id
    AUTHORIZED_GROUPS.add(chat_id)
    await save_auth(chat_id)
    await update.message.reply_text(f"✅ 群组 {chat_id} 已授权。")

async def qxshouquan(update, context):
    user = update.effective_user
    if user.id != ADMIN_USER_ID:
        await update.message.reply_text("❌ 只有机器人管理员可以执行此操作。")
        return
    chat_id = None
    if update.effective_chat.type == "private":
        if context.args and len(context.args) >= 1:
            try:
                chat_id = int(context.args[0])
            except ValueError:
                await update.message.reply_text("群组ID无效。")
                return
        else:
            await update.message.reply_text("用法: /qxshouquan 群组ID")
            return
    else:
        chat_id = update.effective_chat.id
    if chat_id in AUTHORIZED_GROUPS:
        AUTHORIZED_GROUPS.discard(chat_id)
        await delete_auth(chat_id)
        await update.message.reply_text(f"✅ 群组 {chat_id} 已取消授权。")
    else:
        await update.message.reply_text("该群组未授权。")

# ---------- 文本消息处理（自定义加注） ----------
async def text_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """处理自定义加注指令：加注XXX"""
    msg = update.effective_message
    if not msg or not msg.text: return
    user = update.effective_user
    if user.is_bot: return
    chat_id = update.effective_chat.id

    game = active_games.get(chat_id)
    if not game or not isinstance(game, TexasGame):
        return  # 没有活跃的德州游戏

    # 只允许当前玩家执行
    if game.phase not in ('preflop','flop','turn','river'):
        return
    if user.id != game.current_player_id():
        return

    text = msg.text.strip()
    match = re.match(r'^加注\s*(\d+)$', text)
    if not match:
        # 检查回复消息
        if msg.reply_to_message and msg.reply_to_message.message_id == game.game_msg_id:
            match = re.match(r'^加注\s*(\d+)$', text)
            if not match:
                return
        else:
            return

    amount = int(match.group(1))
    success, info = game.handle_action(user.id, 'raise', amount=amount)
    if not success:
        await msg.reply_text(f"❌ {info}")
        return

    # 加注成功，更新游戏
    if game.phase == 'showdown':
        await finish_texas(game, context.application)
        del active_games[chat_id]
    else:
        await update_texas_message(game, context.application)
        await start_texas_timer(game, context.application)

# ---------- 按钮回调 ----------
async def button_handler(update, context):
    query = update.callback_query
    data = query.data
    chat_id = query.message.chat.id
    if not is_authorized(chat_id):
        await query.answer("未授权", show_alert=True)
        return

    game = active_games.get(chat_id)
    if not game:
        await query.edit_message_text("游戏不存在。")
        return

    if isinstance(game, TexasGame):
        await texas_button_handler(update, context, game, query, data)
    elif isinstance(game, ZhaJinHuaGame):
        await zjh_button_handler(update, context, game, query, data)

async def texas_button_handler(update, context, game, query, data):
    user = query.from_user
    await query.answer()

    if data == 'texas_hand':
        if user.id in game.hands and user.id not in game.folded and game.phase != 'showdown':
            if user.id in game.hand_revealed:
                game.hand_revealed.discard(user.id)
                await query.answer("手牌已隐藏", show_alert=False)
            else:
                game.hand_revealed.add(user.id)
                hand = game.hands[user.id]
                hand_text = f"你的手牌: {card_str(hand[0])}  {card_str(hand[1])}"
                await query.answer(hand_text, show_alert=True)
            await update_texas_message(game, context.application)
        else:
            await query.answer("你已弃牌或游戏已结束", show_alert=True)
        return

    if game.phase == 'waiting':
        if data == 'texas_join':
            if game.add_player(user.id):
                player_list = [f"{i}. {await get_name(context.application, uid)}" for i, uid in enumerate(game.players, 1)]
                keyboard = [[InlineKeyboardButton("加入游戏", callback_data="texas_join")]]
                if len(game.players) >= 2:
                    keyboard.append([InlineKeyboardButton("开始游戏", callback_data="texas_start")])
                await query.edit_message_text(
                    f"已加入玩家:\n" + "\n".join(player_list) + "\n\n点击按钮加入或开始",
                    reply_markup=InlineKeyboardMarkup(keyboard)
                )
            else:
                await query.answer("加入失败", show_alert=True)
        elif data == 'texas_start':
            if user.id != game.owner_id:
                await query.answer("只有发起人可以开始", show_alert=True)
                return
            if len(game.players) < 2:
                await query.answer("至少需要2人", show_alert=True)
                return
            broke = [uid for uid in game.players if game.chips[uid] <= 0]
            if broke:
                names = [await get_name(context.application, uid) for uid in broke]
                await query.answer(f"以下玩家筹码不足: {', '.join(names)}，请使用 /add 补充", show_alert=True)
                return
            if game.start_game():
                await update_texas_message(game, context.application)
                await start_texas_timer(game, context.application)
            else:
                await query.edit_message_text("游戏开始失败")
        return

    if game.phase in ('preflop','flop','turn','river'):
        if user.id != game.current_player_id():
            await query.answer("还没轮到你", show_alert=True)
            return
        if data == 'texas_fold':
            success, info = game.handle_action(user.id, 'fold')
        elif data == 'texas_check':
            success, info = game.handle_action(user.id, 'check')
        elif data == 'texas_call':
            success, info = game.handle_action(user.id, 'call')
        elif data.startswith('texas_raise_'):
            try:
                amount = int(data.split('_')[2])
                success, info = game.handle_action(user.id, 'raise', amount=amount)
            except:
                await query.answer("无效加注额", show_alert=True)
                return
        elif data == 'texas_custom_raise':
            await query.answer("请直接回复此消息并输入“加注XXX”来下注", show_alert=True)
            return
        else:
            return

        if not success:
            await query.answer(info, show_alert=True)
            return
        if game.phase == 'showdown':
            await finish_texas(game, context.application)
            del active_games[game.chat_id]
            return
        await update_texas_message(game, context.application)
        await start_texas_timer(game, context.application)

async def zjh_button_handler(update, context, game, query, data):
    user = query.from_user
    await query.answer()

    if data == 'zjh_hand':
        if user.id in game.hands and user.id not in game.folded:
            hand = game.hands[user.id]
            hand_str = "  ".join(card_str(c) for c in hand)
            await query.answer(f"你的手牌: {hand_str}", show_alert=True)
        else:
            await query.answer("无手牌或已弃牌", show_alert=True)
        return

    if game.phase == 'waiting':
        if data == 'zjh_join':
            if game.add_player(user.id):
                player_list = [f"{i}. {await get_name(context.application, uid)}" for i, uid in enumerate(game.players, 1)]
                keyboard = [[InlineKeyboardButton("加入游戏", callback_data="zjh_join")]]
                if len(game.players) >= 2:
                    keyboard.append([InlineKeyboardButton("开始游戏", callback_data="zjh_start")])
                await query.edit_message_text(
                    f"已加入玩家:\n" + "\n".join(player_list) + "\n\n点击按钮加入或开始",
                    reply_markup=InlineKeyboardMarkup(keyboard)
                )
            else:
                await query.answer("加入失败", show_alert=True)
        elif data == 'zjh_start':
            if user.id != game.owner_id:
                await query.answer("只有发起人可以开始", show_alert=True)
                return
            if len(game.players) < 2:
                await query.answer("至少需要2人", show_alert=True)
                return
            if game.start_game():
                await update_zjh_message(game, context.application)
                await start_zjh_timer(game, context.application)
            else:
                await query.edit_message_text("游戏开始失败")
        return

    if game.phase == 'playing':
        if user.id != game.current_player_id():
            await query.answer("还没轮到你", show_alert=True)
            return

        if data == 'zjh_see':
            res, info = game.handle_action(user.id, 'see')
            if not res:
                await query.answer(info, show_alert=True)
            else:
                await update_zjh_message(game, context.application)
        elif data == 'zjh_fold':
            game.handle_action(user.id, 'fold')
            if game.phase == 'showdown':
                await finish_zjh(game, context.application)
                del active_games[game.chat_id]
                return
            await update_zjh_message(game, context.application)
            await start_zjh_timer(game, context.application)
        elif data == 'zjh_call':
            res, info = game.handle_action(user.id, 'call')
            if not res:
                await query.answer(info, show_alert=True)
            else:
                if game.phase == 'showdown':
                    await finish_zjh(game, context.application)
                    del active_games[game.chat_id]
                    return
                await update_zjh_message(game, context.application)
                await start_zjh_timer(game, context.application)
        elif data == 'zjh_raise_menu':
            multiplier = ZJH_SEEN_MULTIPLIER if user.id in game.seen else 1
            amounts = [100*multiplier, 200*multiplier, 500*multiplier, 1000*multiplier]
            btns = [[InlineKeyboardButton(str(a), callback_data=f"zjh_raise_{a}")] for a in amounts if a <= game.chips[user.id]]
            btns.append([InlineKeyboardButton("取消", callback_data="zjh_cancel")])
            await query.edit_message_reply_markup(reply_markup=InlineKeyboardMarkup(btns))
        elif data == 'zjh_compare_menu':
            opponents = [p for p in game.players_in_game if p != user.id and p not in game.folded]
            btns = [[InlineKeyboardButton(await get_name(context.application, uid), callback_data=f"zjh_compare_{uid}")] for uid in opponents]
            btns.append([InlineKeyboardButton("取消", callback_data="zjh_cancel")])
            await query.edit_message_reply_markup(reply_markup=InlineKeyboardMarkup(btns))
        elif data.startswith('zjh_raise_'):
            amount = int(data.split('_')[2])
            res, info = game.handle_action(user.id, 'raise', amount=amount)
            if not res:
                await query.answer(info, show_alert=True)
            else:
                if game.phase == 'showdown':
                    await finish_zjh(game, context.application)
                    del active_games[game.chat_id]
                    return
                await update_zjh_message(game, context.application)
                await start_zjh_timer(game, context.application)
        elif data.startswith('zjh_compare_'):
            target = int(data.split('_')[2])
            res, info = game.handle_action(user.id, 'compare', target=target)
            if not res:
                await query.answer(info, show_alert=True)
            else:
                loser = info
                await query.answer(f"比牌结果：{await get_name(context.application, loser)} 出局", show_alert=True)
                if game.phase == 'showdown':
                    await finish_zjh(game, context.application)
                    del active_games[game.chat_id]
                    return
                await update_zjh_message(game, context.application)
                await start_zjh_timer(game, context.application)
        elif data == 'zjh_cancel':
            await update_zjh_message(game, context.application)
        elif data == 'zjh_seen_info':
            await query.answer("你已经看过牌了", show_alert=True)
        return

# ---------- 主函数 ----------
def main():
    TOKEN = os.environ.get("BOT_TOKEN")
    if not TOKEN:
        logger.error("未设置 BOT_TOKEN")
        return

    loop = asyncio.get_event_loop()
    loop.run_until_complete(init_db())
    loop.run_until_complete(init_auth())

    app = Application.builder().token(TOKEN).build()
    app.add_handler(CommandHandler("start", start_cmd))
    app.add_handler(CommandHandler("dz", dz))
    app.add_handler(CommandHandler("zjh", zjh))
    app.add_handler(CommandHandler("end", end_game))
    app.add_handler(CommandHandler("add", add_chips))
    app.add_handler(CommandHandler("ph", chips))
    app.add_handler(CommandHandler("history", history))
    app.add_handler(CommandHandler("shouquan", shouquan))
    app.add_handler(CommandHandler("qxshouquan", qxshouquan))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, text_handler))
    app.add_handler(CallbackQueryHandler(button_handler))

    logger.info("Bot 启动...")
    while True:
        try:
            app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)
        except Exception as e:
            logger.error(f"Polling 错误: {traceback.format_exc()}")
            asyncio.sleep(5)

if __name__ == "__main__":
    main()
