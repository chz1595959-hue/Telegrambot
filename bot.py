import random, os, asyncio, logging, traceback
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes
from treys import Card, Evaluator
import asyncpg

# ---------- 日志 ----------
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger(__name__)

# ---------- 配置 ----------
STARTING_CHIPS = 10000
SMALL_BLIND = 200
BIG_BLIND = 500
TURN_TIMEOUT = 60  # 秒
DEFAULT_ADMIN = 5431975432
ADMIN_USER_ID = int(os.environ.get("ADMIN_USER_ID", DEFAULT_ADMIN))

# ---------- 数据库 ----------
db_pool = None

async def init_db():
    global db_pool
    DATABASE_URL = os.environ.get("DATABASE_URL")
    if not DATABASE_URL:
        logger.warning("DATABASE_URL 未设置，筹码/授权/历史将不会持久化")
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

async def save_history(chat_id, user_id, net_profit, final_chips):
    if not db_pool: return
    async with db_pool.acquire() as conn:
        await conn.execute('''
            INSERT INTO history (chat_id, user_id, net_profit, final_chips)
            VALUES ($1,$2,$3,$4)
        ''', chat_id, user_id, net_profit, final_chips)

# ---------- 边池计算 ----------
def compute_side_pots(players_total_bet):
    if not players_total_bet:
        return []
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
        if not eligible_scores:
            continue
        best_score = min(eligible_scores.values())
        layer_winners = [uid for uid, s in eligible_scores.items() if s == best_score]
        share = layer['amount'] // len(layer_winners)
        rem = layer['amount'] % len(layer_winners)
        for uid in layer_winners:
            distribution[uid] += share
        if rem:
            distribution[layer_winners[0]] += rem
    return distribution

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

# ---------- 游戏核心 ----------
class Game:
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
            buttons.append([InlineKeyboardButton("🂠 查看手牌", callback_data="hand")])

        if uid not in self.players_in_hand or uid in self.folded or uid in self.all_in or uid != self.current_player_id():
            return InlineKeyboardMarkup(buttons)

        to_call = self.current_bet - self.round_bets[uid]
        if to_call < 0: to_call = 0
        buttons.append([InlineKeyboardButton("❌ 弃牌", callback_data="fold")])
        if to_call == 0:
            buttons.append([InlineKeyboardButton("✅ 过牌", callback_data="check")])
        else:
            buttons.append([InlineKeyboardButton(f"✅ 跟注 {to_call}", callback_data="call")])
        if self.chips[uid] > to_call:
            min_raise_total = self.current_bet + self.min_raise
            min_raise_needed = min_raise_total - self.round_bets[uid]
            if self.chips[uid] >= min_raise_needed:
                buttons.append([InlineKeyboardButton(f"🔼 加注至 {min_raise_total} (最小)", callback_data=f"raise_{min_raise_needed}")])
            half_pot = (self.pot + to_call) // 2 + to_call
            if self.chips[uid] >= half_pot and half_pot > to_call:
                buttons.append([InlineKeyboardButton(f"🔼 加注至 {half_pot} (半池)", callback_data=f"raise_{half_pot}")])
            full_pot = self.pot + to_call * 2
            if self.chips[uid] >= full_pot and full_pot > to_call:
                buttons.append([InlineKeyboardButton(f"🔼 加注至 {full_pot} (满池)", callback_data=f"raise_{full_pot}")])
            all_in_amount = self.chips[uid]
            if all_in_amount > to_call:
                buttons.append([InlineKeyboardButton(f"🔥 全下 {all_in_amount}", callback_data=f"raise_{all_in_amount}")])
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
            return [(winner, "Last one standing", 0)]

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

# ---------- 游戏界面更新 ----------
async def build_game_text(game: Game, app, extra=""):
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

    phase_cn = {
        'preflop': '翻牌前',
        'flop':    '翻牌圈',
        'turn':    '转牌圈',
        'river':   '河牌圈',
        'showdown': '摊牌'
    }.get(game.phase, game.phase)

    current = game.current_player_id()
    if current and game.phase in ('preflop','flop','turn','river'):
        to_call = game.current_bet - game.round_bets[current]
        if to_call < 0: to_call = 0
        cur_name = await get_name(app, current)
        current_text = f"|- 当前：{cur_name}  需跟注：{to_call}"
    else:
        current_text = ""

    text = (
        f"|- 积分德州牌桌\n"
        f"|- 状态：{phase_cn}\n"
        f"|- 公牌：\n{board_display}\n"
        f"|- 奖池：{game.pot}  当前下注：{game.current_bet}\n"
        f"{current_text}\n"
        f"|- 玩家：\n" + "\n".join(player_lines)
    )
    if extra:
        text += f"\n{extra}"
    return text

async def update_game_message(game: Game, app):
    text = await build_game_text(game, app)
    keyboard = None
    if game.phase in ('preflop','flop','turn','river') and game.current_player_id():
        keyboard = game.get_buttons(game.current_player_id())
    try:
        await app.bot.edit_message_text(
            chat_id=game.chat_id,
            message_id=game.game_msg_id,
            text=text,
            reply_markup=keyboard
        )
    except Exception as e:
        logger.error(f"update error: {e}")

async def start_turn_timer(game: Game, app):
    game.cancel_timer()
    uid = game.current_player_id()
    if not uid:
        return
    async def timeout():
        await asyncio.sleep(TURN_TIMEOUT)
        if game.phase in ('preflop','flop','turn','river') and game.current_player_id() == uid:
            success, _ = game.handle_action(uid, 'fold')
            if success:
                await app.bot.send_message(game.chat_id, f"⏰ {await get_name(app, uid)} 超时未操作，自动弃牌")
                if game.phase == 'showdown':
                    await finish_game(game, app)
                else:
                    await update_game_message(game, app)
                    await start_turn_timer(game, app)
    game.turn_task = asyncio.create_task(timeout())

async def finish_game(game: Game, app):
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
            if hand:
                hand_str = " ".join(card_str(c) for c in hand)
                card_lines.append(f"{name}：{hand_str} (全下)")
            else:
                card_lines.append(f"{name}：全下")
        else:
            hand = game.hands.get(uid, [])
            if hand:
                hand_str = " ".join(card_str(c) for c in hand)
                card_lines.append(f"{name}：{hand_str}")
            else:
                card_lines.append(f"{name}：无手牌")

    total_pot = sum(game.total_bet.values())
    prize_lines = []
    for wid, desc, amount in winners:
        name = await get_name(app, wid)
        prize_lines.append(f"{name} +{amount}")

    phase_cn = {
        'preflop': '翻牌前',
        'flop':    '翻牌圈',
        'turn':    '转牌圈',
        'river':   '河牌圈',
        'showdown': '摊牌'
    }.get(game.phase, game.phase)

    win_text = (
        f"积分德州已结算\n\n"
        f"|- 积分德州牌桌\n"
        f"|- 状态：{phase_cn}\n"
        f"|- 公牌：\n{board_display}\n"
        f"|- 奖池：{total_pot}\n"
        f"结果：摊牌结算\n\n"
        f"牌型：\n" + "\n".join(card_lines) + "\n\n"
        f"派奖：\n" + "\n".join(prize_lines)
    )

    # 历史记录
    for uid in game.players:
        start = game.starting_chips_snapshot.get(uid, STARTING_CHIPS)
        end = game.chips.get(uid, 0)
        net = end - start
        await save_history(game.chat_id, uid, net, end)
    await save_chips(game.chat_id, game.chips_dict)

    broke = [uid for uid in game.players if game.chips[uid] == 0]
    if broke:
        names = [await get_name(app, uid) for uid in broke]
        win_text += f"\n⚠️ 以下玩家筹码归零: {', '.join(names)}，使用 /add 补充"

    # 直接编辑原消息，不删除
    try:
        await app.bot.edit_message_text(
            chat_id=game.chat_id,
            message_id=game.game_msg_id,
            text=win_text,
        )
    except Exception as e:
        logger.error(f"结算消息编辑失败: {e}")

# ---------- 全局状态 ----------
games = {}
AUTHORIZED_GROUPS = set()

async def init_auth():
    global AUTHORIZED_GROUPS
    db_auth = await load_auth()
    if db_auth:
        AUTHORIZED_GROUPS = db_auth
        logger.info(f"已加载 {len(AUTHORIZED_GROUPS)} 个授权群组")

def is_authorized(chat_id):
    return chat_id in AUTHORIZED_GROUPS

async def check_auth(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    if not is_authorized(chat_id):
        await update.effective_message.reply_text("❌ 此群组未授权，请联系管理员。")
        return False
    return True

# ---------- 命令处理 ----------
async def dz(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_auth(update, context): return
    chat_id = update.effective_chat.id
    user = update.effective_user
    if chat_id in games and games[chat_id].phase != 'waiting':
        await update.message.reply_text("当前已有进行中的游戏，请等待结束。")
        return

    chips_dict = await load_chips(chat_id)
    game = Game(chat_id, user.id, chips_dict)
    game.add_player(user.id)
    games[chat_id] = game

    player_list = [f"{i}. {await get_name(context.application, uid)}" for i, uid in enumerate(game.players, 1)]
    keyboard = [[InlineKeyboardButton("加入游戏", callback_data="join")]]
    if len(game.players) >= 2:
        keyboard.append([InlineKeyboardButton("开始游戏", callback_data="start_game")])

    msg = await update.message.reply_text(
        f"🃏 新一局德州扑克！\n发起人: {await get_name(context.application, user.id)}\n\n"
        f"已加入玩家:\n" + "\n".join(player_list) + "\n\n点击按钮加入或开始",
        reply_markup=InlineKeyboardMarkup(keyboard)
    )
    game.game_msg_id = msg.message_id

async def end_game(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_auth(update, context): return
    chat_id = update.effective_chat.id
    game = games.pop(chat_id, None)
    if not game:
        await update.message.reply_text("当前没有进行中的游戏。")
        return
    game.cancel_timer()
    game.save_chips()
    await save_chips(chat_id, game.chips_dict)
    await update.message.reply_text("游戏已被手动终止。")
    try:
        await context.bot.edit_message_text(
            chat_id=chat_id,
            message_id=game.game_msg_id,
            text="游戏已被手动终止。",
        )
    except:
        pass

async def add_chips(update: Update, context: ContextTypes.DEFAULT_TYPE):
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

    if chat_id in games and games[chat_id].phase == 'waiting':
        game = games[chat_id]
        if target_id in game.chips:
            game.chips[target_id] = chips_dict[target_id]
    name = await get_name(context.application, target_id)
    await update.message.reply_text(f"✅ 已给 {name} 增加 {amount} 筹码，当前筹码: {chips_dict[target_id]}")

async def chips(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_auth(update, context): return
    chat_id = update.effective_chat.id
    chips_dict = await load_chips(chat_id)
    if not chips_dict:
        await update.message.reply_text("当前群组无筹码记录。")
        return
    lines = [f"{i}. {await get_name(context.application, uid)}: {amt}" for i, (uid, amt) in enumerate(chips_dict.items(), 1)]
    await update.message.reply_text("💰 当前筹码:\n" + "\n".join(lines))

async def history(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await check_auth(update, context): return
    chat_id = update.effective_chat.id
    user = update.effective_user
    if not db_pool:
        await update.message.reply_text("数据库未连接，无法查询历史。")
        return
    async with db_pool.acquire() as conn:
        rows = await conn.fetch(
            "SELECT game_time, net_profit, final_chips FROM history WHERE chat_id=$1 AND user_id=$2 ORDER BY game_time DESC LIMIT 10",
            chat_id, user.id
        )
    if not rows:
        await update.message.reply_text("无历史记录。")
        return
    lines = [f"📅 {r['game_time'].strftime('%m-%d %H:%M')}  盈利:{r['net_profit']:+d}  余额:{r['final_chips']}" for r in rows]
    await update.message.reply_text("📊 最近10局战绩:\n" + "\n".join(lines))

async def shouquan(update: Update, context: ContextTypes.DEFAULT_TYPE):
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

async def qxshouquan(update: Update, context: ContextTypes.DEFAULT_TYPE):
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

# ---------- 按钮处理（修复手牌 bug） ----------
async def button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = query.data
    chat_id = query.message.chat.id
    if not is_authorized(chat_id):
        await query.edit_message_text("❌ 此群组未授权，请联系管理员。")
        return

    game = games.get(chat_id)
    if not game:
        await query.edit_message_text("游戏不存在，请使用 /DZ 创建。")
        return

    if game.game_msg_id != query.message.message_id:
        return

    # 修复：只有非 hand 回调才预先 answer 空包
    if data != 'hand':
        await query.answer()

    user = query.from_user

    # 查看手牌
    if data == 'hand':
        if user.id in game.hands and user.id not in game.folded and game.phase != 'showdown':
            hand = game.hands[user.id]
            hand_text = f"你的手牌: {card_str(hand[0])}  {card_str(hand[1])}"
            await query.answer(hand_text, show_alert=True)
        else:
            await query.answer("你已弃牌或游戏已结束", show_alert=True)
        return

    # 等待阶段
    if game.phase == 'waiting':
        if data == 'join':
            if game.add_player(user.id):
                player_list = [f"{i}. {await get_name(context.application, uid)}" for i, uid in enumerate(game.players, 1)]
                keyboard = [[InlineKeyboardButton("加入游戏", callback_data="join")]]
                if len(game.players) >= 2:
                    keyboard.append([InlineKeyboardButton("开始游戏", callback_data="start_game")])
                await query.edit_message_text(
                    f"已加入玩家:\n" + "\n".join(player_list) + "\n\n点击按钮加入或开始",
                    reply_markup=InlineKeyboardMarkup(keyboard)
                )
            else:
                await query.answer("加入失败，可能已满或游戏已开始", show_alert=True)
        elif data == 'start_game':
            if user.id != game.owner_id:
                await query.answer("只有发起人可以开始", show_alert=True)
                return
            if len(game.players) < 2:
                await query.answer("至少需要2名玩家", show_alert=True)
                return
            broke = [uid for uid in game.players if game.chips[uid] <= 0]
            if broke:
                names = [await get_name(context.application, uid) for uid in broke]
                await query.answer(f"以下玩家筹码不足: {', '.join(names)}，请使用 /add 补充", show_alert=True)
                return
            if game.start_game():
                await update_game_message(game, context.application)
                await start_turn_timer(game, context.application)
            else:
                await query.edit_message_text("游戏开始失败")
        return

    # 游戏进行中
    if game.phase in ('preflop','flop','turn','river'):
        if user.id != game.current_player_id():
            await query.answer("还没轮到你", show_alert=True)
            return
        action = data.split('_')[0]
        amount = None
        if action == 'raise':
            try:
                amount = int(data.split('_')[1])
            except:
                await query.answer("无效加注额", show_alert=True)
                return
            action = 'raise'
        success, info = game.handle_action(user.id, action, amount)
        if not success:
            await query.answer(info, show_alert=True)
            return
        if game.phase == 'showdown':
            await finish_game(game, context.application)
            del games[chat_id]
            return
        await update_game_message(game, context.application)
        await start_turn_timer(game, context.application)

async def start_private(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("你好！请在群组中使用 /DZ 开始德州扑克。")

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
    app.add_handler(CommandHandler("start", start_private))
    app.add_handler(CommandHandler("dz", dz))
    app.add_handler(CommandHandler("end", end_game))
    app.add_handler(CommandHandler("add", add_chips))
    app.add_handler(CommandHandler("ph", chips))
    app.add_handler(CommandHandler("history", history))
    app.add_handler(CommandHandler("shouquan", shouquan))
    app.add_handler(CommandHandler("qxshouquan", qxshouquan))
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
