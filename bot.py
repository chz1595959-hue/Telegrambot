import random, os, asyncio, logging, traceback, re
from collections import defaultdict
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, MessageHandler, filters, ContextTypes
from treys import Card, Evaluator

# ---------- 日志 ----------
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger(__name__)

# ---------- 配置 ----------
STARTING_CHIPS = 10000
SMALL_BLIND = 100
BIG_BLIND = 200
TURN_TIMEOUT = 60
FIXED_MIN_RAISE = 100
AUTO_START_TIMEOUT = 60
DEFAULT_ADMIN = 5431975432
ADMIN_USER_ID = int(os.environ.get("ADMIN_USER_ID", DEFAULT_ADMIN))

# ---------- 牌型中英文映射 ----------
HAND_NAME_CN = {
    "High Card": "高牌",
    "Pair": "一对",
    "One Pair": "一对",
    "Two Pair": "两对",
    "Three of a Kind": "三条",
    "Straight": "顺子",
    "Flush": "同花",
    "Full House": "葫芦",
    "Four of a Kind": "四条",
    "Straight Flush": "同花顺",
    "Royal Flush": "皇家同花顺",
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
        if not eligible_scores:
            continue
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

# ---------- 德州游戏类 ----------
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
        elif action == 'raise':
            # amount 为用户希望额外加注的筹码数
            call_amt = self.current_bet - self.round_bets[uid]  # 需要先跟注的筹码
            total_raise = call_amt + amount                     # 总加注额 = 跟注部分 + 额外加注
            if total_raise <= 0 or total_raise > self.chips[uid]:
                return False, "筹码不足或无效加注额"
            new_total = self.round_bets[uid] + total_raise      # 本轮总共投入
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

# ---------- 游戏界面 ----------
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

# ---------- 定时器 ----------
async def start_turn_timer(game, app):
    game.cancel_timer()
    uid = game.current_player()
    if not uid:
        if game.phase == 'showdown':
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
        return InlineKeyboardMarkup([[InlineKeyboardButton("🂠 查看手牌", callback_data="hand")]])

    to_call = game.current_bet - game.round_bets.get(uid, 0)
    if to_call < 0: to_call = 0

    row1 = [InlineKeyboardButton("❌ 弃牌", callback_data="fold")]
    if to_call == 0:
        row1.append(InlineKeyboardButton("✅ 过牌", callback_data="check"))
    else:
        row1.append(InlineKeyboardButton(f"✅ 跟注 {to_call}", callback_data="call"))

    btns = [[InlineKeyboardButton("🂠 查看手牌", callback_data="hand")], row1]

    if game.chips[uid] > to_call:
        raise_btns = []
        # 最小加注按钮：显示需要额外加注的金额（即总加注额 - 已下注）
        needed = (game.current_bet + FIXED_MIN_RAISE) - game.round_bets.get(uid, 0)
        if needed > 0 and game.chips[uid] >= needed:
            raise_btns.append(InlineKeyboardButton(f"🔼 加注 {needed}", callback_data=f"raise_{needed}"))
        if game.chips[uid] > to_call:
            raise_btns.append(InlineKeyboardButton(f"🔥 全下 {game.chips[uid]}", callback_data=f"raise_{game.chips[uid]}"))
        for i in range(0, len(raise_btns), 2):
            btns.append(raise_btns[i:i+2])
        btns.append([InlineKeyboardButton("✏️ 自定义加注", callback_data="custom_raise")])
    return InlineKeyboardMarkup(btns)

# ---------- 结算 ----------
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

# ---------- 命令 ----------
active_games = {}

def is_auth(chat_id):
    return chat_id in AUTHORIZED_GROUPS

async def need_auth(update, context):
    if not is_auth(update.effective_chat.id):
        await update.effective_message.reply_text("❌ 此群组未授权，请联系管理员。")
        return False
    return True

async def cmd_start(update, context):
    await update.message.reply_text("使用 /DZ 开始德州扑克")

async def cmd_dz(update, context):
    if not await need_auth(update, context): return
    chat_id = update.effective_chat.id
    if chat_id in active_games and active_games[chat_id].phase != 'waiting':
        await update.message.reply_text("当前已有进行中的游戏，请等待结束。")
        return
    game = PokerGame(chat_id, update.effective_user.id)
    game.add_player(update.effective_user.id)
    active_games[chat_id] = game
    plist = [f"{i}. {await get_name(context.application, uid)}" for i, uid in enumerate(game.players, 1)]
    kb = [[InlineKeyboardButton("加入游戏", callback_data="join")]]
    if len(game.players) >= 2:
        kb.append([InlineKeyboardButton("开始游戏", callback_data="start_game")])
    msg = await update.message.reply_text(
        f"🃏 新一局德州扑克！\n发起人: {await get_name(context.application, update.effective_user.id)}\n\n"
        f"已加入玩家:\n" + "\n".join(plist) + "\n\n点击按钮加入或开始",
        reply_markup=InlineKeyboardMarkup(kb)
    )
    game.game_msg_id = msg.message_id

async def cmd_end(update, context):
    if not await need_auth(update, context): return
    chat_id = update.effective_chat.id
    game = active_games.pop(chat_id, None)
    if not game:
        await update.message.reply_text("当前没有进行中的游戏。")
        return
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
    if game.phase == 'showdown':
        await settle_game(game, context.application)
        active_games.pop(chat_id, None); return

    if data == 'hand':
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
        if data == 'join':
            if game.add_player(user.id):
                plist = [f"{i}. {await get_name(context.application, u)}" for i, u in enumerate(game.players, 1)]
                kb = [[InlineKeyboardButton("加入游戏", callback_data="join")]]
                if len(game.players) >= 2:
                    kb.append([InlineKeyboardButton("开始游戏", callback_data="start_game")])
                await q.edit_message_text("已加入玩家:\n" + "\n".join(plist) + "\n\n点击按钮加入或开始", reply_markup=InlineKeyboardMarkup(kb))
                if len(game.players) >= 2:
                    await start_auto_start(game, context.application)
            else:
                await q.answer("加入失败", show_alert=True)
        elif data == 'start_game':
            if user.id != game.owner_id:
                await q.answer("只有发起人可以开始", show_alert=True); return
            if len(game.players) < 2:
                await q.answer("至少需要2人", show_alert=True); return
            if any(game.chips[u] <= 0 for u in game.players):
                await q.answer("有玩家筹码不足，请使用 /add 补充", show_alert=True); return
            if game.start_game():
                await update_table_msg(game, context.application)
                await start_turn_timer(game, context.application)
            else:
                await q.edit_message_text("开始失败")
        return

    if game.phase in ('preflop','flop','turn','river'):
        if user.id != game.current_player():
            await q.answer("还没轮到你", show_alert=True); return
        if data == 'fold':
            ok, desc = game.handle_action(user.id, 'fold')
        elif data == 'check':
            ok, desc = game.handle_action(user.id, 'check')
        elif data == 'call':
            ok, desc = game.handle_action(user.id, 'call')
        elif data.startswith('raise_'):
            # 从按钮传来的 amount 是额外加注额
            try:
                amt = int(data.split('_')[1])
                ok, desc = game.handle_action(user.id, 'raise', amount=amt)
            except:
                await q.answer("无效加注额", show_alert=True); return
        elif data == 'custom_raise':
            await q.answer("请回复此消息输入“加注XXX”来额外加注", show_alert=True); return
        else:
            return

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

# ---------- 文字加注（改进：amount 为额外加注） ----------
async def on_text(update, context):
    msg = update.effective_message
    if not msg or not msg.text: return
    user = update.effective_user
    if user.is_bot: return
    chat_id = update.effective_chat.id
    game = active_games.get(chat_id)
    if not game or game.phase not in ('preflop','flop','turn','river'):
        return
    if user.id != game.current_player():
        return
    m = re.match(r'^加注\s*(\d+)$', msg.text.strip())
    if not m:
        if msg.reply_to_message and msg.reply_to_message.message_id == game.game_msg_id:
            m = re.match(r'^加注\s*(\d+)$', msg.text.strip())
        if not m: return
    amt = int(m.group(1))
    ok, desc = game.handle_action(user.id, 'raise', amount=amt)
    if not ok:
        await msg.reply_text(f"❌ {desc}"); return
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
    app.add_handler(CommandHandler("end", cmd_end))
    app.add_handler(CommandHandler("add", cmd_add))
    app.add_handler(CommandHandler("ph", cmd_ph))
    app.add_handler(CommandHandler("shouquan", cmd_shouquan))
    app.add_handler(CommandHandler("qxshouquan", cmd_qxshouquan))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.add_handler(CallbackQueryHandler(on_button))
    logger.info("Bot 启动...")
    while True:
        try:
            app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)
        except Exception as e:
            logger.error(f"Polling 错误: {traceback.format_exc()}")
            asyncio.sleep(5)

if __name__ == "__main__":
    main()
