import random
import asyncio
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes
from treys import Card, Evaluator

# ---------- 游戏配置 ----------
STARTING_CHIPS = 1000
SMALL_BLIND = 1
BIG_BLIND = 2

# ---------- 德州扑克核心逻辑 ----------
class Game:
    def __init__(self, chat_id, owner_id):
        self.chat_id = chat_id
        self.owner_id = owner_id
        self.players = []          # [user_id, ...] 按加入顺序
        self.chips = {}
        self.hands = {}
        self.folded = set()
        self.all_in = set()
        self.deck = []
        self.board = []
        self.pot = 0
        self.phase = 'waiting'     # waiting, preflop, flop, turn, river, showdown
        self.actor_idx = 0         # 当前行动玩家在 self.players_in_hand 中的索引
        self.players_in_hand = []  # 未弃牌玩家列表（按座位顺序）
        self.current_bet = 0       # 当前轮需要跟注的总额
        self.round_bets = {}       # {user_id: 本轮已下注总额}
        self.min_raise = BIG_BLIND
        self.acted_this_round = set()
        self.last_aggressor = None
        self.game_msg_id = None    # 群内游戏状态消息ID
        self.evaluator = Evaluator()

    def add_player(self, user_id):
        if user_id not in self.players:
            self.players.append(user_id)
            self.chips[user_id] = STARTING_CHIPS
            return True
        return False

    def start_game(self):
        if len(self.players) < 2:
            return False
        self.phase = 'preflop'
        self.deck = [Card.new(r + s) for r in "23456789TJQKA" for s in "shdc"]
        random.shuffle(self.deck)
        # 发手牌
        for uid in self.players:
            self.hands[uid] = [self.deck.pop(), self.deck.pop()]
            self.round_bets[uid] = 0
        # 确定庄家（简单用最后一个加入的，也可随机）
        self.dealer_idx = len(self.players) - 1
        # 盲注
        sb_idx = (self.dealer_idx + 1) % len(self.players)
        bb_idx = (self.dealer_idx + 2) % len(self.players)
        sb = self.players[sb_idx]
        bb = self.players[bb_idx]
        self._post_blind(sb, SMALL_BLIND)
        self._post_blind(bb, BIG_BLIND)
        self.current_bet = BIG_BLIND
        # 行动顺序：大盲下一位
        self.players_in_hand = self.players.copy()
        self.actor_idx = (bb_idx + 1) % len(self.players)
        # 确保当前玩家在未弃牌列表中
        # 记录行动过的人为空（盲注不算行动）
        self.acted_this_round = set()
        return True

    def _post_blind(self, uid, amount):
        actual = min(amount, self.chips[uid])
        self.chips[uid] -= actual
        self.round_bets[uid] += actual
        self.pot += actual
        if self.chips[uid] == 0:
            self.all_in.add(uid)

    def get_buttons(self, uid):
        """为当前行动玩家生成操作按钮"""
        if uid not in self.players_in_hand or uid in self.folded or uid in self.all_in:
            return []
        to_call = self.current_bet - self.round_bets[uid]
        if to_call < 0:
            to_call = 0
        buttons = []
        # Fold
        buttons.append([InlineKeyboardButton("Fold", callback_data="fold")])
        # Check / Call
        if to_call == 0:
            buttons.append([InlineKeyboardButton("Check", callback_data="check")])
        else:
            buttons.append([InlineKeyboardButton(f"Call ({to_call})", callback_data="call")])
        # Raise buttons (only if not all-in and enough chips)
        if self.chips[uid] > to_call:
            # 最小加注
            min_raise_total = self.current_bet + self.min_raise
            min_raise_amount = min_raise_total - self.round_bets[uid]
            if self.chips[uid] >= min_raise_amount:
                buttons.append([InlineKeyboardButton(f"Raise min ({min_raise_amount})", callback_data=f"raise_{min_raise_amount}")])
            # 半池加注
            half_pot = (self.pot + to_call) // 2 + to_call
            if self.chips[uid] >= half_pot and half_pot > to_call:
                buttons.append([InlineKeyboardButton(f"Raise 1/2 pot ({half_pot})", callback_data=f"raise_{half_pot}")])
            # 满池加注
            full_pot = self.pot + to_call * 2
            if self.chips[uid] >= full_pot and full_pot > to_call:
                buttons.append([InlineKeyboardButton(f"Raise pot ({full_pot})", callback_data=f"raise_{full_pot}")])
            # 全下
            all_in_amount = self.chips[uid]
            if all_in_amount > to_call:
                buttons.append([InlineKeyboardButton(f"All-in ({all_in_amount})", callback_data=f"raise_{all_in_amount}")])
        return InlineKeyboardMarkup(buttons)

    def current_player_id(self):
        if not self.players_in_hand:
            return None
        return self.players_in_hand[self.actor_idx]

    def next_player(self):
        """移动到下一个可以行动的玩家"""
        if not self.players_in_hand:
            return None
        start = self.actor_idx
        while True:
            self.actor_idx = (self.actor_idx + 1) % len(self.players_in_hand)
            if self.actor_idx == start:
                break
            uid = self.players_in_hand[self.actor_idx]
            if uid not in self.folded and uid not in self.all_in:
                return uid
        return None

    def handle_action(self, uid, action, amount=None):
        """执行动作：fold/check/call/raise"""
        if uid != self.current_player_id():
            return False, "not your turn"
        if action == 'fold':
            self.folded.add(uid)
            self.players_in_hand.remove(uid)
            # 调整actor_idx
            if self.actor_idx >= len(self.players_in_hand):
                self.actor_idx = 0
        elif action == 'check':
            self.acted_this_round.add(uid)
        elif action == 'call':
            call_amount = self.current_bet - self.round_bets[uid]
            actual = min(call_amount, self.chips[uid])
            self.chips[uid] -= actual
            self.round_bets[uid] += actual
            self.pot += actual
            if self.chips[uid] == 0:
                self.all_in.add(uid)
            self.acted_this_round.add(uid)
        elif action == 'raise':
            raise_total = amount
            if raise_total <= self.current_bet:
                return False, "raise must be greater than current bet"
            needed = raise_total - self.round_bets[uid]
            actual = min(needed, self.chips[uid])
            self.chips[uid] -= actual
            self.round_bets[uid] += actual
            self.pot += actual
            self.current_bet = self.round_bets[uid]
            if self.chips[uid] == 0:
                self.all_in.add(uid)
            self.acted_this_round = {uid}  # 加注后只保留加注者
            self.last_aggressor = uid
        else:
            return False, "unknown action"

        # 检查是否只有一人存活
        alive = [p for p in self.players_in_hand if p not in self.folded]
        if len(alive) == 1:
            self.phase = 'showdown'
            return True, None

        # 判断本轮是否结束：当前玩家行动后，如果下一玩家已在acted集合中，则轮结束
        next_uid = self.next_player()
        if next_uid is None:
            # 所有人都全下或弃牌
            self._end_round()
            return True, None
        if next_uid in self.acted_this_round:
            self._end_round()
            return True, None
        return True, None

    def _end_round(self):
        """结束当前下注轮，进入下一阶段或摊牌"""
        # 重置轮内下注额
        for uid in self.round_bets:
            self.round_bets[uid] = 0
        self.current_bet = 0
        self.acted_this_round.clear()
        # 进入下一阶段
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
        # 确定下一轮先手：小盲位开始（players_in_hand中第一个是小盲？可按位置定）
        # 简单从列表开头第一个未弃牌玩家开始
        for i, uid in enumerate(self.players_in_hand):
            if uid not in self.folded and uid not in self.all_in:
                self.actor_idx = i
                break

    def showdown(self):
        """比较手牌，返回赢家列表和牌型描述"""
        alive = [p for p in self.players_in_hand if p not in self.folded]
        if len(alive) == 1:
            winner = alive[0]
            self.chips[winner] += self.pot
            self.pot = 0
            return [(winner, "Last one standing")]
        # 评估手牌
        best = {}
        for uid in alive:
            hand = self.hands[uid]
            score = self.evaluator.evaluate(hand, self.board)
            best[uid] = score
        min_score = min(best.values())
        winners = [uid for uid, sc in best.items() if sc == min_score]
        # 平分底池（简化，忽略边池）
        share = self.pot // len(winners)
        remainder = self.pot % len(winners)
        for uid in winners:
            self.chips[uid] += share
        if remainder:
            self.chips[winners[0]] += remainder
        self.pot = 0
        return [(uid, self.evaluator.class_to_string(self.evaluator.get_rank_class(min_score))) for uid in winners]

# ---------- 机器人状态 ----------
games = {}   # {chat_id: Game}

def card_str(card_int):
    return Card.int_to_pretty_str(card_int)

async def send_private_hand(app, user_id, hand):
    try:
        msg = f"你的手牌: {card_str(hand[0])}  {card_str(hand[1])}"
        await app.bot.send_message(chat_id=user_id, text=msg)
    except Exception:
        pass

async def update_game_message(game: Game, app):
    """刷新群聊中的游戏主消息"""
    text = f"♠️ 德州扑克  ♥️\n"
    text += f"底池: {game.pot}\n"
    if game.board:
        board_cards = " ".join(card_str(c) for c in game.board)
        text += f"公共牌: {board_cards}\n"
    else:
        text += "公共牌: -\n"
    text += "\n玩家筹码:\n"
    for uid in game.players:
        status = ""
        if uid in game.folded:
            status = " (弃牌)"
        elif uid in game.all_in:
            status = " (全下)"
        text += f"- {await get_name(app, uid)}: {game.chips[uid]}{status}\n"
    if game.phase in ('preflop','flop','turn','river'):
        current = game.current_player_id()
        if current:
            text += f"\n轮到 {await get_name(app, current)} 行动"
    elif game.phase == 'showdown':
        text += "\n摊牌！"
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
        print(f"update error: {e}")

async def get_name(app, user_id):
    try:
        chat = await app.bot.get_chat(user_id)
        return chat.first_name or str(user_id)
    except:
        return str(user_id)

# ---------- 命令处理 ----------
async def new_game(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    user = update.effective_user
    if chat_id in games and games[chat_id].phase != 'waiting':
        await update.message.reply_text("当前已有进行中的游戏，请等待结束。")
        return
    game = Game(chat_id, user.id)
    games[chat_id] = game
    keyboard = InlineKeyboardMarkup([[InlineKeyboardButton("加入游戏", callback_data="join")]])
    msg = await update.message.reply_text(
        f"🃏 新一局德州扑克！\n发起人: {user.first_name}\n点击下方按钮加入（至少2人）",
        reply_markup=keyboard
    )
    game.game_msg_id = msg.message_id

async def button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    data = query.data
    user = query.from_user
    chat_id = query.message.chat.id
    msg_id = query.message.message_id
    game = games.get(chat_id)
    if not game:
        await query.edit_message_text("游戏不存在，请使用 /newgame 创建。")
        return

    if game.game_msg_id != msg_id:
        # 防止旧消息按钮干扰
        return

    if game.phase == 'waiting':
        if data == 'join':
            if game.add_player(user.id):
                await query.edit_message_text(
                    f"已加入: {', '.join([await get_name(context.application, uid) for uid in game.players])}\n"
                    f"发起人点下方按钮开始游戏",
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("开始游戏", callback_data="start_game")]
                    ]) if user.id == game.owner_id and len(game.players) >= 2 else None
                )
            else:
                await query.answer("你已经在游戏中", show_alert=True)
        elif data == 'start_game':
            if user.id != game.owner_id:
                await query.answer("只有发起人可以开始", show_alert=True)
                return
            if len(game.players) < 2:
                await query.answer("至少需要2名玩家", show_alert=True)
                return
            if game.start_game():
                # 私聊发手牌
                for uid in game.players:
                    await send_private_hand(context.application, uid, game.hands[uid])
                await update_game_message(game, context.application)
            else:
                await query.edit_message_text("游戏开始失败")
        return

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
            # 游戏结束
            winners = game.showdown()
            win_text = "🏆 游戏结束！\n"
            for wid, hand_desc in winners:
                hand_cards = " ".join(card_str(c) for c in game.hands[wid])
                win_text += f"{await get_name(context.application, wid)} 获胜: {hand_cards} ({hand_desc})\n"
            await context.application.bot.send_message(chat_id=chat_id, text=win_text)
            del games[chat_id]
            try:
                await query.delete_message()
            except:
                pass
            return
        # 继续游戏
        await update_game_message(game, context.application)

async def start_private(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("你好！请在群组中使用 /newgame 开始德州扑克。")

# ---------- 主函数 ----------
def main():
    import os
    TOKEN = os.environ.get("BOT_TOKEN")
    if not TOKEN:
        print("请设置环境变量 BOT_TOKEN")
        return
    app = Application.builder().token(TOKEN).build()
    app.add_handler(CommandHandler("start", start_private))
    app.add_handler(CommandHandler("newgame", new_game))
    app.add_handler(CallbackQueryHandler(button_handler))
    print("Bot 已启动...")
    app.run_polling(allowed_updates=Update.ALL_TYPES)

if __name__ == "__main__":
    main()
