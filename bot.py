import random
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes
from treys import Card, Evaluator

# ---------- 游戏配置 ----------
STARTING_CHIPS = 10000
SMALL_BLIND = 200
BIG_BLIND = 500

# ---------- 全局筹码存储 ----------
group_chips = {}  # { chat_id: { user_id: chips } }

# ---------- 德州扑克核心逻辑 ----------
class Game:
    def __init__(self, chat_id, owner_id, chips_dict):
        self.chat_id = chat_id
        self.owner_id = owner_id
        self.players = []
        self.chips = {}
        self.chips_dict = chips_dict
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
        self.hand_revealed = set()  # 记录当前展开手牌的用户

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
        for uid in self.players:
            self.chips[uid] = self.chips_dict.get(uid, STARTING_CHIPS)
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

    def _post_blind(self, uid, amount):
        actual = min(amount, self.chips[uid])
        self.chips[uid] -= actual
        self.round_bets[uid] += actual
        self.pot += actual
        if self.chips[uid] == 0:
            self.all_in.add(uid)

    def get_buttons(self, uid):
        """为当前行动玩家生成操作按钮，同时添加通用手牌按钮"""
        buttons = []
        # 所有存活玩家都能看手牌
        if uid in self.hands and uid not in self.folded and self.phase != 'showdown':
            buttons.append([InlineKeyboardButton("🂠 查看手牌", callback_data="hand")])

        # 如果不是当前行动玩家，或者已弃牌/全下，只显示手牌按钮
        if uid not in self.players_in_hand or uid in self.folded or uid in self.all_in or uid != self.current_player_id():
            return InlineKeyboardMarkup(buttons)

        to_call = self.current_bet - self.round_bets[uid]
        if to_call < 0:
            to_call = 0
        buttons.append([InlineKeyboardButton("Fold", callback_data="fold")])
        if to_call == 0:
            buttons.append([InlineKeyboardButton("Check", callback_data="check")])
        else:
            buttons.append([InlineKeyboardButton(f"Call ({to_call})", callback_data="call")])
        if self.chips[uid] > to_call:
            min_raise_total = self.current_bet + self.min_raise
            min_raise_needed = min_raise_total - self.round_bets[uid]
            if self.chips[uid] >= min_raise_needed:
                buttons.append([InlineKeyboardButton(f"Raise to {min_raise_total} (min)", callback_data=f"raise_{min_raise_needed}")])
            half_pot = (self.pot + to_call) // 2 + to_call
            if self.chips[uid] >= half_pot and half_pot > to_call:
                buttons.append([InlineKeyboardButton(f"Raise to {half_pot} (1/2 pot)", callback_data=f"raise_{half_pot}")])
            full_pot = self.pot + to_call * 2
            if self.chips[uid] >= full_pot and full_pot > to_call:
                buttons.append([InlineKeyboardButton(f"Raise to {full_pot} (pot)", callback_data=f"raise_{full_pot}")])
            all_in_amount = self.chips[uid]
            if all_in_amount > to_call:
                buttons.append([InlineKeyboardButton(f"All-in {all_in_amount}", callback_data=f"raise_{all_in_amount}")])
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
            return [(winner, "Last one standing")]

        scores = {}
        for uid in alive:
            hand = self.hands[uid]
            if self.board:
                scores[uid] = self.evaluator.evaluate(hand, self.board)
            else:
                scores[uid] = self.evaluator.evaluate(hand, [])

        best_score = min(scores.values())
        winners = [uid for uid in alive if scores[uid] == best_score]
        share = self.pot // len(winners)
        remainder = self.pot % len(winners)
        for uid in winners:
            self.chips[uid] += share
        if remainder:
            self.chips[winners[0]] += remainder
        self.pot = 0
        for uid in self.chips:
            self.chips_dict[uid] = self.chips[uid]
        desc = self.evaluator.class_to_string(self.evaluator.get_rank_class(best_score))
        return [(uid, desc) for uid in winners]

    def save_chips(self):
        for uid in self.chips:
            self.chips_dict[uid] = self.chips[uid]

    def reset_to_waiting(self):
        self.phase = 'waiting'
        self.hands = {}
        self.folded.clear()
        self.all_in.clear()
        self.deck = []
        self.board = []
        self.pot = 0
        self.side_pots = []
        self.players_in_hand = []
        self.actor_idx = 0
        self.current_bet = 0
        self.round_bets = {}
        self.min_raise = BIG_BLIND
        self.acted_this_round.clear()
        self.last_aggressor = None
        self.dealer_idx = 0
        self.hand_revealed.clear()

# ---------- 辅助函数 ----------
def card_str(card_int):
    """将牌面转换为漂亮的字符串，例如 10♠️"""
    raw = Card.int_to_pretty_str(card_int)  # 例如 "T♥" 或 "As"
    # 替换 T 为 10，并美化花色符号
    suit_map = {
        '♠': '♠️',
        '♥': '♥️',
        '♦': '♦️',
        '♣': '♣️',
    }
    rank = raw[:-1].replace('T', '10')
    suit = raw[-1]
    suit_emoji = suit_map.get(suit, suit)
    return f"{rank}{suit_emoji}"

async def get_name(app, user_id):
    try:
        chat = await app.bot.get_chat(user_id)
        return chat.first_name or str(user_id)
    except:
        return str(user_id)

async def async_format_player_list(app, players):
    names = [await get_name(app, uid) for uid in players]
    return "\n".join(f"{i}. {name}" for i, name in enumerate(names, 1))

async def update_game_message(game: Game, app):
    text = "♠️ 德州扑克 ♥️\n"
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

# ---------- 命令处理 ----------
async def dz(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    user = update.effective_user

    if chat_id in games and games[chat_id].phase != 'waiting':
        await update.message.reply_text("当前已有进行中的游戏，请等待结束。")
        return

    if chat_id not in group_chips:
        group_chips[chat_id] = {}

    game = Game(chat_id, user.id, group_chips[chat_id])
    game.add_player(user.id)
    games[chat_id] = game

    player_list = await async_format_player_list(context.application, game.players)
    keyboard_buttons = [[InlineKeyboardButton("加入游戏", callback_data="join")]]
    if len(game.players) >= 2:
        keyboard_buttons.append([InlineKeyboardButton("开始游戏", callback_data="start_game")])

    msg = await update.message.reply_text(
        f"🃏 新一局德州扑克！\n发起人: {await get_name(context.application, user.id)}\n\n"
        f"已加入玩家:\n{player_list}\n\n"
        f"点击下方按钮加入（至少2人）",
        reply_markup=InlineKeyboardMarkup(keyboard_buttons)
    )
    game.game_msg_id = msg.message_id

async def end_game(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    if chat_id not in games:
        await update.message.reply_text("当前没有进行中的游戏。")
        return
    game = games[chat_id]
    game.save_chips()
    del games[chat_id]
    await update.message.reply_text("游戏已被手动终止。")
    try:
        await context.bot.delete_message(chat_id=chat_id, message_id=game.game_msg_id)
    except:
        pass

async def add_chips(update: Update, context: ContextTypes.DEFAULT_TYPE):
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
        await update.message.reply_text("用法: /add @用户名 数量  或  /add 用户ID 数量\n也可以回复某人的消息然后 /add 数量")
        return

    if chat_id not in group_chips:
        group_chips[chat_id] = {}
    if target_id not in group_chips[chat_id]:
        group_chips[chat_id][target_id] = STARTING_CHIPS

    group_chips[chat_id][target_id] += amount

    if chat_id in games and games[chat_id].phase == 'waiting':
        game = games[chat_id]
        if target_id in game.chips:
            game.chips[target_id] = group_chips[chat_id][target_id]

    name = await get_name(context.application, target_id)
    await update.message.reply_text(f"✅ 已给 {name} 增加 {amount} 筹码，当前筹码: {group_chips[chat_id][target_id]}")

async def chips(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    if chat_id not in group_chips or not group_chips[chat_id]:
        await update.message.reply_text("当前群组无筹码记录。")
        return

    chips_dict = group_chips[chat_id]
    lines = [f"{i}. {await get_name(context.application, uid)}: {amount}" for i, (uid, amount) in enumerate(chips_dict.items(), 1)]
    text = "💰 当前筹码:\n" + "\n".join(lines)
    await update.message.reply_text(text)

async def button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    data = query.data
    user = query.from_user
    chat_id = query.message.chat.id
    game = games.get(chat_id)
    if not game:
        await query.edit_message_text("游戏不存在，请使用 /DZ 创建。")
        return

    if game.game_msg_id != query.message.message_id:
        return

    # 查看手牌按钮（所有阶段均可使用）
    if data == 'hand':
        if user.id in game.hands and user.id not in game.folded and game.phase != 'showdown':
            if user.id in game.hand_revealed:
                # 已展开 → 隐藏
                game.hand_revealed.discard(user.id)
                await query.answer("手牌已隐藏", show_alert=False)
            else:
                # 未展开 → 显示
                game.hand_revealed.add(user.id)
                hand = game.hands[user.id]
                hand_text = f"你的手牌: {card_str(hand[0])}  {card_str(hand[1])}"
                await query.answer(hand_text, show_alert=True)
        else:
            await query.answer("你已弃牌或游戏已结束", show_alert=True)
        return

    if game.phase == 'waiting':
        if data == 'join':
            if game.add_player(user.id):
                player_list = await async_format_player_list(context.application, game.players)
                keyboard_buttons = [[InlineKeyboardButton("加入游戏", callback_data="join")]]
                if len(game.players) >= 2:
                    keyboard_buttons.append([InlineKeyboardButton("开始游戏", callback_data="start_game")])
                await query.edit_message_text(
                    f"已加入玩家:\n{player_list}\n\n点击按钮加入或开始游戏",
                    reply_markup=InlineKeyboardMarkup(keyboard_buttons)
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

            broke_players = [uid for uid in game.players if game.chips[uid] <= 0]
            if broke_players:
                names = [await get_name(context.application, uid) for uid in broke_players]
                await query.answer(f"以下玩家筹码不足: {', '.join(names)}，请使用 /add 补充", show_alert=True)
                return

            if game.start_game():
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
            winners = game.showdown()
            board_str = " ".join(card_str(c) for c in game.board) if game.board else "无公共牌"
            win_text = f"🏆 游戏结束！\n公共牌: {board_str}\n"
            for wid, desc in winners:
                hand_cards = " ".join(card_str(c) for c in game.hands[wid])
                win_text += f"{await get_name(context.application, wid)} 获胜: {hand_cards} ({desc})\n"
            alive = [p for p in game.players if p not in game.folded]
            for uid in alive:
                if uid not in [w[0] for w in winners]:
                    hand_cards = " ".join(card_str(c) for c in game.hands[uid])
                    win_text += f"{await get_name(context.application, uid)}: {hand_cards}\n"

            broke_players = [uid for uid in game.players if game.chips[uid] == 0]
            if broke_players:
                broke_names = [await get_name(context.application, uid) for uid in broke_players]
                win_text += f"\n⚠️ 以下玩家筹码归零: {', '.join(broke_names)}，可使用 /add 补充"

            await context.application.bot.send_message(chat_id=chat_id, text=win_text)
            del games[chat_id]
            try:
                await query.delete_message()
            except:
                pass
            return
        await update_game_message(game, context.application)

async def start_private(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("你好！请在群组中使用 /DZ 开始德州扑克。")

def main():
    import os
    TOKEN = os.environ.get("BOT_TOKEN")
    if not TOKEN:
        print("请设置环境变量 BOT_TOKEN")
        return
    app = Application.builder().token(TOKEN).build()
    app.add_handler(CommandHandler("start", start_private))
    app.add_handler(CommandHandler("dz", dz))
    app.add_handler(CommandHandler("end", end_game))
    app.add_handler(CommandHandler("add", add_chips))
    app.add_handler(CommandHandler("ph", chips))
    app.add_handler(CallbackQueryHandler(button_handler))
    print("Bot 已启动...")
    app.run_polling(allowed_updates=Update.ALL_TYPES)

if __name__ == "__main__":
    main()
