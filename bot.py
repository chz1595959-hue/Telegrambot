import random
import asyncio
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes
from treys import Card, Evaluator

# ---------- 游戏配置 ----------
STARTING_CHIPS = 10000          # 新玩家的初始筹码
SMALL_BLIND = 100               # 小盲注（可调）
BIG_BLIND = 200                 # 大盲注（可调）

# ---------- 全局筹码存储 ----------
# 格式：{ chat_id: { user_id: chips } }
group_chips = {}

# ---------- 德州扑克核心逻辑 ----------
class Game:
    def __init__(self, chat_id, owner_id, chips_dict):
        self.chat_id = chat_id
        self.owner_id = owner_id
        self.players = []          # 座位顺序
        self.chips = {}            # 本局玩家筹码（从 chips_dict 加载）
        self.chips_dict = chips_dict  # 引用全局筹码字典
        self.hands = {}
        self.folded = set()
        self.all_in = set()
        self.deck = []
        self.board = []
        self.pot = 0
        self.phase = 'waiting'     # waiting, preflop, flop, turn, river, showdown
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

    def add_player(self, user_id):
        if user_id not in self.players and self.phase == 'waiting':
            # 从持久化存储中获取筹码，若无则赋予起始筹码
            if user_id not in self.chips_dict:
                self.chips_dict[user_id] = STARTING_CHIPS
            self.chips[user_id] = self.chips_dict[user_id]
            self.players.append(user_id)
            return True
        return False

    def start_game(self):
        if len(self.players) < 2:
            return False
        # 确保所有玩家的筹码已从持久化字典加载（可能已更新过）
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
        if uid not in self.players_in_hand or uid in self.folded or uid in self.all_in:
            return []
        to_call = self.current_bet - self.round_bets[uid]
        if to_call < 0:
            to_call = 0
        buttons = []
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
            # 将本局筹码变化写回持久化存储
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
        # 将本局筹码变化写回持久化存储
        for uid in self.chips:
            self.chips_dict[uid] = self.chips[uid]
        desc = self.evaluator.class_to_string(self.evaluator.get_rank_class(best_score))
        return [(uid, desc) for uid in winners]

    def save_chips(self):
        """将当前筹码保存到全局存储（用于中断等情况）"""
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
        # 注意：保留 players 列表和 chips 字典（已经是最新的筹码）

# ---------- 全局游戏状态 ----------
games = {}

def card_str(card_int):
    raw = Card.int_to_pretty_str(card_int)
    return raw.replace('T', '10')

async def send_private_hand(app, user_id, hand):
    try:
        msg = f"你的手牌: {card_str(hand[0])}  {card_str(hand[1])}"
        await app.bot.send_message(chat_id=user_id, text=msg)
        return True
    except Exception:
        return False

async def get_name(app, user_id):
    try:
        chat = await app.bot.get_chat(user_id)
        return chat.first_name or str(user_id)
    except:
        return str(user_id)

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

    # 获取或初始化该群组的筹码字典
    if chat_id not in group_chips:
        group_chips[chat_id] = {}

    game = Game(chat_id, user.id, group_chips[chat_id])
    game.add_player(user.id)   # 房主自动加入
    games[chat_id] = game

    keyboard_buttons = [[InlineKeyboardButton("加入游戏", callback_data="join")]]
    if len(game.players) >= 2:
        keyboard_buttons.append([InlineKeyboardButton("开始游戏", callback_data="start_game")])

    msg = await update.message.reply_text(
        f"🃏 新一局德州扑克！\n发起人: {user.first_name}\n已加入: {await get_name(context.application, user.id)}\n点击下方按钮加入（至少2人）\n⚠️ 所有玩家必须先私聊机器人发送 /start 才能收到手牌！",
        reply_markup=InlineKeyboardMarkup(keyboard_buttons)
    )
    game.game_msg_id = msg.message_id

async def end_game(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    if chat_id not in games:
        await update.message.reply_text("当前没有进行中的游戏。")
        return
    game = games[chat_id]
    # 保存当前筹码（即使游戏未正常结束，已下注的筹码不会退还）
    game.save_chips()
    del games[chat_id]
    await update.message.reply_text("游戏已被手动终止。")
    try:
        await context.bot.delete_message(chat_id=chat_id, message_id=game.game_msg_id)
    except:
        pass

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

    if game.phase == 'waiting':
        if data == 'join':
            if game.add_player(user.id):
                names = [await get_name(context.application, uid) for uid in game.players]
                keyboard_buttons = [[InlineKeyboardButton("加入游戏", callback_data="join")]]
                if len(game.players) >= 2:
                    keyboard_buttons.append([InlineKeyboardButton("开始游戏", callback_data="start_game")])
                await query.edit_message_text(
                    f"已加入: {', '.join(names)}\n点击下方按钮加入或开始游戏",
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
            if game.start_game():
                failed = []
                for uid in game.players:
                    if not await send_private_hand(context.application, uid, game.hands[uid]):
                        failed.append(uid)
                if failed:
                    game.reset_to_waiting()
                    # 重置时保留已加入的玩家和筹码
                    names = [await get_name(context.application, uid) for uid in game.players]
                    keyboard_buttons = [[InlineKeyboardButton("加入游戏", callback_data="join")]]
                    if len(game.players) >= 2:
                        keyboard_buttons.append([InlineKeyboardButton("开始游戏", callback_data="start_game")])
                    await query.edit_message_text(
                        f"无法开始游戏，以下玩家未私聊机器人：{', '.join([await get_name(context.application, uid) for uid in failed])}\n"
                        "请这些玩家先私聊机器人发送 /start，然后房主重新点击开始。\n"
                        f"当前已加入: {', '.join(names)}",
                        reply_markup=InlineKeyboardMarkup(keyboard_buttons)
                    )
                    return
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
    app.add_handler(CallbackQueryHandler(button_handler))
    print("Bot 已启动...")
    app.run_polling(allowed_updates=Update.ALL_TYPES)

if __name__ == "__main__":
    main()
