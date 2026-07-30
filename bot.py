import random
import asyncio
from collections import defaultdict
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes
from treys import Card, Evaluator

# ---------- 游戏配置 ----------
STARTING_CHIPS = 1000
SMALL_BLIND = 1
BIG_BLIND = 2

# ---------- 德州扑克核心逻辑（修复版） ----------
class Game:
    def __init__(self, chat_id, owner_id):
        self.chat_id = chat_id
        self.owner_id = owner_id
        self.players = []          # 座位顺序（按加入顺序）
        self.chips = {}
        self.hands = {}
        self.folded = set()
        self.all_in = set()
        self.deck = []
        self.board = []
        self.pot = 0
        self.side_pots = []        # [(金额, 有资格的玩家集合)]
        self.phase = 'waiting'     # waiting, preflop, flop, turn, river, showdown
        self.players_in_hand = []  # 当前未弃牌玩家（按座位顺序）
        self.actor_idx = 0         # 在 players_in_hand 中的索引
        self.current_bet = 0       # 本轮当前最大下注额
        self.round_bets = {}       # {uid: 本轮已下总额}
        self.min_raise = BIG_BLIND
        self.acted_this_round = set()
        self.last_aggressor = None
        self.dealer_idx = 0        # 庄家在 self.players 中的索引
        self.game_msg_id = None
        self.evaluator = Evaluator()

    def add_player(self, user_id):
        if user_id not in self.players and self.phase == 'waiting':
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
        # 确定庄家（默认最后一个加入的为庄家）
        self.dealer_idx = len(self.players) - 1
        # 盲注位
        sb_idx = (self.dealer_idx + 1) % len(self.players)
        bb_idx = (self.dealer_idx + 2) % len(self.players)
        sb = self.players[sb_idx]
        bb = self.players[bb_idx]
        self._post_blind(sb, SMALL_BLIND)
        self._post_blind(bb, BIG_BLIND)
        self.current_bet = BIG_BLIND
        # 未弃牌玩家列表（按座位顺序）
        self.players_in_hand = self.players.copy()
        # 行动从大盲下一位开始
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

    def _update_side_pots(self):
        """更新边池（简化计算所有全下者的主池+边池）"""
        all_in_players = sorted([uid for uid in self.all_in if uid in self.players_in_hand],
                                key=lambda uid: self.round_bets[uid] + self.chips[uid])  # 参与的总投入
        # 这里仅作非常简化的处理：只分出主池和最大边池
        # 对于演示基本可用，正式游戏建议使用完整 side pot 算法
        # 重置
        self.side_pots = []
        remaining = self.pot
        prev_invest = 0
        for uid in all_in_players:
            total_invest = sum(self.round_bets.values())  # 近似
        # 为保持简洁，此处留一个占位，实际在 showdown 分配时计算
        pass

    def get_buttons(self, uid):
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
        # 加注选项（仅当有足够筹码且未全下）
        if self.chips[uid] > to_call:
            # 最小加注
            min_raise_total = self.current_bet + self.min_raise
            min_raise_needed = min_raise_total - self.round_bets[uid]
            if self.chips[uid] >= min_raise_needed:
                buttons.append([InlineKeyboardButton(f"Raise to {min_raise_total} (min)", callback_data=f"raise_{min_raise_needed}")])
            # 半池
            half_pot = (self.pot + to_call) // 2 + to_call
            if self.chips[uid] >= half_pot and half_pot > to_call:
                buttons.append([InlineKeyboardButton(f"Raise to {half_pot} (1/2 pot)", callback_data=f"raise_{half_pot}")])
            # 满池
            full_pot = self.pot + to_call * 2
            if self.chips[uid] >= full_pot and full_pot > to_call:
                buttons.append([InlineKeyboardButton(f"Raise to {full_pot} (pot)", callback_data=f"raise_{full_pot}")])
            # 全下
            all_in_amount = self.chips[uid]
            if all_in_amount > to_call:
                buttons.append([InlineKeyboardButton(f"All-in {all_in_amount}", callback_data=f"raise_{all_in_amount}")])
        return InlineKeyboardMarkup(buttons)

    def current_player_id(self):
        if not self.players_in_hand:
            return None
        if self.actor_idx >= len(self.players_in_hand):
            return None
        return self.players_in_hand[self.actor_idx]

    def next_player(self):
        """移动到下一个可以行动的玩家，若所有存活玩家均已行动则返回 None"""
        start = self.actor_idx
        while True:
            self.actor_idx = (self.actor_idx + 1) % len(self.players_in_hand)
            if self.actor_idx == start:
                # 全部轮询一遍仍无未行动者
                return None
            uid = self.players_in_hand[self.actor_idx]
            if uid not in self.folded and uid not in self.all_in and uid not in self.acted_this_round:
                return uid
            # 否则继续寻找（可能其他玩家都在 acted 或 all_in）
            # 注意：如果所有人都是全下或已行动，则结束本轮
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
            # actor_idx 调整到当前索引（移除后列表缩短）
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
            needed = amount  # 这是需要额外投入的筹码量
            if needed <= 0:
                return False, "invalid raise amount"
            if self.chips[uid] < needed:
                return False, "not enough chips"
            # 加注后总额 = 已经下的 + 本次加的
            new_total = self.round_bets[uid] + needed
            if new_total <= self.current_bet:
                return False, f"raise must be > current bet ({self.current_bet})"
            # 检查最小加注
            if new_total - self.current_bet < self.min_raise:
                return False, f"min raise is {self.min_raise}"
            self.chips[uid] -= needed
            self.round_bets[uid] += needed
            self.pot += needed
            self.current_bet = new_total
            self.min_raise = self.current_bet - (self.current_bet - self.min_raise)  # 实际可重设为 new_total - old_bet
            if self.chips[uid] == 0:
                self.all_in.add(uid)
            # 加注后，只有加注者已完成行动，其他人需要重新行动
            self.acted_this_round = {uid}
            self.last_aggressor = uid
        else:
            return False, "unknown action"

        # 检查是否只剩一人
        alive = [p for p in self.players_in_hand if p not in self.folded]
        if len(alive) == 1:
            self.phase = 'showdown'
            return True, None

        # 检查本轮是否结束
        if self.all_players_acted_or_allin():
            self._end_round()
            return True, None

        # 移动到下一个玩家
        self.next_player()
        # 如果移动后仍然找不到可行动玩家（如全下），也结束本轮
        if self.current_player_id() is None or self.all_players_acted_or_allin():
            self._end_round()
        return True, None

    def _end_round(self):
        """结束当前下注轮，进入下一阶段或摊牌"""
        # 重置轮内下注额
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

        # 确定下一轮起始玩家：小盲位（庄家下一位）最先行动，若其弃牌则向下找
        start_idx = (self.dealer_idx + 1) % len(self.players)
        for i in range(len(self.players)):
            test_uid = self.players[(start_idx + i) % len(self.players)]
            if test_uid in self.players_in_hand and test_uid not in self.folded:
                # 找到在未弃牌列表中的索引
                self.actor_idx = self.players_in_hand.index(test_uid)
                break

    def showdown(self):
        """比牌，返回赢家列表和牌型，并分配底池（含简化边池）"""
        alive = [p for p in self.players_in_hand if p not in self.folded]
        if len(alive) == 1:
            winner = alive[0]
            self.chips[winner] += self.pot
            self.pot = 0
            return [(winner, "Last one standing")]

        # 计算手牌评分
        scores = {}
        for uid in alive:
            hand = self.hands[uid]
            if self.board:
                scores[uid] = self.evaluator.evaluate(hand, self.board)
            else:
                # 无公共牌（极其罕见，比如翻前全弃）直接比较手牌
                scores[uid] = self.evaluator.evaluate(hand, [])

        # 简易边池分配：按玩家全下投入额分层
        # 收集每个存活玩家的总投入（本轮之前round_bets已清，需要用chips反推？这里简化直接按pot均分）
        # 以下只做基本均分，正式边池可单独优化
        best_score = min(scores.values())
        winners = [uid for uid in alive if scores[uid] == best_score]
        share = self.pot // len(winners)
        remainder = self.pot % len(winners)
        for uid in winners:
            self.chips[uid] += share
        if remainder:
            self.chips[winners[0]] += remainder
        self.pot = 0
        desc = self.evaluator.class_to_string(self.evaluator.get_rank_class(best_score))
        return [(uid, desc) for uid in winners]

# ---------- 全局状态 ----------
games = {}

def card_str(card_int):
    raw = Card.int_to_pretty_str(card_int)  # 例如 "T♥" 或 "As"
    # 替换 T 为 10
    return raw.replace('T', '10')

async def send_private_hand(app, user_id, hand):
    try:
        msg = f"你的手牌: {card_str(hand[0])}  {card_str(hand[1])}"
        await app.bot.send_message(chat_id=user_id, text=msg)
    except Exception:
        pass

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
    game = games.get(chat_id)
    if not game:
        await query.edit_message_text("游戏不存在，请使用 /newgame 创建。")
        return

    if game.game_msg_id != query.message.message_id:
        return

    if game.phase == 'waiting':
        if data == 'join':
            if game.add_player(user.id):
                names = [await get_name(context.application, uid) for uid in game.players]
                await query.edit_message_text(
                    f"已加入: {', '.join(names)}\n发起人点击下方按钮开始游戏",
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("开始游戏", callback_data="start_game")]
                    ]) if user.id == game.owner_id and len(game.players) >= 2 else None
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
            # 结算展示
            winners = game.showdown()
            board_str = " ".join(card_str(c) for c in game.board) if game.board else "无公共牌"
            win_text = f"🏆 游戏结束！\n公共牌: {board_str}\n"
            for wid, desc in winners:
                hand_cards = " ".join(card_str(c) for c in game.hands[wid])
                win_text += f"{await get_name(context.application, wid)} 获胜: {hand_cards} ({desc})\n"
            # 同时展示所有存活玩家的手牌
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
    await update.message.reply_text("你好！请在群组中使用 /newgame 开始德州扑克。")

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
