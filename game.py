from treys import Card, Deck, Evaluator

class Player:
    def __init__(self, user_id: int, name: str):
        self.user_id = user_id       # 也是私聊 chat_id
        self.name = name
        self.hand = []               # 两张手牌
        self.chips = 1000
        self.current_round_bet = 0   # 本轮已经下的筹码
        self.total_bet = 0           # 整个牌局总下注
        self.folded = False
        self.all_in = False

    def reset_round(self):
        self.current_round_bet = 0
        self.folded = False
        self.all_in = False

class PokerGame:
    def __init__(self, group_id: int):
        self.group_id = group_id
        self.players: list[Player] = []
        self.deck = Deck()
        self.community: list[int] = []  # 公共牌
        self.pot = 0
        self.current_bet = 0            # 本轮需要跟注的金额
        self.sb = 10
        self.bb = 20
        self.dealer_idx = 0
        self.action_idx = 0             # 当前行动的玩家在 players 中的索引
        self.stage = 'waiting'          # waiting, preflop, flop, turn, river, showdown
        self.evaluator = Evaluator()
        self.last_raise = 0
        self.min_raise = self.bb

    def add_player(self, user_id: int, name: str):
        if len(self.players) >= 9:
            return False, "最多9名玩家"
        if any(p.user_id == user_id for p in self.players):
            return False, "你已经在游戏中"
        self.players.append(Player(user_id, name))
        return True, "加入成功"

    def start_game(self):
        if len(self.players) < 2:
            return False, "至少需要2名玩家"
        # 重置所有玩家状态
        for p in self.players:
            p.reset_round()
            p.chips = 1000
        self.pot = 0
        self.community = []
        self.deck = Deck()
        self.deck.shuffle()
        # 发手牌
        for p in self.players:
            p.hand = self.deck.draw(2)
        # 庄位为第一个加入的玩家，小盲大盲顺延
        self.dealer_idx = 0
        # 盲注
        sb_player = self.players[(self.dealer_idx + 1) % len(self.players)]
        bb_player = self.players[(self.dealer_idx + 2) % len(self.players)]
        # 收取盲注
        sb_amount = min(self.sb, sb_player.chips)
        bb_amount = min(self.bb, bb_player.chips)
        sb_player.chips -= sb_amount
        sb_player.total_bet += sb_amount
        sb_player.current_round_bet = sb_amount
        bb_player.chips -= bb_amount
        bb_player.total_bet += bb_amount
        bb_player.current_round_bet = bb_amount
        self.pot = sb_amount + bb_amount
        self.current_bet = bb_amount
        # 行动玩家为大盲的下一个
        self.action_idx = (self.dealer_idx + 3) % len(self.players)
        self.stage = 'preflop'
        # 如果大盲注等于大盲额，则 min_raise 是大盲
        self.min_raise = self.bb
        return True, "游戏开始"

    def get_current_player(self) -> Player:
        return self.players[self.action_idx]

    def process_action(self, user_id: int, action: str, amount: int = 0):
        """处理一个行动，返回 (成功, 消息)"""
        player = self.get_current_player()
        if player.user_id != user_id:
            return False, "不是你的回合"
        if player.folded or player.all_in:
            return False, "你已经无法行动"

        if action == 'fold':
            player.folded = True
            self._next_player()
            return True, f"{player.name} 弃牌"

        elif action == 'check':
            if self.current_bet > player.current_round_bet:
                return False, "你需要跟注或加注"
            # 过牌
            self._next_player()
            return True, f"{player.name} 过牌"

        elif action == 'call':
            call_amount = self.current_bet - player.current_round_bet
            if call_amount <= 0:
                # 已经跟平，可以过牌
                return self.process_action(user_id, 'check')
            actual = min(call_amount, player.chips)
            player.chips -= actual
            player.current_round_bet += actual
            player.total_bet += actual
            self.pot += actual
            if player.chips == 0:
                player.all_in = True
            self._next_player()
            return True, f"{player.name} 跟注 {actual}"

        elif action == 'raise':
            # amount 为加注到的总金额（指本轮需要达到的金额，即 current_bet + 加注量？这里定义 amount 为“加注后新的当前下注额”）
            # 我们规定 amount 必须 >= 当前下注额 + min_raise，且不能超过玩家筹码
            if amount <= self.current_bet:
                return False, "加注必须大于当前下注额"
            if amount < self.current_bet + self.min_raise:
                return False, f"最小加注额为 {self.min_raise}"
            if amount > player.chips + player.current_round_bet:
                return False, "筹码不足"
            # 加注
            add_amount = amount - player.current_round_bet
            player.chips -= add_amount
            player.current_round_bet = amount
            player.total_bet += add_amount
            self.pot += add_amount
            self.current_bet = amount
            self.last_raise = amount - (self.current_bet - self.min_raise)  # 本次加注量
            self.min_raise = self.last_raise
            if player.chips == 0:
                player.all_in = True
            # 重置其他玩家的行动状态？不需要，只要跳到下一个未弃牌的玩家
            self._next_player()
            return True, f"{player.name} 加注到 {amount}"

        elif action == 'allin':
            allin_amount = player.chips
            if allin_amount == 0:
                return False, "已经全下"
            player.current_round_bet += allin_amount
            player.total_bet += allin_amount
            self.pot += allin_amount
            player.chips = 0
            player.all_in = True
            if player.current_round_bet > self.current_bet:
                self.current_bet = player.current_round_bet
                self.last_raise = player.current_round_bet - self.current_bet  # 粗略
                self.min_raise = self.last_raise
            self._next_player()
            return True, f"{player.name} 全下 {allin_amount}"
        else:
            return False, "未知操作"

    def _next_player(self):
        """移动到下一个可以行动的玩家"""
        n = len(self.players)
        for _ in range(n):
            self.action_idx = (self.action_idx + 1) % n
            next_player = self.players[self.action_idx]
            if not next_player.folded and not next_player.all_in:
                # 还需要判断该玩家是否已经平跟，且没有人加注
                # 如果所有未弃牌玩家都已行动且下注额相等，则结束本轮
                break
        # 检查本轮是否结束
        active_players = [p for p in self.players if not p.folded]
        # 如果所有活跃玩家都 all-in 或者都平跟，且没有人需要行动
        if all(p.all_in or p.current_round_bet == self.current_bet for p in active_players):
            # 进入下一阶段
            self._next_stage()

    def _next_stage(self):
        """进入下一阶段：发公共牌"""
        if self.stage == 'preflop':
            self.community.extend(self.deck.draw(3))
            self.stage = 'flop'
        elif self.stage == 'flop':
            self.community.extend(self.deck.draw(1))
            self.stage = 'turn'
        elif self.stage == 'turn':
            self.community.extend(self.deck.draw(1))
            self.stage = 'river'
        elif self.stage == 'river':
            self.stage = 'showdown'
            return
        # 重置轮次下注
        for p in self.players:
            p.current_round_bet = 0
        self.current_bet = 0
        self.last_raise = 0
        self.min_raise = self.bb
        # 找到第一个未弃牌且未all-in的玩家，从小盲开始？按照庄位后第一个未弃牌玩家
        start_idx = (self.dealer_idx + 1) % len(self.players)
        for _ in range(len(self.players)):
            p = self.players[start_idx]
            if not p.folded and not p.all_in:
                self.action_idx = start_idx
                break
            start_idx = (start_idx + 1) % len(self.players)

    def is_round_over(self):
        """判断当前下注轮是否结束（比如发完公共牌后需要继续行动）"""
        # 如果 stage 刚进入下一阶段且还没人行动，则不算结束，需要等待 action
        # 实际上 _next_stage 已经设置了新的 action_idx，所以返回 False 即可
        return False

    def get_winners(self):
        """返回赢家列表和他们的手牌排名"""
        active = [p for p in self.players if not p.folded]
        if len(active) == 1:
            return [(active[0], None)]  # 弃牌到只剩一人
        # 评估
        scores = []
        for p in active:
            score = self.evaluator.evaluate(p.hand, self.community)
            scores.append((p, score))
        # 找最低分（最佳手牌）
        min_score = min(scores, key=lambda x: x[1])[1]
        winners = [item for item in scores if item[1] == min_score]
        return winners

    def end_game(self):
        """结算并返回赢家信息"""
        winners = self.get_winners()
        # 分配底池（简化，平分）
        share = self.pot // len(winners)
        for p, _ in winners:
            p.chips += share  # 赢家收回筹码
        return winners, share
