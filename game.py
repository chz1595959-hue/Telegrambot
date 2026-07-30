from treys import Card, Deck, Evaluator

class Player:
    def __init__(self, uid, name):
        self.user_id = uid
        self.name = name
        self.hand = []
        self.chips = 1000
        self.round_bet = 0      # 本轮已下注额
        self.total_bet = 0
        self.folded = False
        self.all_in = False
        self.acted_this_round = False  # 本轮是否已行动

    def reset_for_new_hand(self):
        self.hand = []
        self.round_bet = 0
        self.total_bet = 0
        self.folded = False
        self.all_in = False
        self.acted_this_round = False

    def can_act(self):
        return not self.folded and not self.all_in

class PokerGame:
    def __init__(self, group_id):
        self.group_id = group_id
        self.players: list[Player] = []
        self.deck = Deck()
        self.community = []
        self.pot = 0
        self.current_bet = 0
        self.sb = 10
        self.bb = 20
        self.dealer_idx = 0
        self.action_idx = 0
        self.stage = 'waiting'
        self.evaluator = Evaluator()
        self.last_raise = 0
        self.min_raise = self.bb
        self.hand_over = False

    def add_player(self, uid, name):
        if len(self.players) >= 9:
            return False, "最多9人"
        if any(p.user_id == uid for p in self.players):
            return False, "已在游戏中"
        self.players.append(Player(uid, name))
        return True, "已加入"

    def start_game(self):
        if len(self.players) < 2:
            return False, "至少2人"
        for p in self.players:
            p.reset_for_new_hand()
            p.chips = 1000
        self.pot = 0
        self.community = []
        self.deck = Deck()
        self.deck.shuffle()
        for p in self.players:
            p.hand = self.deck.draw(2)
        self.dealer_idx = 0
        # 小盲、大盲
        sb_p = self.players[(self.dealer_idx + 1) % len(self.players)]
        bb_p = self.players[(self.dealer_idx + 2) % len(self.players)]
        sb_amt = min(self.sb, sb_p.chips)
        bb_amt = min(self.bb, bb_p.chips)
        sb_p.chips -= sb_amt
        sb_p.total_bet += sb_amt
        sb_p.round_bet = sb_amt
        sb_p.all_in = (sb_p.chips == 0)
        bb_p.chips -= bb_amt
        bb_p.total_bet += bb_amt
        bb_p.round_bet = bb_amt
        bb_p.all_in = (bb_p.chips == 0)
        self.pot = sb_amt + bb_amt
        self.current_bet = bb_amt
        self.min_raise = self.bb
        self.stage = 'preflop'
        # 行动位置为大盲后一位
        self.action_idx = (self.dealer_idx + 3) % len(self.players)
        self._skip_inactive()
        return True, "开始"

    def get_current_player(self):
        return self.players[self.action_idx]

    def _skip_inactive(self):
        """跳过无法行动的玩家，若无人可行动则推进阶段"""
        n = len(self.players)
        for _ in range(n):
            p = self.players[self.action_idx]
            if p.can_act():
                return True
            self.action_idx = (self.action_idx + 1) % n
        # 全部无法行动 → 下一阶段
        self._next_stage()
        return False

    def _all_acted_equal(self):
        """检查是否所有人都已行动且下注额一致"""
        active = [p for p in self.players if not p.folded]
        if not active:
            return True
        target = self.current_bet
        return all((p.all_in or p.acted_this_round) and p.round_bet == target for p in active)

    def process_action(self, uid, action, amount=0):
        if self.stage == 'showdown':
            return False, "游戏已结束"
        cur = self.get_current_player()
        if cur.user_id != uid:
            return False, "不是你的回合"
        if not cur.can_act():
            return False, "无法行动"

        if action == 'fold':
            cur.folded = True
            cur.acted_this_round = True
            self._next_action()
            return True, f"{cur.name} 弃牌"

        elif action == 'check':
            if self.current_bet > cur.round_bet:
                return False, "不能过牌，需要跟注或加注"
            cur.acted_this_round = True
            self._next_action()
            return True, f"{cur.name} 过牌"

        elif action == 'call':
            diff = self.current_bet - cur.round_bet
            if diff <= 0:
                # 已平跟，等同过牌
                return self.process_action(uid, 'check')
            call_amt = min(diff, cur.chips)
            cur.chips -= call_amt
            cur.round_bet += call_amt
            cur.total_bet += call_amt
            self.pot += call_amt
            if cur.chips == 0:
                cur.all_in = True
            cur.acted_this_round = True
            self._next_action()
            return True, f"{cur.name} 跟注 {call_amt}"

        elif action == 'raise':
            if amount <= self.current_bet:
                return False, "加注必须大于当前注"
            if amount < self.current_bet + self.min_raise:
                return False, f"最小加注 {self.min_raise}"
            needed = amount - cur.round_bet
            if needed > cur.chips:
                return False, "筹码不足"
            cur.chips -= needed
            cur.round_bet = amount
            cur.total_bet += needed
            self.pot += needed
            self.last_raise = amount - self.current_bet
            self.min_raise = self.last_raise
            self.current_bet = amount
            if cur.chips == 0:
                cur.all_in = True
            cur.acted_this_round = True
            # 重置其他未弃牌玩家的本轮行动状态
            for p in self.players:
                if p != cur and not p.folded:
                    p.acted_this_round = False
            self._next_action()
            return True, f"{cur.name} 加注到 {amount}"

        elif action == 'allin':
            amt = cur.chips
            if amt == 0:
                return False, "已经全下"
            cur.round_bet += amt
            cur.total_bet += amt
            self.pot += amt
            cur.chips = 0
            cur.all_in = True
            cur.acted_this_round = True
            if cur.round_bet > self.current_bet:
                # 相当于加注
                self.last_raise = cur.round_bet - self.current_bet
                self.min_raise = self.last_raise
                self.current_bet = cur.round_bet
                for p in self.players:
                    if p != cur and not p.folded:
                        p.acted_this_round = False
            self._next_action()
            return True, f"{cur.name} 全下 {amt}"
        else:
            return False, "未知操作"

    def _next_action(self):
        """移动到下一个可行动玩家，若本轮结束则推进阶段"""
        n = len(self.players)
        # 移动 action_idx
        for _ in range(n):
            self.action_idx = (self.action_idx + 1) % n
            if self.players[self.action_idx].can_act():
                break
        # 检查是否所有活跃玩家都已行动且下注额持平
        if self._all_acted_equal():
            self._next_stage()

    def _next_stage(self):
        """发公共牌或结束"""
        # 重置本轮行动状态
        for p in self.players:
            p.acted_this_round = False
            p.round_bet = 0
        self.current_bet = 0
        self.last_raise = 0
        self.min_raise = self.bb

        if self.stage == 'preflop':
            self.community += self.deck.draw(3)
            self.stage = 'flop'
        elif self.stage == 'flop':
            self.community += self.deck.draw(1)
            self.stage = 'turn'
        elif self.stage == 'turn':
            self.community += self.deck.draw(1)
            self.stage = 'river'
        elif self.stage == 'river':
            self.stage = 'showdown'
            self.hand_over = True
            return

        # 寻找第一个能行动的玩家（从庄位后一人开始）
        start = (self.dealer_idx + 1) % len(self.players)
        found = False
        for _ in range(len(self.players)):
            p = self.players[start]
            if p.can_act():
                self.action_idx = start
                found = True
                break
            start = (start + 1) % len(self.players)
        if not found:
            # 无人能行动，继续发下一阶段
            self._next_stage()
        else:
            # 即使找到玩家，还需检查是否只剩一人（直接摊牌）
            active = [p for p in self.players if not p.folded]
            if len(active) == 1:
                self._next_stage()

    def get_winners(self):
        active = [p for p in self.players if not p.folded]
        if len(active) == 1:
            return [(active[0], None)]
        scores = []
        for p in active:
            score = self.evaluator.evaluate(p.hand, self.community)
            scores.append((p, score))
        min_score = min(scores, key=lambda x: x[1])[1]
        return [item for item in scores if item[1] == min_score]

    def end_game(self):
        winners = self.get_winners()
        share = self.pot // len(winners) if winners else 0
        for p, _ in winners:
            p.chips += share
        return winners, share
