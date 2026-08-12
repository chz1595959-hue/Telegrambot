# -*- coding: utf-8 -*-
"""麻将核心逻辑（纯逻辑，无 Telegram 依赖，可单独 import 测试）。

牌型（共 30 种，每种 4 张 = 120 张）：
    万 0-8 ｜ 条 9-17 ｜ 筒 18-26 ｜ 中 27 ｜ 发 28 ｜ 白 29
玩法：简化广东麻将——碰 / 杠 / 胡，鸡胡也能胡；番种仅 碰碰胡 / 清一色 / 混一色 / 自摸 / 杠上花。
设计目标（对应使用者最在意的 4 个坑）：
    1) 机器人不每局打同样的牌：发牌随机洗牌 + AI 按手牌评估打最废的牌 + 等价牌随机选 + 每台电脑性格不同。
    2) 开得了局：start() 校验人数 + 自动补位电脑，状态机清晰。
    3) 结算得了：settle() 纯计算，不碰积分；积分累加由调用方负责（绝不覆盖）。
"""
import random

SUIT = 30
WAN, TIAO, TONG = 0, 9, 18
ZHONG, FA, BAI = 27, 28, 29

TILE_EMOJI = [
    "🀇", "🀈", "🀉", "🀊", "🀋", "🀌", "🀍", "🀎", "🀏",   # 万
    "🀐", "🀑", "🀒", "🀓", "🀔", "🀕", "🀖", "🀗", "🀘",   # 条
    "🀙", "🀚", "🀛", "🀜", "🀝", "🀞", "🀟", "🀠", "🀡",   # 筒
    "🀄", "🀅", "🀆",                                   # 中 发 白
]
TILE_NAME = [
    "一万", "二万", "三万", "四万", "五万", "六万", "七万", "八万", "九万",
    "一条", "二条", "三条", "四条", "五条", "六条", "七条", "八条", "九条",
    "一筒", "二筒", "三筒", "四筒", "五筒", "六筒", "七筒", "八筒", "九筒",
    "红中", "发财", "白板",
]

BASE_SCORE = 100      # 每番基础分
MAX_FAN = 8           # 封顶番数
DRAW_RESERVE = 14     # 牌墙留 14 张防摸穿（流局线）

BOT_PERSONALITIES = ["normal", "aggressive", "conservative"]


# ----------------------------------------------------------------------------
# 基础工具
# ----------------------------------------------------------------------------
def tile_emoji(t):
    return TILE_EMOJI[t]


def tile_name(t):
    return TILE_NAME[t]


def hand_to_counts(tiles):
    c = [0] * SUIT
    for t in tiles:
        c[t] += 1
    return c


def build_wall():
    wall = []
    for t in range(SUIT):
        wall += [t] * 4
    random.shuffle(wall)
    return wall


def render_hand(hand_counts, melds=None):
    """把暗手牌渲染成 emoji 串（按 万/条/筒/字 排序）。"""
    parts = []
    for suit_start in (WAN, TIAO, TONG, ZHONG):
        suit_end = suit_start + 9 if suit_start < ZHONG else SUIT
        for t in range(suit_start, suit_end):
            if hand_counts[t] > 0:
                parts.append(TILE_EMOJI[t] * hand_counts[t])
    s = " ".join(parts)
    if melds:
        mstr = "  ".join(_render_meld(m) for m in melds)
        s += "\n明牌：" + mstr
    return s


def _render_meld(m):
    kind, tile = m
    if kind == "pong":
        return TILE_EMOJI[tile] * 2 + "▫"  # 碰：两实一虚（简化显示）
    if kind in ("kong", "ankan"):
        return TILE_EMOJI[tile] * 4
    return TILE_EMOJI[tile]


# ----------------------------------------------------------------------------
# 胡牌 / 听牌判定
# ----------------------------------------------------------------------------
def _can_melds_count(counts, needed):
    """剩余牌能否恰好分解成 needed 个面子（刻子/顺子）。"""
    if needed == 0:
        return all(v == 0 for v in counts)
    i = next((k for k in range(SUIT) if counts[k] > 0), None)
    if i is None:
        return False
    # 刻子
    if counts[i] >= 3:
        counts[i] -= 3
        if _can_melds_count(counts, needed - 1):
            counts[i] += 3
            return True
        counts[i] += 3
    # 顺子（仅数牌，且非该花色最后两张）
    if i < 27 and (i % 9) <= 6 and counts[i + 1] > 0 and counts[i + 2] > 0:
        counts[i] -= 1
        counts[i + 1] -= 1
        counts[i + 2] -= 1
        if _can_melds_count(counts, needed - 1):
            counts[i] += 1
            counts[i + 1] += 1
            counts[i + 2] += 1
            return True
        counts[i] += 1
        counts[i + 1] += 1
        counts[i + 2] += 1
    return False


def is_win(hand_counts, melds=None):
    """胡牌判定：4 面子 + 1 将，或七对。

    melds 为已亮明的副露（碰/杠/暗杠）。有副露时暗手牌只需凑成
    (4 - len(melds)) 个面子 + 1 将，否则有副露的玩家永远胡不了。
    """
    if melds is None:
        melds = []
    n = len(melds)
    if n > 4:
        return False
    c = list(hand_counts)
    total = sum(c)
    need = 3 * (4 - n) + 2          # 暗手牌应凑成的面子数*3 + 将
    if total != need:
        return False
    # 七对：仅在没有副露时成立
    if n == 0 and total == 14 and all(c[k] in (0, 2) for k in range(SUIT)) \
            and sum(1 for k in range(SUIT) if c[k] == 2) == 7:
        return True
    # 枚举将
    for i in range(SUIT):
        if c[i] >= 2:
            c[i] -= 2
            ok = _can_melds_count(c, 4 - n)
            c[i] += 2
            if ok:
                return True
    return False


def is_ting(hand_counts, melds=None):
    """听牌判定：再摸任意一张后能胡（需考虑已有副露）。"""
    for t in range(SUIT):
        c = list(hand_counts)
        c[t] += 1
        if is_win(c, melds):
            return True
    return False


def _win_after_add(hand_counts, tile, melds=None):
    c = list(hand_counts)
    c[tile] += 1
    return is_win(c, melds)


# ----------------------------------------------------------------------------
# 番数计算
# ----------------------------------------------------------------------------
def calc_fan(hand_counts, melds, self_draw, kong_draw):
    fans = 1  # 鸡胡底
    suits = set()
    has_zi = False
    for t in range(SUIT):
        if hand_counts[t] > 0:
            if t < 27:
                suits.add(t // 9)
            else:
                has_zi = True
    for _, tile in melds:
        if tile < 27:
            suits.add(tile // 9)
        else:
            has_zi = True
    if has_zi and len(suits) == 1:
        fans += 1           # 混一色
    elif not has_zi and len(suits) == 1:
        fans += 2           # 清一色
    # 碰碰胡：手牌本身全为刻子+将，或 4 个明面子全是刻/杠
    hand_triplet = all(hand_counts[t] in (0, 2, 3) for t in range(SUIT)) and \
                   sum(1 for t in range(SUIT) if hand_counts[t] == 2) == 1
    melds_triplet = len(melds) == 4 and all(kind in ("pong", "kong", "ankan") for kind, _ in melds)
    if hand_triplet or melds_triplet:
        fans += 2           # 碰碰胡
    if self_draw:
        fans += 1           # 自摸
    if kong_draw:
        fans += 1           # 杠上花
    return min(fans, MAX_FAN)


# ----------------------------------------------------------------------------
# AI 出牌策略（核心：避免每局打同样的牌）
# ----------------------------------------------------------------------------
def ai_choose_discard(hand_counts, discards_seen, personality="normal"):
    """基于手牌评估每张暗牌的保留价值，打最低者；等价最低者随机选，保证不固定。"""
    candidates = [t for t in range(SUIT) if hand_counts[t] > 0]
    if not candidates:           # 手牌为空（异常态），交由调用方兜底流局
        return None
    scored = [( _tile_value(t, hand_counts, discards_seen, personality), t ) for t in candidates]
    min_v = min(v for v, _ in scored)
    lows = [t for v, t in scored if v == min_v]
    return random.choice(lows)   # 随机打破对称，确保每局不同


def _tile_value(t, hand_counts, discards_seen, personality):
    c = hand_counts[t]
    v = 0
    if c >= 3:
        v += 100          # 已成刻
    elif c == 2:
        v += 60           # 对子
    if t < 27:            # 数牌搭子
        r = t % 9
        if r >= 1 and hand_counts[t - 1] > 0:
            v += 40
        if r <= 7 and hand_counts[t + 1] > 0:
            v += 40
        if r >= 2 and hand_counts[t - 2] > 0:
            v += 25
        if r <= 6 and hand_counts[t + 2] > 0:
            v += 25
    if t >= 27:           # 字牌孤张最废
        v -= 10
    v += discards_seen.get(t, 0) * 2   # 场上已出现多次的牌更安全
    if personality == "aggressive":
        if c >= 2:
            v += 15
    elif personality == "conservative":
        if t >= 27:
            v -= 10
    return v


def ai_decide_claim(claims_self, hand_counts, personality="normal", melds=None):
    """电脑是否对别人打出的牌鸣牌。优先胡 > 杠 > 碰。"""
    if claims_self.get("win"):
        return "win"
    if personality == "conservative" and claims_self.get("pong"):
        # 保守型少碰，除非已听牌
        if not is_ting(hand_counts, melds):
            return "pass"
    if claims_self.get("kong"):
        return "kong"
    if claims_self.get("pong"):
        return "pong"
    return "pass"


# ----------------------------------------------------------------------------
# 牌局状态机
# ----------------------------------------------------------------------------
class MahjongGame:
    def __init__(self, cid, owner_uid):
        self.cid = cid
        self.owner_uid = owner_uid
        self.players = []          # [{uid,is_bot,hand,melds,discards}]
        self.phase = "waiting"      # waiting | playing | settling | finished
        self.wall = []
        self.turn = 0
        self.dealer_idx = 0
        self.last_discard = None    # (tile, from_uid)
        self.skip_draw = False      # 碰/杠后该玩家打牌不摸
        self.kong_draw = False      # 杠上花标记
        self.log = []
        self.result = None
        self._bot_seq = 0

    # ---- 玩家管理 ----
    def add_player(self, uid, is_bot=False):
        if any(p["uid"] == uid for p in self.players):
            return False
        self.players.append({
            "uid": uid, "is_bot": is_bot,
            "hand": [0] * SUIT, "melds": [], "discards": [],
        })
        return True

    def fill_bots(self):
        """补位电脑到 4 人；每台电脑性格不同，保证出牌差异。"""
        while len(self.players) < 4:
            self._bot_seq += 1
            bid = -9000 - self._bot_seq
            self.add_player(bid, is_bot=True)
            self.players[-1]["personality"] = BOT_PERSONALITIES[(len(self.players) - 1) % len(BOT_PERSONALITIES)]

    def _idx(self, uid):
        for i, p in enumerate(self.players):
            if p["uid"] == uid:
                return i
        return -1

    def _find(self, uid):
        i = self._idx(uid)
        return self.players[i] if i >= 0 else None

    def current(self):
        return self.players[self.turn]

    # ---- 开局 ----
    def start(self):
        if self.phase == "playing":
            return False, "本局已开始"
        if len(self.players) < 2:
            return False, "至少需要 2 人（含电脑补位）"
        self.fill_bots()
        if len(self.players) != 4:
            return False, "开局人数异常"
        self.wall = build_wall()
        for p in self.players:
            p["hand"] = [0] * SUIT
            p["melds"] = []
            p["discards"] = []
        for _ in range(13):
            for p in self.players:
                p["hand"][self.wall.pop()] += 1
        self.phase = "playing"
        self.turn = 0
        self.skip_draw = False
        self.kong_draw = False
        self.last_discard = None
        self.log = []
        return True, None

    # ---- 回合动作 ----
    def draw(self):
        if not self.wall:
            return None
        t = self.wall.pop()
        self.current()["hand"][t] += 1
        return t

    def can_self_win(self):
        p = self.current()
        return is_win(p["hand"], p["melds"])

    def discard(self, uid, tile):
        """当前玩家打牌。返回 True/False。"""
        if self.phase != "playing":
            return False
        if self.players[self.turn]["uid"] != uid:
            return False
        if self.players[self.turn]["hand"][tile] <= 0:
            return False
        self.players[self.turn]["hand"][tile] -= 1
        self.players[self.turn]["discards"].append(tile)
        self.last_discard = (tile, uid)
        self.skip_draw = False
        return True

    def get_claims(self):
        """别人打出 last_discard 后，其余玩家可鸣牌情况。"""
        if self.last_discard is None:
            return {}
        tile, from_uid = self.last_discard
        res = {}
        for p in self.players:
            if p["uid"] == from_uid:
                continue
            h = p["hand"]
            can_win = _win_after_add(h, tile, p["melds"])
            can_pong = h[tile] >= 2
            can_kong = h[tile] >= 3
            if can_win or can_pong or can_kong:
                res[p["uid"]] = {"win": can_win, "pong": can_pong, "kong": can_kong}
        return res

    def do_pong(self, uid, tile):
        p = self._find(uid)
        if p is None or p["hand"][tile] < 2:
            return False
        p["hand"][tile] -= 2
        p["melds"].append(("pong", tile))
        self.turn = self._idx(uid)
        self.skip_draw = True
        self.last_discard = None
        return True

    def do_kong(self, uid, tile):
        """明杠：手中有 3 张 + 别人打出 1 张。杠后必须补摸 1 张替换牌。"""
        p = self._find(uid)
        if p is None or p["hand"][tile] < 3:
            return False
        p["hand"][tile] -= 3
        p["melds"].append(("kong", tile))
        self.turn = self._idx(uid)
        self.skip_draw = True
        self.kong_draw = True
        self.last_discard = None
        if self.wall:                      # 补摸替换牌（否则手牌会越杠越少直至耗尽）
            r = self.wall.pop()
            p["hand"][r] += 1
        return True

    def do_win(self, uid, tile, self_draw):
        """结算胡牌（纯计算，不动积分）。"""
        winner = self._find(uid)
        if winner is None:
            return None
        hand = list(winner["hand"])
        if not self_draw:
            hand[tile] += 1
        if not is_win(hand, winner["melds"]):
            return None
        fans = calc_fan(hand, winner["melds"], self_draw, self.kong_draw)
        score = BASE_SCORE * fans
        self.result = {
            "winner": uid, "tile": tile, "self_draw": self_draw,
            "fans": fans, "score": score, "melds": list(winner["melds"]),
        }
        self.phase = "settling"
        return self.result

    def is_wall_empty(self):
        return len(self.wall) <= DRAW_RESERVE

    def advance(self):
        self.turn = (self.turn + 1) % len(self.players)
        self.skip_draw = False
        self.kong_draw = False

    def settle_draw(self):
        """流局结算（无输赢）。"""
        self.result = {"draw": True}
        self.phase = "settling"
        return self.result
