from aiogram.types import InlineKeyboardMarkup, InlineKeyboardButton

def join_start_buttons():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="加入游戏", callback_data="join_game")],
        [InlineKeyboardButton(text="开始游戏", callback_data="start_game")]
    ])

def action_buttons(current_bet: int, player_round_bet: int, player_chips: int, min_raise: int):
    """根据当前局面生成操作按钮"""
    buttons = []
    call_amount = current_bet - player_round_bet
    # 过牌/跟注
    if call_amount <= 0:
        buttons.append([InlineKeyboardButton(text="过牌", callback_data="action_check")])
    else:
        actual_call = min(call_amount, player_chips)
        buttons.append([InlineKeyboardButton(text=f"跟注 {actual_call}", callback_data=f"action_call_{actual_call}")])

    # 加注按钮（预设几个倍数）
    if player_chips > call_amount:
        # 加注到当前下注额 + min_raise 或 2倍大盲
        raise_options = [min_raise, 2*min_raise, 3*min_raise]
        if current_bet == 0:
            raise_options = [10, 20, 50]  # 默认
        row = []
        for r in raise_options:
            total = current_bet + r
            if total <= player_chips + player_round_bet:
                row.append(InlineKeyboardButton(text=f"加 {r}", callback_data=f"action_raise_{total}"))
        if row:
            buttons.append(row)
        # 自定义加注
        buttons.append([InlineKeyboardButton(text="自定义加注", callback_data="action_custom_raise")])
        # 全下
        buttons.append([InlineKeyboardButton(text="All-in", callback_data="action_allin")])

    # 弃牌
    buttons.append([InlineKeyboardButton(text="弃牌", callback_data="action_fold")])

    return InlineKeyboardMarkup(inline_keyboard=buttons)

def hand_view_button():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="查看我的手牌", callback_data="view_hand")]
    ])
