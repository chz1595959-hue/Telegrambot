from aiogram import Router, F, Bot
from aiogram.types import Message, CallbackQuery
from aiogram.filters import Command
from game import PokerGame, Player
from keyboards import join_start_buttons, action_buttons, hand_view_button
from treys import Card

router = Router()
games = {}  # chat_id -> PokerGame

@router.message(Command("newgame"))
async def new_game(message: Message):
    chat_id = message.chat.id
    if chat_id in games:
        await message.reply("当前已有进行中的游戏，请先结束再创建。")
        return
    games[chat_id] = PokerGame(chat_id)
    await message.reply("🃏 德州扑克新一局！请点击加入游戏（至少2人）。", reply_markup=join_start_buttons())

@router.callback_query(F.data == "join_game")
async def join_game(callback: CallbackQuery):
    chat_id = callback.message.chat.id
    game = games.get(chat_id)
    if not game:
        await callback.answer("没有正在创建的游戏，请先使用 /newgame。", show_alert=True)
        return
    user = callback.from_user
    success, msg = game.add_player(user.id, user.full_name)
    if success:
        # 私聊通知
        try:
            await callback.bot.send_message(user.id, "你已加入游戏，游戏开始后会私发手牌。")
        except:
            pass
        # 更新群消息
        player_names = ", ".join(p.name for p in game.players)
        await callback.message.edit_text(
            f"当前玩家 ({len(game.players)}人)：{player_names}\n点击「开始游戏」开始。",
            reply_markup=join_start_buttons()
        )
    else:
        await callback.answer(msg, show_alert=True)
    await callback.answer()

@router.callback_query(F.data == "start_game")
async def start_game(callback: CallbackQuery):
    chat_id = callback.message.chat.id
    game = games.get(chat_id)
    if not game:
        await callback.answer("游戏不存在。", show_alert=True)
        return
    success, msg = game.start_game()
    if not success:
        await callback.answer(msg, show_alert=True)
        return
    # 私聊发手牌
    for p in game.players:
        hand_str = " ".join(Card.int_to_pretty_str(c) for c in p.hand)
        try:
            await callback.bot.send_message(p.user_id, f"你的手牌：{hand_str}")
        except:
            await callback.message.answer(f"无法私聊 {p.name}，请确保已对机器人发送过消息。")
    # 群内发当前轮次信息
    await show_turn_message(callback.message, game)
    await callback.answer()

async def show_turn_message(message, game: PokerGame):
    cur = game.get_current_player()
    community_str = " ".join(Card.int_to_pretty_str(c) for c in game.community) if game.community else "无"
    text = (
        f"🃏 公共牌：{community_str}\n"
        f"💰 底池：{game.pot}\n"
        f"💵 当前下注：{game.current_bet}\n"
        f"🎯 轮到 @{cur.name} 行动"
    )
    kb = action_buttons(game.current_bet, cur.current_round_bet, cur.chips, game.min_raise)
    await message.edit_text(text, reply_markup=kb)

@router.callback_query(F.data.startswith("action_"))
async def handle_action(callback: CallbackQuery):
    chat_id = callback.message.chat.id
    game = games.get(chat_id)
    if not game:
        await callback.answer("游戏不存在。", show_alert=True)
        return
    user_id = callback.from_user.id
    data = callback.data
    # 解析动作
    if data == "action_fold":
        success, msg = game.process_action(user_id, 'fold')
    elif data == "action_check":
        success, msg = game.process_action(user_id, 'check')
    elif data.startswith("action_call_"):
        amount = int(data.split("_")[2])
        success, msg = game.process_action(user_id, 'call', amount)
    elif data == "action_allin":
        success, msg = game.process_action(user_id, 'allin')
    elif data.startswith("action_raise_"):
        total = int(data.split("_")[2])
        success, msg = game.process_action(user_id, 'raise', total)
    else:
        await callback.answer("未知操作")
        return

    if not success:
        await callback.answer(msg, show_alert=True)
        return

    # 检查游戏是否结束
    if game.stage == 'showdown':
        winners, share = game.end_game()
        # 展示结果
        result_text = "🏆 摊牌！\n"
        for p in game.players:
            hand_str = " ".join(Card.int_to_pretty_str(c) for c in p.hand) if p.hand else ""
            result_text += f"{'✅' if not p.folded else '❌'} {p.name}: {hand_str}  (筹码剩余 {p.chips})\n"
        result_text += f"\n赢家：{', '.join(w[0].name for w in winners)}，赢得 {share} 筹码"
        await callback.message.edit_text(result_text)
        # 删除游戏实例
        del games[chat_id]
    else:
        # 如果轮次刚切换（发了公共牌），需要发送新消息
        if game.stage in ['flop', 'turn', 'river'] and game.current_bet == 0:
            # 新阶段，发送带公共牌的新消息
            await show_turn_message(callback.message, game)
        else:
            # 还是在同一消息上更新
            await show_turn_message(callback.message, game)
    await callback.answer()

# 私聊查看手牌
@router.callback_query(F.data == "view_hand")
async def view_hand(callback: CallbackQuery):
    user_id = callback.from_user.id
    # 在所有游戏中查找该玩家
    for game in games.values():
        for p in game.players:
            if p.user_id == user_id:
                hand_str = " ".join(Card.int_to_pretty_str(c) for c in p.hand)
                await callback.answer(f"你的手牌：{hand_str}", show_alert=True)
                return
    await callback.answer("你不在游戏中。", show_alert=True)
