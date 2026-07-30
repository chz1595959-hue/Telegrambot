from aiogram import Router, F, Bot
from aiogram.types import Message, CallbackQuery
from aiogram.filters import Command
from game import PokerGame, Player
from keyboards import join_start_buttons, action_buttons
from treys import Card

router = Router()
games = {}

@router.message(Command("newgame"))
async def new_game(message: Message):
    chat_id = message.chat.id
    if chat_id in games:
        await message.reply("当前已有游戏，请先 /endgame 结束。")
        return
    games[chat_id] = PokerGame(chat_id)
    await message.reply("🃏 德州扑克！点击加入游戏。", reply_markup=join_start_buttons())

@router.message(Command("endgame"))
async def end_game(message: Message):
    chat_id = message.chat.id
    if games.pop(chat_id, None):
        await message.reply("🛑 游戏已结束，可以 /newgame 开新局。")
    else:
        await message.reply("当前没有游戏。")

@router.callback_query(F.data == "join_game")
async def join_game(callback: CallbackQuery):
    chat_id = callback.message.chat.id
    game = games.get(chat_id)
    if not game:
        await callback.answer("没有创建中的游戏，请 /newgame。", show_alert=True)
        return
    user = callback.from_user
    ok, msg = game.add_player(user.id, user.full_name)
    if ok:
        try:
            await callback.bot.send_message(user.id, "你已加入，游戏开始后会私发手牌。")
        except:
            pass
        names = ", ".join(p.name for p in game.players)
        await callback.message.edit_text(
            f"玩家 ({len(game.players)}人)：{names}\n点击开始游戏。",
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
        await callback.answer("无游戏。", show_alert=True)
        return
    ok, msg = game.start_game()
    if not ok:
        await callback.answer(msg, show_alert=True)
        return
    # 私发手牌
    for p in game.players:
        hand_str = " ".join(Card.int_to_pretty_str(c).replace('T','10') for c in p.hand)
        try:
            await callback.bot.send_message(p.user_id, f"你的手牌：{hand_str}")
        except:
            await callback.message.answer(f"无法私聊 {p.name}，请先给我发条消息。")
    await show_turn(callback.message, game)
    await callback.answer()

async def show_turn(message, game):
    cur = game.get_current_player()
    comm = " ".join(Card.int_to_pretty_str(c).replace('T','10') for c in game.community) if game.community else "无"
    text = (
        f"🃏 公共牌：{comm}\n"
        f"💰 底池：{game.pot}\n"
        f"💵 当前注：{game.current_bet}\n"
        f"🎯 轮到 @{cur.name} 行动"
    )
    kb = action_buttons(game.current_bet, cur.round_bet, cur.chips, game.min_raise)
    await message.edit_text(text, reply_markup=kb)

@router.callback_query(F.data.startswith("action_"))
async def handle_action(callback: CallbackQuery):
    chat_id = callback.message.chat.id
    game = games.get(chat_id)
    if not game:
        await callback.answer("游戏不存在。", show_alert=True)
        return
    uid = callback.from_user.id
    data = callback.data
    if data == "action_fold":
        ok, msg = game.process_action(uid, 'fold')
    elif data == "action_check":
        ok, msg = game.process_action(uid, 'check')
    elif data.startswith("action_call_"):
        amt = int(data.split("_")[2])
        ok, msg = game.process_action(uid, 'call', amt)
    elif data == "action_allin":
        ok, msg = game.process_action(uid, 'allin')
    elif data.startswith("action_raise_"):
        total = int(data.split("_")[2])
        ok, msg = game.process_action(uid, 'raise', total)
    elif data == "action_custom_raise":
        await callback.answer("请在私聊里输入 /raise 金额", show_alert=True)
        return
    else:
        await callback.answer("未知操作")
        return

    if not ok:
        await callback.answer(msg, show_alert=True)
        return

    # 游戏结束？
    if game.stage == 'showdown':
        winners, share = game.end_game()
        comm = " ".join(Card.int_to_pretty_str(c).replace('T','10') for c in game.community)
        text = f"🏆 摊牌！公共牌：{comm}\n"
        for p in game.players:
            hand = " ".join(Card.int_to_pretty_str(c).replace('T','10') for c in p.hand) if p.hand else ""
            text += f"{'✅' if not p.folded else '❌'} {p.name}: {hand} (筹码{p.chips})\n"
        text += f"\n赢家：{', '.join(w[0].name for w in winners)}，各得 {share} 筹码"
        await callback.message.edit_text(text)
        del games[chat_id]
    else:
        await show_turn(callback.message, game)
    await callback.answer()
