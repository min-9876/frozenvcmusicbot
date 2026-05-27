import os
import re
import sys
import time
import uuid
import json
import random
import logging
import tempfile
import threading
import subprocess
import psutil
from io import BytesIO
from datetime import datetime, timezone, timedelta
from threading import Thread
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import quote, urljoin
import aiohttp
import aiofiles
import asyncio
import requests
import isodate
import pymongo
from pymongo import MongoClient, ASCENDING
from bson import ObjectId
from bson.binary import Binary
from dotenv import load_dotenv
from flask import Flask, request
from PIL import Image, ImageDraw, ImageFont, ImageFilter
from pyrogram import Client, filters, errors
from pyrogram.enums import ChatType, ChatMemberStatus, ParseMode
from pyrogram.types import (
    Message,
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputMediaPhoto,
    ChatPermissions,
)
from pyrogram.errors import RPCError
from pytgcalls import PyTgCalls, idle
from pytgcalls.types import MediaStream
from pytgcalls import filters as fl
from pytgcalls.types import (
    ChatUpdate,
    UpdatedGroupCallParticipant,
    Update as TgUpdate,
)
from pytgcalls.types.stream import StreamEnded
from typing import Union
import urllib
from FrozenMusic.infra.concurrency.ci import deterministic_privilege_validator
from FrozenMusic.telegram_client.vector_transport import vector_transport_resolver
from FrozenMusic.infra.vector.yt_vector_orchestrator import yt_vector_orchestrator
from FrozenMusic.infra.vector.yt_backup_engine import yt_backup_engine
from FrozenMusic.infra.chrono.chrono_formatter import quantum_temporal_humanizer
from FrozenMusic.vector_text_tools import vectorized_unicode_boldifier
from FrozenMusic.telegram_client.startup_hooks import precheck_channels
from collections import deque

# 🔍 YouTube Search Library
from youtube_search import YoutubeSearch

load_dotenv()

API_ID = int(os.environ.get("API_ID"))
API_HASH = os.environ.get("API_HASH")
BOT_TOKEN = os.environ.get("BOT_TOKEN")
ASSISTANT_SESSION = os.environ.get("ASSISTANT_SESSION")
OWNER_ID = int(os.getenv("OWNER_ID", "8315544720"))

logging.getLogger("pyrogram").setLevel(logging.ERROR)
_original_resolve_peer = Client.resolve_peer
async def _safe_resolve_peer(self, peer_id):
    try:
        return await _original_resolve_peer(self, peer_id)
    except (KeyError, ValueError) as e:
        if "ID not found" in str(e) or "Peer id invalid" in str(e):
            return None
        raise
Client.resolve_peer = _safe_resolve_peer

def _custom_exception_handler(loop, context):
    exc = context.get("exception")
    if isinstance(exc, (KeyError, ValueError)) and (
        "ID not found" in str(exc) or "Peer id invalid" in str(exc)
    ):
        return  

    if isinstance(exc, AttributeError) and "has no attribute 'write'" in str(exc):
        return

    loop.default_exception_handler(context)

asyncio.get_event_loop().set_exception_handler(_custom_exception_handler)

session_name = os.environ.get("SESSION_NAME", "music_bot1")
bot = Client(session_name, bot_token=BOT_TOKEN, api_id=API_ID, api_hash=API_HASH)
assistant = Client("assistant_account", session_string=ASSISTANT_SESSION)
call_py = PyTgCalls(assistant)

ASSISTANT_USERNAME = None
ASSISTANT_CHAT_ID = None
API_ASSISTANT_USERNAME = os.getenv("API_ASSISTANT_USERNAME")

mongo_uri = os.environ.get("MongoDB_url")
mongo_client = MongoClient(mongo_uri)
db = mongo_client["music_bot"]

broadcast_collection  = db["broadcast"]
state_backup = db["state_backup"]

chat_containers = {}
playback_tasks = {}  
bot_start_time = time.time()
COOLDOWN = 10
chat_last_command = {}
chat_pending_commands = {}
QUEUE_LIMIT = 20
MAX_DURATION_SECONDS = 480  
LOCAL_VC_LIMIT = 10
playback_mode = {}

async def process_pending_command(chat_id, delay):
    await asyncio.sleep(delay)  
    if chat_id in chat_pending_commands:
        message, cooldown_reply = chat_pending_commands.pop(chat_id)
        await cooldown_reply.delete()  
        await play_handler(bot, message) 

async def skip_to_next_song(chat_id, message):
    if chat_id not in chat_containers or not chat_containers[chat_id]:
        await message.edit("❌ No more songs in the queue.")
        await leave_voice_chat(chat_id)
        return

    await message.edit("⏭ Skipping to the next song...")
    
    next_song_info = chat_containers[chat_id][0]
    try:
        await fallback_local_playback(chat_id, message, next_song_info)
    except Exception as e:
        print(f"Error starting next local playback: {e}")
        await bot.send_message(chat_id, f"❌ Failed to start next song: {e}")

def safe_handler(func):
    async def wrapper(*args, **kwargs):
        try:
            return await func(*args, **kwargs)
        except Exception as e:
            chat_id = "Unknown"
            try:
                if len(args) >= 2:
                    chat_id = args[1].chat.id
                elif "message" in kwargs:
                    chat_id = kwargs["message"].chat.id
            except Exception:
                chat_id = "Unknown"
            error_text = (
                f"Error in handler `{func.__name__}` (chat id: {chat_id}):\n\n{str(e)}"
            )
            print(error_text)
            await bot.send_message(5268762773, error_text)
    return wrapper

async def extract_invite_link(client, chat_id):
    try:
        chat_info = await client.get_chat(chat_id)
        if chat_info.invite_link:
            return chat_info.invite_link
        elif chat_info.username:
            return f"https://t.me/{chat_info.username}"
        return None
    except ValueError as e:
        if "Peer id invalid" in str(e):
            return None
        else:
            raise e  
    except Exception as e:
        return None

async def extract_target_user(message: Message):
    if message.reply_to_message:
        return message.reply_to_message.from_user.id

    parts = message.text.split()
    if len(parts) < 2:
        await message.reply("❌ You must reply to a user or specify their @username/user_id.")
        return None

    target = parts[1]
    if target.startswith("@"):
        target = target[1:]
    try:
        user = await message._client.get_users(target)
        return user.id
    except:
        await message.reply("❌ Could not find that user.")
        return None

async def is_assistant_in_chat(chat_id):
    try:
        member = await assistant.get_chat_member(chat_id, ASSISTANT_USERNAME)
        return member.status is not None
    except Exception as e:
        error_message = str(e)
        if "USER_BANNED" in error_message or "Banned" in error_message:
            return "banned"
        elif "USER_NOT_PARTICIPANT" in error_message or "Chat not found" in error_message:
            return False
        return False

async def is_api_assistant_in_chat(chat_id):
    try:
        member = await bot.get_chat_member(chat_id, API_ASSISTANT_USERNAME)
        return member.status is not None
    except Exception as e:
        return False
    
def iso8601_to_seconds(iso_duration):
    try:
        duration = isodate.parse_duration(iso_duration)
        return int(duration.total_seconds())
    except Exception:
        return 0

def iso8601_to_human_readable(iso_duration):
    try:
        duration = isodate.parse_duration(iso_duration)
        total_seconds = int(duration.total_seconds())
        hours, remainder = divmod(total_seconds, 3600)
        minutes, seconds = divmod(remainder, 60)
        if hours > 0:
            return f"{hours}:{minutes:02}:{seconds:02}"
        return f"{minutes}:{seconds:02}"
    except Exception:
        return "Unknown duration"

# 🛠️ ပြင်ဆင်ပြီးသား YouTube Search Function
async def fetch_youtube_link(query):
    try:
        loop = asyncio.get_event_loop()
        
        def search_without_cookie():
            # youtube-search library version အသစ်မှာ cookies parameter က error တက်စေလို့ ဖြုတ်လိုက်ပါတယ်
            return YoutubeSearch(query, max_results=1).to_dict()

        results = await loop.run_in_executor(None, search_without_cookie)
        
        if not results:
            raise Exception("No results found on YouTube")

        video = results[0]
        video_id = video["id"]
        video_url = f"https://www.youtube.com/watch?v={video_id}"
        title = video["title"]
        duration_str = video.get("duration", "0:00")
        
        if ":" in duration_str:
            parts = duration_str.split(":")
            if len(parts) == 2:
                duration_iso = f"PT{parts[0]}M{parts[1]}S"
            elif len(parts) == 3:
                duration_iso = f"PT{parts[0]}H{parts[1]}M{parts[2]}S"
            else:
                duration_iso = "PT3M"
        else:
            duration_iso = "PT3M"

        thumbnails = video.get("thumbnails", [])
        thumb = thumbnails[0] if thumbnails else "https://telegra.ph/file/default_thumb.jpg"

        return (video_url, title, duration_iso, thumb)

    except Exception as e:
        raise Exception(f"YouTube Search failed: {str(e)}")
    
async def fetch_youtube_link_backup(query):
    return await fetch_youtube_link(query)
    
BOT_NAME = os.environ.get("BOT_NAME", "HAN THAR")
BOT_LINK = os.environ.get("BOT_LINK", "https://t.me/MYANMAR_FM_BOT")

async def invite_assistant(chat_id, invite_link, processing_message):
    try:
        await assistant.join_chat(invite_link)
        return True
    except UserAlreadyParticipant:
        return True
    except RPCError as e:
        await processing_message.edit(f"❌ Error while inviting assistant: {e.error_message}")
        return False
    except Exception as e:
        await processing_message.edit(f"❌ Unexpected error: {str(e)}")
        return False

def to_bold_unicode(text: str) -> str:
    bold_text = ""
    for char in text:
        if 'A' <= char <= 'Z':
            bold_text += chr(ord('𝗔') + (ord(char) - ord('A')))
        elif 'a' <= char <= 'z':
            bold_text += chr(ord('𝗮') + (ord(char) - ord('a')))
        else:
            bold_text += char
    return bold_text

@bot.on_message(filters.command("start"))
async def start_handler(_, message):
    user_id = message.from_user.id
    raw_name = message.from_user.first_name or ""
    styled_name = to_bold_unicode(raw_name)
    user_link = f"[{styled_name}](tg://user?id={user_id})"

    add_me_text = to_bold_unicode("Add Me")
    updates_text = to_bold_unicode("Updates")
    support_text = to_bold_unicode("Support")
    help_text = to_bold_unicode("Help")

    updates_channel = os.getenv("UPDATES_CHANNEL", "https://t.me/myanmarbot_music")
    support_group = os.getenv("SUPPORT_GROUP", "https://t.me/myanmar_music_Bot2027")
    start_animation = os.getenv("START_ANIMATION", "https://files.catbox.moe/10hbxr.mp4")
    
    caption = (
        f"👋 нєу {user_link} 💠, 🥀\n\n"
        f">🎶 𝗪𝗘𝗟𝗖𝗢𝗠𝗘 𝗧𝗢 {BOT_NAME.upper()}! 🎵\n"
        ">🚀 𝗧𝗢𝗣-𝗡𝗢𝗧𝗖𝗛 24×7 𝗨𝗣𝗧𝗜𝗠𝗘 & 𝗦𝗨𝗣𝗣𝗢𝗥𝗧\n"
        ">🎧 𝗦𝗨𝗣𝗣𝗢𝗥𝗧𝗘𝗗 𝗣𝗟𝗔𝗧𝗙𝗢𝗥𝗠𝗦: YouTube | Spotify | SoundCloud\n"
        ">✨ 𝗔𝗨𝗧𝗢-𝗦𝗨𝗚𝗚𝗘𝗦𝗧𝗜𝗢𝗡𝗦 when queue ends\n"
        ">🛠️ 𝗔𝗗𝗠𝗜𝗡 𝗖𝗢𝗠𝗠𝗔𝗡𝗗𝗦: Pause, Resume, Skip, Stop\n"
        ">**အရာအားလုံးအကောင်းလို့ပဲ မြင်တယ်**\n"
        f"๏ ᴄʟɪᴄᴋ {help_text} ʙᴇʟᴏဝ ғᴏʀ ᴄOM𝗠𝗔𝗡𝗗 ʟɪsᴛ."
    )

    buttons = [
        [
            InlineKeyboardButton(f"➕ {add_me_text}", url=f"{BOT_LINK}?startgroup=true"),
            InlineKeyboardButton(f"📢 {updates_text}", url=updates_channel)
        ],
        [
            InlineKeyboardButton(f"💬 {support_text}", url=support_group),
            InlineKeyboardButton(f"❓ {help_text}", callback_data="show_help")
        ]
    ]
    await message.reply_animation(animation=start_animation, caption=caption, reply_markup=InlineKeyboardMarkup(buttons))

    chat_id = message.chat.id
    if message.chat.type == ChatType.PRIVATE:
        if not broadcast_collection.find_one({"chat_id": chat_id}):
            broadcast_collection.insert_one({"chat_id": chat_id, "type": "private"})

@bot.on_callback_query(filters.regex("^show_help$"))
async def show_help_callback(_, callback_query):
    help_text = ">📜 *Choose a category to explore commands:*"
    buttons = [
        [InlineKeyboardButton("🎵 Music Controls", callback_data="help_music"), InlineKeyboardButton("🛡️ Admin Tools", callback_data="help_admin")],
        [InlineKeyboardButton("🏠 Home", callback_data="go_back")]
    ]
    await callback_query.message.edit_text(help_text, parse_mode=ParseMode.MARKDOWN, reply_markup=InlineKeyboardMarkup(buttons))

@bot.on_callback_query(filters.regex("^go_back$"))
async def go_back_callback(_, callback_query):
    # (ဟိုဘက်က start caption အတိုင်း ပြန်ထည့်ပေးရပါမယ်)
    await callback_query.answer("Returning to main menu...")

@bot.on_message(filters.group & filters.regex(r'^/play(?:@\w+)?(?:\s+(?P<query>.+))?$'))
async def play_handler(_, message: Message):
    chat_id = message.chat.id
    match = message.matches[0]
    query = (match.group('query') or "").strip()

    if not query and not message.reply_to_message:
        await message.reply("❌ Please provide a song name or reply to an audio file.")
        return

    await process_play_command(message, query)

async def process_play_command(message: Message, query: str):
    chat_id = message.chat.id
    processing_message = await message.reply("❄️")

    # YouTube Search
    try:
        result = await fetch_youtube_link(query)
    except Exception as e:
        await processing_message.edit(f"❌ Search Error: {str(e)}")
        return

    video_url, title, duration_iso, thumb = result
    secs = isodate.parse_duration(duration_iso).total_seconds()
    readable = iso8601_to_human_readable(duration_iso)

    chat_containers.setdefault(chat_id, [])
    chat_containers[chat_id].append({
        "url": video_url,
        "title": title,
        "duration": readable,
        "duration_seconds": secs,
        "requester": message.from_user.first_name if message.from_user else "Unknown",
        "thumbnail": thumb
    })

    if len(chat_containers[chat_id]) == 1:
        await fallback_local_playback(chat_id, processing_message, chat_containers[chat_id][0])
    else:
        await processing_message.edit(f"✅ Added to queue: **{title}**")

async def fallback_local_playback(chat_id: int, message: Message, song_info: dict):
    playback_mode[chat_id] = "local"
    try:
        video_url = song_info.get("url")
        media_path = await vector_transport_resolver(video_url)
        
        await call_py.play(chat_id, MediaStream(media_path, video_flags=MediaStream.Flags.IGNORE))
        
        caption = f"🎧 **Now Playing**\n\n📌 **Title:** {song_info['title']}\n👤 **By:** {song_info['requester']}"
        await message.reply_photo(photo=song_info['thumbnail'], caption=caption)
        await message.delete()

    except Exception as e:
        await bot.send_message(chat_id, f"❌ Playback Error: {e}")

@bot.on_message(filters.group & filters.command(["stop", "end"]))
async def stop_handler(_, message):
    if not await deterministic_privilege_validator(message): return
    chat_id = message.chat.id
    try:
        await call_py.leave_call(chat_id)
        chat_containers.pop(chat_id, None)
        await message.reply("⏹ Stopped and cleared queue.")
    except:
        await message.reply("❌ Bot is not in VC.")

@bot.on_message(filters.command("ping"))
async def ping_handler(_, message):
    start = time.time()
    msg = await message.reply("Pinging...")
    end = time.time()
    await msg.edit(f"🏓 **Pong!**\nLatency: {round((end - start) * 1000)}ms")

# --- Bot အသက်သွင်းခြင်း ---
if __name__ == "__main__":
    print("→ Starting PyTgCalls client...")
    call_py.start()
    
    print("→ Starting Bot client...")
    bot.start()
    
    #  ဒီနေရာကို စစ်ဆေးပြီးမှ start လုပ်အောင် ပြင်လိုက်ပါတယ်
    if not assistant.is_connected:
        print("→ Starting Assistant client...")
        assistant.start()
    else:
        print("ℹ️ Assistant is already connected.")

    print("✅ Bot is online!")
    idle()

