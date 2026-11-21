# -*- coding: utf-8 -*-
"""
================================================================================
 课堂单词喊麦器 · Word Shouter（电竞风格单文件版 · 三模式 · 稳定版）
================================================================================
 用途：面向英语 / 语文老师的课堂节奏领读工具，支持三种模式：
   · 英语变位模式：大标题显示中文释义，三宫格展示「原型 / 过去式 / 过去分词」。
   · 基础英语模式：四宫格显示同一个英文单词，大标题显示中文释义。
   · 语文词汇模式：大标题显示「词汇 - 拼音」，四宫格显示当前词汇。
   三种模式下，方框每次亮起都会从「左侧自定义颜色列表」里随机取色。

 本次重点修复 / 补全：
   1. 四宫格严格锁定为 2x2 矩阵：无论「朗读次数」设为多少，格子数量不变，
      文字永远显示当前单词，动画只在格子里循环高亮，绝不增加/变形/越界。
   2. 大字自适应边界：超大字体按长度缩放 + 自动换行，始终居中完整显示。
   3. 鼓点音色：winsound.Beep 三种明显不同的音色（低沉 / 高频破音 / 清脆）。
   4. 背景音乐：导入 .mp3/.wav，开始喊麦时循环播放，音量低于人声与鼓点。
   5. 全屏按钮 + F11 快捷键。
   6. 全屏只隐藏左侧控制面板，让大字 + 四宫格铺满屏幕；ESC 或按钮退出。

 技术要点：
   · UI     : customtkinter（暗色 / 电竞霓虹风格）
   · 发音   : pyttsx3（后台线程 + runAndWait，绝不阻塞 UI）
   · 鼓点   : winsound.Beep 模拟三种鼓点音色
   · 音乐   : pygame.mixer 播放 .mp3/.wav（低音量循环）
   · 数据   : openpyxl 读取 .xlsx，纯文本读取 .txt，自动识别新旧格式与模式

 依赖安装（Windows）：
     pip install customtkinter pyttsx3 openpyxl pygame

 打包成 exe（PyInstaller）：
     pyinstaller -F -w -n WordShouter word_shouter.py
     （建议加 --collect-all customtkinter，确保暗色主题资源被打包进去）
================================================================================
"""

import json
import os
import random
import re
import queue
import threading
import time
import tkinter as tk
from tkinter import filedialog, messagebox, colorchooser

# 依赖缺失时给出友好提示，避免打包后双击闪退无任何信息
try:
    import customtkinter as ctk
except ImportError:
    raise SystemExit("缺少依赖 customtkinter，请先执行：pip install customtkinter")

try:
    import pyttsx3
except ImportError:
    raise SystemExit("缺少依赖 pyttsx3，请先执行：pip install pyttsx3")

try:
    import openpyxl
except ImportError:
    raise SystemExit("缺少依赖 openpyxl，请先执行：pip install openpyxl")


# ------------------------------------------------------------------------------
# 颜色 / 风格常量（电竞深空黑蓝 + 霓虹蓝 + 金色）
# ------------------------------------------------------------------------------
COLOR_BG          = "#050510"   # 主背景：深空黑蓝
COLOR_SIDEBAR     = "#0d0d1f"   # 侧边栏 / 状态栏 / 底部控制栏背景
COLOR_CARD        = "#131326"   # 侧边栏内卡片背景
COLOR_CELL_IDLE   = "#1a1a30"   # 方框未点亮时的背景
COLOR_NEON        = "#00E5FF"   # 霓虹蓝（高亮色 1 / 随机取色的兜底色）
COLOR_GOLD        = "#FFD60A"   # 金色（高亮色 2，用于核心大字 / 强调）
COLOR_TEXT        = "#EAF2FF"   # 主文字
COLOR_TEXT_DIM    = "#8b93b0"   # 次要文字
COLOR_BTN_DARK    = "#1f2937"   # 深色按钮

# 闪烁颜色列表的预设色（电竞霓虹系，可多选/取消）
PRESET_FLASH_COLORS = ["#00E5FF", "#FFD60A", "#39FF14", "#FF2D95", "#B388FF", "#FF6B35"]

# 大标题使用的中文字体，Windows 自带、含中英文字形
BIG_FONT_FAMILY = "Microsoft YaHei UI"

# 鼓点音色可选列表
DRUM_STYLES = ["标准底鼓", "重金属摇滚", "军鼓拍手"]

# 模式相关常量
MODE_LABELS = {"en": "英语变位模式", "zh": "语文词汇模式", "basic": "基础英语模式"}
MODE_KEYS = {"英语变位模式": "en", "语文词汇模式": "zh", "基础英语模式": "basic"}

# 表头关键字（导入时自动跳过表头行）
HEADER_KEYS = {"word", "english", "base", "原型", "单词", "英文",
               "词汇", "词语", "汉字", "拼音", "释义"}

# 参数边界
BPM_MIN, BPM_MAX = 40, 240      # BPM 范围
READ_COUNT_MAX = 10             # 朗读次数上限（只控制高亮循环次数，不改变格子数）
BGM_VOLUME = 0.2                # 背景音乐音量（低于人声与鼓点）


def _has_cjk(s: str) -> bool:
    """判断字符串里是否包含中文字符（用于自动识别语文词汇数据）。"""
    return any('\u4e00' <= ch <= '\u9fff' for ch in s)


# ------------------------------------------------------------------------------
# 鼓点音效播放器（用 winsound.Beep 的不同频率模拟三种鼓点音色）
# ------------------------------------------------------------------------------
class DrumPlayer:
    """鼓点音效播放器（Windows 兼容）。

    用 winsound.Beep(frequency, duration) 用「不同频率/音高」模拟三种鼓点，
    三种音色区别非常明显。winsound.Beep 会阻塞当前线程，因此放到独立线程执行。
    """

    _PATTERNS = {
        "标准底鼓": [(120, 110)],                 # 低沉长音
        "重金属摇滚": [(1800, 45), (2600, 45)],     # 高频破音，快速两连击
        "军鼓拍手": [(1000, 35)],                  # 清脆短促
    }

    def __init__(self, fallback_beep=None):
        self._winsound = None
        try:
            import winsound
            self._winsound = winsound
        except ImportError:
            pass  # 非 Windows 平台
        self._fallback_beep = fallback_beep

    def play(self, style="标准底鼓"):
        """播放一次指定音色的鼓点。"""
        if self._winsound is None:
            if self._fallback_beep is not None:
                try:
                    self._fallback_beep()
                except Exception:
                    pass
            return

        pattern = self._PATTERNS.get(style, self._PATTERNS["标准底鼓"])

        def _run():
            try:
                for freq, dur in pattern:
                    self._winsound.Beep(freq, dur)
            except Exception as e:
                print("[鼓点] Beep 播放失败：", e)

        threading.Thread(target=_run, daemon=True).start()


# ------------------------------------------------------------------------------
# 后台语音引擎（pyttsx3 的初始化与 runAndWait 全部放在独立线程中）
# ------------------------------------------------------------------------------
class SpeechEngine:
    """负责所有发音的后台线程封装。

    pyttsx3 的 runAndWait() 会阻塞调用线程，所以常驻一个后台线程独占引擎，
    主线程只往队列里丢任务。额外提供：
       · speak_and_wait()：供「后台线程」同步朗读并等待完全结束
       · interrupt()：立即强制切断当前发音（高 BPM 防重叠）
       · is_busy()：查询是否正在朗读
    """

    _STOP = ("__STOP__",)  # 哨兵：通知后台线程打断当前发音

    def __init__(self, pause_event: threading.Event):
        self._queue = queue.Queue()              # 条目 = (texts, rate, done_event_or_None)
        self._pause_event = pause_event          # 暂停信号（set = 暂停）
        self._abort = threading.Event()          # 打断信号
        self._busy = threading.Event()           # 正在 runAndWait 中
        self._en_voice = None
        self._zh_voice = None
        self._engine = None
        self._thread = threading.Thread(target=self._worker,
                                        name="SpeechWorker",
                                        daemon=True)
        self._thread.start()

    # ------------------------------------------------------------------ 语音匹配
    @staticmethod
    def _find_voice(voices, lang: str):
        def lower(s):
            return (s or "").lower()

        for v in voices:
            langs = [lower(x) for x in (getattr(v, "languages", None) or [])]
            name = lower(getattr(v, "name", ""))
            vid = lower(getattr(v, "id", ""))
            if lang == "en":
                if (any(l.startswith("en") for l in langs)
                        or "english" in name
                        or "en-us" in vid or "en_gb" in vid or "en_au" in vid):
                    return v.id
            else:
                if (any(l.startswith("zh") for l in langs)
                        or "chinese" in name
                        or "中文" in (getattr(v, "name", "") or "")
                        or "zh-cn" in vid or "zh_cn" in vid
                        or "zh-hk" in vid or "zh-tw" in vid
                        or "2052" in vid):
                    return v.id
        return voices[0].id if voices else None

    # ------------------------------------------------------------------ 后台循环
    def _worker(self):
        try:
            self._engine = pyttsx3.init()
            voices = self._engine.getProperty("voices")
            self._en_voice = self._find_voice(voices, "en")
            self._zh_voice = self._find_voice(voices, "zh")
            self._engine.setProperty("volume", 1.0)   # 人声满音量，确保高于背景音乐
        except Exception as e:
            print("[语音] 引擎初始化失败：", e)
            self._engine = None

        while True:
            item = self._queue.get()
            if item is None:
                break
            if item == self._STOP:
                self._stop_now()
                self._abort.clear()
                continue

            texts, rate, done = item

            while self._pause_event.is_set() and not self._abort.is_set():
                self._pause_event.wait(timeout=0.05)
            if self._abort.is_set():
                self._abort.clear()
                if done is not None:
                    done.set()
                continue

            if self._engine is None:
                if done is not None:
                    done.set()
                continue

            try:
                self._engine.setProperty("rate", rate)
                for text, lang in texts:
                    vid = self._en_voice if lang == "en" else self._zh_voice
                    if vid:
                        self._engine.setProperty("voice", vid)
                    self._engine.say(text)
                self._busy.set()
                self._engine.runAndWait()
            except Exception as e:
                print("[语音] 发音失败：", e)
            finally:
                self._busy.clear()
                if done is not None:
                    done.set()

    def _stop_now(self):
        if self._engine is None:
            return
        try:
            self._engine.stop()
        except Exception:
            pass

    # ------------------------------------------------------------------ 对外接口
    def speak(self, texts, rate=175):
        """入队一段发音（非阻塞）。texts: [(文本, 'en'/'zh'), ...]"""
        self._queue.put((texts, rate, None))

    def speak_and_wait(self, texts, rate=175):
        """在【调用线程】内同步朗读并等待完全结束。仅供后台线程调用。"""
        done = threading.Event()
        self._queue.put((texts, rate, done))
        done.wait(timeout=30)

    def is_busy(self) -> bool:
        return self._busy.is_set()

    def clear(self):
        """清空尚未发音的队列，并释放其中带完成事件的任务。"""
        while True:
            try:
                item = self._queue.get_nowait()
            except queue.Empty:
                break
            if isinstance(item, tuple) and len(item) == 3 and item[2] is not None:
                item[2].set()

    def interrupt(self):
        """立即强制切断当前发音（高 BPM 防重叠）。"""
        self.clear()
        if self._engine is not None:
            try:
                self._engine.stop()
            except Exception:
                pass
        self._busy.clear()

    def stop(self):
        """停止：打断当前发音并清空队列（用于“重置”）。"""
        self._abort.set()
        self.clear()
        self._stop_now()
        self._queue.put(self._STOP)

    def shutdown(self):
        self._abort.set()
        self.clear()
        self._queue.put(None)


# ------------------------------------------------------------------------------
# 主窗口
# ------------------------------------------------------------------------------
class WordShouterApp(ctk.CTk):
    SPEAK_RATE = 175     # 朗读语速

    def __init__(self):
        super().__init__()
        ctk.set_appearance_mode("dark")

        self.title("课堂单词喊麦器 · Word Shouter")
        self.geometry("1280x800")
        self.minsize(1024, 700)
        self.configure(fg_color=COLOR_BG)

        # ---------------- 运行状态 ----------------
        self.mode = "en"                 # "en" / "zh" / "basic"
        self.words = []                  # {"base","past","pp","meaning","word","pinyin"}
        self.bpm = 112                   # 当前 BPM（40~240）
        self.voice_on = False            # 人声领读（默认关）
        self.drum_on = True              # 鼓点音效（默认开）
        self.drum_style = DRUM_STYLES[0]
        self.show_chinese = True         # 显示中文释义（英语类模式生效）
        self.repeat_count = 4            # 朗读次数 1~10（只控制高亮循环次数）
        self.font_size = 96              # 大标题基础字号
        self.flash_colors = list(PRESET_FLASH_COLORS)
        self.running = False
        self.paused = False
        self.fullscreen = False
        self.current_index = 0
        self.beat_index = 0
        self._after_id = None
        self._flash_started = False      # 当前词条的闪烁动画是否已开始（配合先读后闪）

        # 背景音乐 / 配置记忆
        self.bgm_path = None
        self._pygame = None
        self._music_config = self._load_config()

        self.pause_event = threading.Event()
        self._ui_queue = queue.Queue()   # 后台线程 → 主线程 的消息队列

        self.speech = SpeechEngine(self.pause_event)
        self.drum_player = DrumPlayer(fallback_beep=self.bell)

        self._build_ui()

        self.bind("<F11>", self._toggle_fullscreen)
        self.bind("<Escape>", self._on_escape)

        self.after(50, self._poll_ui_queue)

        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ==========================================================================
    # 配置记忆（config.json）
    # ==========================================================================
    def _load_config(self):
        try:
            with open("config.json", "r", encoding="utf-8") as f:
                data = json.loads(f.read())
                return data if isinstance(data, dict) else {}
        except Exception:
            return {}

    def _save_config(self):
        try:
            with open("config.json", "w", encoding="utf-8") as f:
                f.write(json.dumps(self._music_config, ensure_ascii=False, indent=2))
        except Exception as e:
            print("[配置] 保存失败：", e)

    # ==========================================================================
    # 界面构建
    # ==========================================================================
    def _build_ui(self):
        self.grid_columnconfigure(0, weight=0, minsize=320)
        self.grid_columnconfigure(1, weight=1)
        self.grid_rowconfigure(0, weight=1)

        self._build_sidebar()
        self._build_main()

    # ------------------------------------------------ 左侧控制边栏
    def _build_sidebar(self):
        self.sidebar = ctk.CTkFrame(self, fg_color=COLOR_SIDEBAR,
                                    corner_radius=0, width=320)
        self.sidebar.grid(row=0, column=0, sticky="nsew")
        self.sidebar.grid_propagate(False)

        ctk.CTkLabel(self.sidebar, text="⚡ 单词喊麦器",
                     font=ctk.CTkFont(size=24, weight="bold"),
                     text_color=COLOR_GOLD).pack(pady=(22, 2))
        ctk.CTkLabel(self.sidebar, text="WORD SHOUTER · MULTI MODE",
                     font=ctk.CTkFont(size=11),
                     text_color=COLOR_TEXT_DIM).pack(pady=(0, 14))

        # ---- 模式选择区 ----
        card0 = ctk.CTkFrame(self.sidebar, fg_color=COLOR_CARD, corner_radius=14)
        card0.pack(fill="x", padx=20, pady=(0, 10))
        ctk.CTkLabel(card0, text="模式选择",
                     font=ctk.CTkFont(size=15, weight="bold"),
                     text_color=COLOR_NEON).pack(anchor="w", padx=16, pady=(12, 4))
        self.mode_menu = ctk.CTkOptionMenu(
            card0, values=[MODE_LABELS["en"], MODE_LABELS["zh"], MODE_LABELS["basic"]],
            command=self._on_mode_change,
            height=34, corner_radius=10,
            fg_color=COLOR_BTN_DARK, button_color="#0ea5e9",
            button_hover_color="#38bdf8",
            text_color=COLOR_TEXT, font=ctk.CTkFont(size=14, weight="bold"),
            dropdown_fg_color=COLOR_CARD, dropdown_text_color=COLOR_TEXT,
            dropdown_hover_color=COLOR_BTN_DARK)
        self.mode_menu.set(MODE_LABELS["en"])
        self.mode_menu.pack(fill="x", padx=16, pady=(2, 12))

        # ---- 数据导入区 ----
        card1 = ctk.CTkFrame(self.sidebar, fg_color=COLOR_CARD, corner_radius=14)
        card1.pack(fill="x", padx=20, pady=(0, 10))
        ctk.CTkLabel(card1, text="数据导入",
                     font=ctk.CTkFont(size=15, weight="bold"),
                     text_color=COLOR_NEON).pack(anchor="w", padx=16, pady=(12, 4))
        ctk.CTkButton(card1, text="＋ 导入 .xlsx / .txt", height=44,
                      font=ctk.CTkFont(size=15, weight="bold"),
                      fg_color=COLOR_GOLD, hover_color="#FFC300",
                      text_color="#111111", corner_radius=10,
                      command=self._on_import).pack(fill="x", padx=16, pady=(2, 6))
        self.import_status = ctk.CTkLabel(card1, text="已导入 0 条",
                                          font=ctk.CTkFont(size=13),
                                          text_color=COLOR_TEXT_DIM)
        self.import_status.pack(anchor="w", padx=16, pady=(2, 12))

        # ---- 参数设置区 ----
        card2 = ctk.CTkFrame(self.sidebar, fg_color=COLOR_CARD, corner_radius=14)
        card2.pack(fill="x", padx=20, pady=(0, 10))
        card2.grid_columnconfigure(0, weight=1)
        _r = 0
        ctk.CTkLabel(card2, text="参数设置",
                     font=ctk.CTkFont(size=15, weight="bold"),
                     text_color=COLOR_NEON).grid(row=_r, column=0, sticky="w",
                                                 padx=16, pady=(12, 4)); _r += 1

        # BPM（40~240）
        bpm_row = ctk.CTkFrame(card2, fg_color="transparent")
        bpm_row.grid(row=_r, column=0, sticky="ew", padx=16, pady=(6, 0)); _r += 1
        ctk.CTkLabel(bpm_row, text="BPM 速度",
                     font=ctk.CTkFont(size=13),
                     text_color=COLOR_TEXT).pack(side="left")
        self.bpm_value = ctk.CTkLabel(bpm_row, text="112",
                                      font=ctk.CTkFont(size=16, weight="bold"),
                                      text_color=COLOR_GOLD)
        self.bpm_value.pack(side="right")
        self.bpm_slider = ctk.CTkSlider(card2, from_=BPM_MIN, to=BPM_MAX,
                                        number_of_steps=(BPM_MAX - BPM_MIN),
                                        command=self._on_bpm_change)
        self.bpm_slider.set(self.bpm)
        self.bpm_slider.grid(row=_r, column=0, sticky="ew", padx=16, pady=(6, 8)); _r += 1

        # 朗读次数（1~10，只控制高亮循环次数，不改变格子数）
        read_row = ctk.CTkFrame(card2, fg_color="transparent")
        read_row.grid(row=_r, column=0, sticky="ew", padx=16, pady=(0, 0)); _r += 1
        ctk.CTkLabel(read_row, text="朗读次数",
                     font=ctk.CTkFont(size=13),
                     text_color=COLOR_TEXT).pack(side="left")
        self.read_count_value = ctk.CTkLabel(read_row, text="4",
                                             font=ctk.CTkFont(size=16, weight="bold"),
                                             text_color=COLOR_GOLD)
        self.read_count_value.pack(side="right")
        self.read_count_slider = ctk.CTkSlider(card2, from_=1, to=READ_COUNT_MAX,
                                               number_of_steps=(READ_COUNT_MAX - 1),
                                               command=self._on_read_count_change)
        self.read_count_slider.set(self.repeat_count)
        self.read_count_slider.grid(row=_r, column=0, sticky="ew", padx=16, pady=(6, 8)); _r += 1

        # 字体大小
        font_row = ctk.CTkFrame(card2, fg_color="transparent")
        font_row.grid(row=_r, column=0, sticky="ew", padx=16, pady=(0, 0)); _r += 1
        ctk.CTkLabel(font_row, text="字体大小",
                     font=ctk.CTkFont(size=13),
                     text_color=COLOR_TEXT).pack(side="left")
        self.font_value = ctk.CTkLabel(font_row, text="96",
                                       font=ctk.CTkFont(size=16, weight="bold"),
                                       text_color=COLOR_GOLD)
        self.font_value.pack(side="right")
        self.font_slider = ctk.CTkSlider(card2, from_=48, to=160, number_of_steps=112,
                                         command=self._on_font_change)
        self.font_slider.set(self.font_size)
        self.font_slider.grid(row=_r, column=0, sticky="ew", padx=16, pady=(6, 8)); _r += 1

        # 鼓点音效开关
        self.drum_switch = ctk.CTkSwitch(card2, text="鼓点音效",
                                         font=ctk.CTkFont(size=14),
                                         progress_color=COLOR_NEON,
                                         command=self._on_drum_toggle)
        self.drum_switch.select()
        self.drum_switch.grid(row=_r, column=0, sticky="w", padx=16, pady=(2, 4)); _r += 1

        # 鼓点音色选择
        drum_style_row = ctk.CTkFrame(card2, fg_color="transparent")
        drum_style_row.grid(row=_r, column=0, sticky="ew", padx=16, pady=(0, 6)); _r += 1
        ctk.CTkLabel(drum_style_row, text="鼓点音色",
                     font=ctk.CTkFont(size=13),
                     text_color=COLOR_TEXT).pack(side="left")
        self.drum_style_menu = ctk.CTkOptionMenu(
            drum_style_row, values=DRUM_STYLES, command=self._on_drum_style_change,
            width=140, height=28, corner_radius=8,
            fg_color=COLOR_BTN_DARK, button_color="#0ea5e9",
            button_hover_color="#38bdf8",
            text_color=COLOR_TEXT, font=ctk.CTkFont(size=13),
            dropdown_fg_color=COLOR_CARD, dropdown_text_color=COLOR_TEXT,
            dropdown_hover_color=COLOR_BTN_DARK)
        self.drum_style_menu.set(self.drum_style)
        self.drum_style_menu.pack(side="right")

        # 人声领读开关
        self.voice_switch = ctk.CTkSwitch(card2, text="开启人声领读",
                                          font=ctk.CTkFont(size=14),
                                          progress_color=COLOR_NEON,
                                          command=self._on_voice_toggle)
        self.voice_switch.grid(row=_r, column=0, sticky="w", padx=16, pady=(2, 4)); _r += 1

        # 显示中文释义开关（英语类模式生效）
        self.chinese_switch = ctk.CTkSwitch(card2, text="显示中文释义（英语）",
                                            font=ctk.CTkFont(size=14),
                                            progress_color=COLOR_NEON,
                                            command=self._on_chinese_toggle)
        self.chinese_switch.select()
        self.chinese_switch.grid(row=_r, column=0, sticky="w", padx=16, pady=(2, 12)); _r += 1

        # ---- 背景音乐区 ----
        card_music = ctk.CTkFrame(self.sidebar, fg_color=COLOR_CARD, corner_radius=14)
        card_music.pack(fill="x", padx=20, pady=(0, 10))
        ctk.CTkLabel(card_music, text="背景音乐",
                     font=ctk.CTkFont(size=15, weight="bold"),
                     text_color=COLOR_NEON).pack(anchor="w", padx=16, pady=(12, 4))
        ctk.CTkButton(card_music, text="导入背景音乐 (.mp3 / .wav)", height=36,
                      font=ctk.CTkFont(size=13, weight="bold"),
                      fg_color=COLOR_BTN_DARK, hover_color="#334155",
                      text_color=COLOR_TEXT, corner_radius=8,
                      command=self._on_import_music).pack(fill="x", padx=16, pady=(2, 6))
        self.bgm_status = ctk.CTkLabel(card_music, text="未选择音乐",
                                       font=ctk.CTkFont(size=12),
                                       text_color=COLOR_TEXT_DIM)
        self.bgm_status.pack(anchor="w", padx=16, pady=(0, 12))

        # ---- 闪烁颜色列表区（随机取色）----
        card3 = ctk.CTkFrame(self.sidebar, fg_color=COLOR_CARD, corner_radius=14)
        card3.pack(fill="x", padx=20, pady=(0, 10))
        ctk.CTkLabel(card3, text="闪烁颜色列表（随机）",
                     font=ctk.CTkFont(size=15, weight="bold"),
                     text_color=COLOR_NEON).pack(anchor="w", padx=16, pady=(12, 4))

        presets_row = ctk.CTkFrame(card3, fg_color="transparent")
        presets_row.pack(fill="x", padx=16, pady=(6, 4))
        self._swatch_buttons = []
        for color in PRESET_FLASH_COLORS:
            btn = ctk.CTkButton(presets_row, text="", width=30, height=30,
                                fg_color=color, hover_color=color,
                                corner_radius=8, border_width=0,
                                command=lambda c=color: self._toggle_flash_color(c))
            btn.pack(side="left", padx=(0, 8))
            self._swatch_buttons.append((color, btn))

        add_row = ctk.CTkFrame(card3, fg_color="transparent")
        add_row.pack(fill="x", padx=16, pady=(4, 4))
        ctk.CTkButton(add_row, text="＋ 添加颜色", height=28,
                      font=ctk.CTkFont(size=13),
                      fg_color=COLOR_BTN_DARK, hover_color="#334155",
                      text_color=COLOR_TEXT, corner_radius=8,
                      command=self._add_flash_color).pack(side="left")
        self.color_count_label = ctk.CTkLabel(add_row, text="",
                                              font=ctk.CTkFont(size=12),
                                              text_color=COLOR_TEXT_DIM)
        self.color_count_label.pack(side="right")

        self.color_preview_frame = ctk.CTkFrame(card3, fg_color="transparent")
        self.color_preview_frame.pack(fill="x", padx=16, pady=(0, 12))
        self._refresh_color_ui()

        # 全屏按钮
        self.fullscreen_btn = ctk.CTkButton(self.sidebar, text="全屏展示（F11）",
                                            height=36,
                                            font=ctk.CTkFont(size=13, weight="bold"),
                                            fg_color=COLOR_BTN_DARK,
                                            hover_color="#334155",
                                            text_color=COLOR_TEXT, corner_radius=10,
                                            command=self._toggle_fullscreen)
        self.fullscreen_btn.pack(fill="x", padx=20, pady=(0, 6))

        ctk.CTkLabel(self.sidebar, text="F11 全屏 · ESC 退出\n1 拍 = 60 / BPM 秒",
                     font=ctk.CTkFont(size=11), text_color=COLOR_TEXT_DIM,
                     justify="left").pack(side="bottom", anchor="w",
                                          padx=20, pady=10)

    # ------------------------------------------------ 右侧主展示区
    def _build_main(self):
        self.main = ctk.CTkFrame(self, fg_color=COLOR_BG, corner_radius=0)
        self.main.grid(row=0, column=1, sticky="nsew")
        self.main.grid_rowconfigure(0, weight=0)   # 顶部状态栏
        self.main.grid_rowconfigure(1, weight=1)   # 中央核心展示区
        self.main.grid_rowconfigure(2, weight=0)   # 底部控制区
        self.main.grid_columnconfigure(0, weight=1)

        self._build_status_bar()
        self._build_center()
        self._build_controls()

    def _build_status_bar(self):
        self.status_bar = ctk.CTkFrame(self.main, fg_color=COLOR_SIDEBAR,
                                       corner_radius=0)
        self.status_bar.grid(row=0, column=0, sticky="ew")
        self.status_bar.grid_columnconfigure(0, weight=1)

        self.status_word_label = ctk.CTkLabel(self.status_bar, text="等待开始…",
                                              font=ctk.CTkFont(size=22, weight="bold"),
                                              text_color=COLOR_GOLD)
        self.status_word_label.grid(row=0, column=0, sticky="w", padx=24, pady=(14, 2))

        dash = ctk.CTkFrame(self.status_bar, fg_color="transparent")
        dash.grid(row=0, column=1, sticky="e", padx=24)
        self.remain_label = ctk.CTkLabel(dash, text="剩余 0",
                                         font=ctk.CTkFont(size=13),
                                         text_color=COLOR_TEXT_DIM)
        self.remain_label.pack(side="left", padx=(0, 14))
        self.progress_label = ctk.CTkLabel(dash, text="进度 0%",
                                           font=ctk.CTkFont(size=13),
                                           text_color=COLOR_NEON)
        self.progress_label.pack(side="left", padx=(0, 14))
        self.total_label = ctk.CTkLabel(dash, text="总数 0",
                                        font=ctk.CTkFont(size=13),
                                        text_color=COLOR_TEXT_DIM)
        self.total_label.pack(side="left")

        # 右上角「全屏演示」按钮（进度条旁边）
        self.fullscreen_top_btn = ctk.CTkButton(
            dash, text="⛶ 全屏演示", height=30,
            font=ctk.CTkFont(size=13, weight="bold"),
            fg_color="#0ea5e9", hover_color="#38bdf8",
            text_color="#04121a", corner_radius=8,
            command=self._toggle_fullscreen)
        self.fullscreen_top_btn.pack(side="left", padx=(14, 0))

        self.progress_bar = ctk.CTkProgressBar(self.status_bar, height=8, corner_radius=4,
                                               progress_color=COLOR_NEON,
                                               fg_color=COLOR_CELL_IDLE)
        self.progress_bar.set(0)
        self.progress_bar.grid(row=1, column=0, columnspan=2, sticky="ew",
                               padx=24, pady=(2, 14))

    def _build_center(self):
        self.center = ctk.CTkFrame(self.main, fg_color=COLOR_BG, corner_radius=0)
        self.center.grid(row=1, column=0, sticky="nsew")
        self.center.grid_rowconfigure(0, weight=3, minsize=120)   # 大字区（约 30% 高度）
        self.center.grid_rowconfigure(1, weight=7)                # 四宫格区（约 70% 高度）
        self.center.grid_columnconfigure(0, weight=1)

        self.word_area = ctk.CTkFrame(self.center, fg_color="transparent")
        self.word_area.grid(row=0, column=0, sticky="nsew")

        self.word_shadow = ctk.CTkLabel(self.word_area, text="READY",
                                        font=ctk.CTkFont(BIG_FONT_FAMILY, 96, "bold"),
                                        text_color="#001224")
        self.word_shadow.place(relx=0.5, rely=0.5, anchor="center", x=5, y=5)

        self.word_main = ctk.CTkLabel(self.word_area, text="READY",
                                      font=ctk.CTkFont(BIG_FONT_FAMILY, 96, "bold"),
                                      text_color=COLOR_GOLD)
        self.word_main.place(relx=0.5, rely=0.5, anchor="center")

        # 方框矩阵容器（严格 2x2）
        self.grid_frame = ctk.CTkFrame(self.center, fg_color="transparent")
        self.grid_frame.grid(row=1, column=0, sticky="nsew", pady=(0, 10))

        self._rebuild_grid()

    def _build_controls(self):
        self.controls_bar = ctk.CTkFrame(self.main, fg_color=COLOR_SIDEBAR,
                                         corner_radius=0)
        self.controls_bar.grid(row=2, column=0, sticky="ew")

        inner = ctk.CTkFrame(self.controls_bar, fg_color="transparent")
        inner.pack(pady=18)

        self.start_btn = ctk.CTkButton(inner, text="▶ 开始喊麦", width=200, height=52,
                                       font=ctk.CTkFont(size=17, weight="bold"),
                                       fg_color=COLOR_GOLD, hover_color="#FFC300",
                                       text_color="#111111", corner_radius=12,
                                       command=self.start_game)
        self.start_btn.pack(side="left", padx=10)

        self.pause_btn = ctk.CTkButton(inner, text="⏸ 暂停/继续", width=200, height=52,
                                       font=ctk.CTkFont(size=17, weight="bold"),
                                       fg_color="#0ea5e9", hover_color="#38bdf8",
                                       text_color="#04121a", corner_radius=12,
                                       command=self.toggle_pause)
        self.pause_btn.pack(side="left", padx=10)

        self.reset_btn = ctk.CTkButton(inner, text="↻ 重置游戏", width=200, height=52,
                                       font=ctk.CTkFont(size=17, weight="bold"),
                                       fg_color=COLOR_BTN_DARK, hover_color="#334155",
                                       text_color=COLOR_TEXT, corner_radius=12,
                                       command=self.reset_game)
        self.reset_btn.pack(side="left", padx=10)

    # ------------------------------------------------ 方框矩阵重建（严格 2x2）
    def _rebuild_grid(self):
        """严格 2x2 矩阵：英语变位 = 3 格（右下角留空）；基础英语 / 语文 = 4 格。

        格子数量只与「模式」有关，与「朗读次数」无关，绝不增加或越界。
        """
        for w in self.grid_frame.winfo_children():
            w.destroy()
        self.cells = []
        self.cell_labels = []

        if self.mode == "en":
            positions = [(0, 0), (0, 1), (1, 0)]   # 原型 / 过去式 / 过去分词
        else:
            positions = [(0, 0), (0, 1), (1, 0), (1, 1)]   # 2x2 四宫格

        for c in range(2):
            self.grid_frame.grid_columnconfigure(c, weight=1, uniform="cell")
        for r in range(2):
            self.grid_frame.grid_rowconfigure(r, weight=1, uniform="cell")

        for r, c in positions:
            cell = ctk.CTkFrame(self.grid_frame, fg_color=COLOR_CELL_IDLE,
                                corner_radius=16, border_width=1,
                                border_color="#2a2a4a")
            cell.grid(row=r, column=c, sticky="nsew", padx=10, pady=10)
            lbl = ctk.CTkLabel(cell, text="",
                               font=ctk.CTkFont("Arial Black", 22, "bold"),
                               text_color=COLOR_TEXT_DIM)
            lbl.place(relx=0.5, rely=0.5, anchor="center")
            self.cells.append(cell)
            self.cell_labels.append(lbl)

    # ==========================================================================
    # 界面显示辅助方法
    # ==========================================================================
    def _set_big_title(self, text: str):
        """更新中央大标题：按长度缩放字号 + 自动换行，始终居中完整显示。"""
        n = len(text) if text else 0
        if n <= 4:
            size = self.font_size
        elif n <= 8:
            size = int(self.font_size * 0.8)
        elif n <= 12:
            size = int(self.font_size * 0.64)
        elif n <= 20:
            size = int(self.font_size * 0.5)
        else:
            size = int(self.font_size * 0.38)
        size = max(14, size)
        font = ctk.CTkFont(BIG_FONT_FAMILY, size, "bold")

        # 计算可用宽度做自动换行，避免超长文字被切掉
        try:
            w = self.main.winfo_width()
        except Exception:
            w = 0
        wrap = int(w * 0.9) if w > 120 else 800

        self.word_main.configure(text=text, font=font, wraplength=wrap, justify="center")
        self.word_shadow.configure(text=text, font=font, wraplength=wrap, justify="center")

    def _set_status_word(self, text: str):
        self.status_word_label.configure(text=text or " ")

    def _cell_font(self, text: str):
        """方框内文字字号：随「字体大小」缩放；中文用中文字体。"""
        n = len(text)
        base = max(10, int(26 * self.font_size / 96))
        if n <= 6:
            size = base
        elif n <= 10:
            size = int(base * 0.77)
        elif n <= 14:
            size = int(base * 0.58)
        else:
            size = int(base * 0.46)
        if self.fullscreen:
            size = int(size * 1.7)
        family = BIG_FONT_FAMILY if _has_cjk(text) else "Arial Black"
        return ctk.CTkFont(family, max(8, size), "bold")

    def _current_item(self):
        if 0 <= self.current_index < len(self.words):
            return self.words[self.current_index]
        return None

    def _render_title(self):
        item = self._current_item()
        if self.mode in ("en", "basic"):
            if not item:
                text = ""
            elif self.show_chinese and item["meaning"]:
                text = item["meaning"]
            else:
                text = item["base"] or ""
        else:
            if item and item["pinyin"]:
                text = f"{item['word']} - {item['pinyin']}"
            else:
                text = ""
        self._set_big_title(text)

    def _render_status(self):
        item = self._current_item()
        if self.mode in ("en", "basic"):
            text = item["base"] if item else ""
        else:
            text = item["word"] if item else ""
        self._set_status_word(text or " ")

    def _render_cells(self):
        """按模式把内容填入方框（数量固定，与朗读次数无关）。"""
        item = self._current_item()
        if self.mode == "en":
            contents = [item["base"], item["past"], item["pp"]] if item else ["", "", ""]
        else:
            word = item["base"] if (self.mode == "basic" and item) else (item["word"] if item else "")
            contents = [word] * 4       # 四个格子永远显示同一个当前单词
        for i, lbl in enumerate(self.cell_labels):
            text = contents[i] if i < len(contents) else ""
            lbl.configure(text=text, font=self._cell_font(text))

    def _render_current(self):
        self._render_title()
        self._render_status()
        self._render_cells()
        self._update_dashboard()

    def _random_flash_color(self):
        if self.flash_colors:
            return random.choice(self.flash_colors)
        return COLOR_NEON

    def _light_cell(self, idx: int, color=None):
        if color is None:
            color = self._random_flash_color()
        for j, cell in enumerate(self.cells):
            if j == idx:
                cell.configure(fg_color=color, border_color=color, border_width=2)
                self.cell_labels[j].configure(text_color="#04121a")
            else:
                cell.configure(fg_color=COLOR_CELL_IDLE,
                               border_color="#2a2a4a", border_width=1)
                self.cell_labels[j].configure(text_color=COLOR_TEXT_DIM)

    def _update_dashboard(self):
        total = len(self.words)
        if total == 0:
            self.remain_label.configure(text="剩余 0")
            self.progress_label.configure(text="进度 0%")
            self.total_label.configure(text="总数 0")
            self.progress_bar.set(0)
            return
        done = min(self.current_index, total)
        remain = max(0, total - self.current_index)
        percent = int(done / total * 100)
        self.remain_label.configure(text=f"剩余 {remain}")
        self.progress_label.configure(text=f"进度 {percent}%")
        self.total_label.configure(text=f"总数 {total}")
        self.progress_bar.set(done / total)

    def _update_pause_button(self):
        if not self.running:
            self.pause_btn.configure(text="⏸ 暂停/继续")
        elif self.paused:
            self.pause_btn.configure(text="▶ 继续")
        else:
            self.pause_btn.configure(text="⏸ 暂停")

    # ==========================================================================
    # 核心节奏逻辑（先读后闪：root.after + 后台线程，绝不阻塞 UI）
    # ==========================================================================
    @property
    def _cell_count(self):
        """格子数量：英语变位 3，基础/语文 4（与朗读次数无关）。"""
        return 3 if self.mode == "en" else 4

    @property
    def _beats_per_word(self):
        """当前词条总拍数：变位 = 3 × 朗读次数；基础/语文 = 朗读次数。"""
        if self.mode == "en":
            return 3 * self.repeat_count
        return self.repeat_count

    def start_game(self):
        if not self.words:
            messagebox.showinfo("提示", "请先导入数据（.xlsx 或 .txt）。")
            return
        if self.running and not self.paused:
            return

        self._ensure_bgm_playing()   # 开始喊麦时循环播放背景音乐（低音量）

        self.running = True
        self.paused = False
        self.pause_event.clear()
        self.current_index = 0
        self.beat_index = 0
        self._flash_started = False
        self._update_pause_button()
        self._show_word()

    def toggle_pause(self):
        if not self.running:
            return

        if self.paused:
            self.paused = False
            self.pause_event.clear()
            self._update_pause_button()
            if not self._flash_started:
                self._start_flash()
            else:
                self._schedule_next_beat()
        else:
            self.paused = True
            self.pause_event.set()
            self._update_pause_button()
            if self._after_id is not None:
                self.after_cancel(self._after_id)
                self._after_id = None
            self.speech.clear()

    def reset_game(self):
        self.running = False
        self.paused = False
        self.pause_event.clear()
        self._flash_started = False
        if self._after_id is not None:
            self.after_cancel(self._after_id)
            self._after_id = None
        self.speech.stop()
        self.current_index = 0
        self.beat_index = 0
        self._light_cell(-1)
        self._render_cells()
        self._set_big_title("READY")
        self._set_status_word("等待开始…")
        self._update_dashboard()
        self._update_pause_button()

    def _show_word(self):
        """展示当前词条：先渲染，再决定「先读后闪」还是「直接闪」。"""
        self.beat_index = 0
        self._flash_started = False
        self._render_current()

        if self.voice_on:
            texts = self._current_word_texts()
            if self.bpm > 200:
                # 高 BPM 防重叠：切断上一句，本句异步读，立即开始闪烁
                self.speech.interrupt()
                if texts:
                    self.speech.speak(texts, rate=self.SPEAK_RATE)
                self._start_flash()
            else:
                self._start_voice_then_flash(texts)
        else:
            self._start_flash()

    def _start_flash(self):
        if not self.running or self.paused:
            return
        self._flash_started = True
        self.beat_index = 0
        self._beat_step()
        self._schedule_next_beat()

    def _beat_step(self):
        """执行当前这一拍：点亮对应格子（随机色）+ 鼓点。"""
        cell = self.beat_index % self._cell_count
        self._light_cell(cell, self._random_flash_color())
        self._play_beat()

    def _current_word_texts(self):
        item = self._current_item()
        if not item:
            return []
        if self.mode == "en":
            return [(t, "en") for t in (item["base"], item["past"], item["pp"]) if t]
        elif self.mode == "basic":
            return [(item["base"], "en")] if item["base"] else []
        else:
            return [(item["word"], "zh")] if item["word"] else []

    def _start_voice_then_flash(self, texts):
        """后台线程：朗读 → 等人声完全结束 → 再等 0.5s → 通知主线程开始闪烁。"""
        def _run():
            try:
                if texts:
                    self.speech.speak_and_wait(texts, rate=self.SPEAK_RATE)
                time.sleep(0.5)
            except Exception as e:
                print("[同步] 朗读线程异常：", e)
            self._ui_queue.put("flash_ready")

        threading.Thread(target=_run, daemon=True).start()

    def _play_beat(self):
        if self.drum_on:
            self.drum_player.play(self.drum_style)

    def _beat_ms(self) -> int:
        return max(40, int(60000 / max(1, self.bpm)))

    def _schedule_next_beat(self):
        if not self.running or self.paused:
            return
        self._after_id = self.after(self._beat_ms(), self._on_beat)

    def _on_beat(self):
        self._after_id = None
        if not self.running or self.paused:
            return

        self.beat_index += 1
        if self.beat_index >= self._beats_per_word:
            self.current_index += 1
            if self.current_index >= len(self.words):
                self._finish()
                return
            self._show_word()
        else:
            self._beat_step()
            self._schedule_next_beat()

    def _finish(self):
        self.running = False
        self.paused = False
        self.pause_event.clear()
        self._flash_started = False
        self._light_cell(-1)
        self._set_big_title("FINISH")
        self._set_status_word("全部读完，点击「开始喊麦」再来一轮")
        self._update_dashboard()
        self._update_pause_button()

    # ------------------------------------------------------------------ 线程安全的事件轮询
    def _poll_ui_queue(self):
        try:
            while True:
                msg = self._ui_queue.get_nowait()
                self._handle_ui_event(msg)
        except queue.Empty:
            pass
        try:
            self.after(50, self._poll_ui_queue)
        except Exception:
            pass

    def _handle_ui_event(self, msg):
        if msg == "flash_ready":
            if self.running and not self.paused and not self._flash_started:
                self._start_flash()

    # ==========================================================================
    # 模式切换 / 全屏
    # ==========================================================================
    def _apply_mode(self, mode: str):
        self.mode = mode
        self.mode_menu.set(MODE_LABELS[mode])
        self._rebuild_grid()
        self._render_cells()

    def _on_mode_change(self, choice: str):
        key = MODE_KEYS[choice]
        if key == self.mode:
            return
        self._apply_mode(key)
        self.reset_game()

    def _toggle_fullscreen(self, event=None):
        """全屏：只隐藏左侧控制边栏，保留状态栏、大字（30%）和四宫格（70%）。

        关键：隐藏侧边栏的同时，必须把根窗口第 0 列的 minsize 清零，
        否则侧边栏列仍会空占 320px，导致主区（含中央大字）整体右偏、无法精确居中。
        """
        self.fullscreen = not self.fullscreen
        if self.fullscreen:
            self.attributes("-fullscreen", True)
            self.grid_columnconfigure(0, weight=0, minsize=0)   # 释放侧边栏列占用的 320px
            self.sidebar.grid_remove()          # 只隐藏左侧边栏
            self.fullscreen_top_btn.configure(text="⛶ 退出全屏")
        else:
            self.attributes("-fullscreen", False)
            self.grid_columnconfigure(0, weight=0, minsize=320)  # 恢复侧边栏列宽
            self.sidebar.grid()                 # 恢复左侧边栏
            self.fullscreen_top_btn.configure(text="⛶ 全屏演示")
        # 无论全屏还是窗口，都按 30% / 70% 分配大字与四宫格的高度
        self.center.grid_rowconfigure(0, weight=3, minsize=120)
        self.center.grid_rowconfigure(1, weight=7)
        self._render_title()   # 重算大字字号 / 换行宽度
        self._render_cells()

    def _on_escape(self, event=None):
        if self.fullscreen:
            self._toggle_fullscreen()

    # ==========================================================================
    # 侧边栏事件回调
    # ==========================================================================
    def _on_bpm_change(self, value):
        self.bpm = max(BPM_MIN, min(BPM_MAX, int(round(float(value)))))
        self.bpm_value.configure(text=str(self.bpm))
        if self.bgm_path:
            name = os.path.basename(self.bgm_path)
            self._music_config.setdefault("music_bpm", {})[name] = self.bpm
            self._save_config()

    def _on_read_count_change(self, value):
        self.repeat_count = max(1, min(READ_COUNT_MAX, int(round(float(value)))))
        self.read_count_value.configure(text=str(self.repeat_count))

    def _on_font_change(self, value):
        self.font_size = max(12, int(round(float(value))))
        self.font_value.configure(text=str(self.font_size))
        self._render_title()
        self._render_cells()

    def _on_drum_toggle(self):
        self.drum_on = bool(self.drum_switch.get())

    def _on_drum_style_change(self, choice):
        self.drum_style = choice
        if self.drum_on:
            self.drum_player.play(choice)   # 切换即试听，便于听出区别

    def _on_voice_toggle(self):
        self.voice_on = bool(self.voice_switch.get())

    def _on_chinese_toggle(self):
        self.show_chinese = bool(self.chinese_switch.get())
        if self.mode in ("en", "basic") and self.words:
            self._render_title()

    # ------------------------------------------------------------------ 颜色列表
    def _toggle_flash_color(self, color: str):
        if color in self.flash_colors:
            self.flash_colors.remove(color)
        else:
            self.flash_colors.append(color)
        self._refresh_color_ui()

    def _add_flash_color(self):
        rgb, hex_color = colorchooser.askcolor(parent=self)
        if hex_color:
            if hex_color.upper() not in [c.upper() for c in self.flash_colors]:
                self.flash_colors.append(hex_color)
            self._refresh_color_ui()

    def _remove_flash_color(self, color: str):
        if color in self.flash_colors:
            self.flash_colors.remove(color)
        self._refresh_color_ui()

    def _refresh_color_ui(self):
        upper_list = [c.upper() for c in self.flash_colors]
        for c, btn in self._swatch_buttons:
            if c.upper() in upper_list:
                btn.configure(border_width=2, border_color="#FFFFFF")
            else:
                btn.configure(border_width=0)
        self.color_count_label.configure(text=f"已选 {len(self.flash_colors)} 色")
        for w in self.color_preview_frame.winfo_children():
            w.destroy()
        for c in self.flash_colors:
            chip = ctk.CTkButton(self.color_preview_frame, text="",
                                 width=22, height=22, fg_color=c, hover_color=c,
                                 corner_radius=6, border_width=0,
                                 command=lambda col=c: self._remove_flash_color(col))
            chip.pack(side="left", padx=(0, 6))

    # ==========================================================================
    # 背景音乐（pygame.mixer + config.json 记忆）
    # ==========================================================================
    def _load_pygame(self):
        if self._pygame is not None:
            return True
        try:
            import pygame
            pygame.mixer.init()
            self._pygame = pygame
            return True
        except Exception as e:
            messagebox.showerror("缺少依赖", f"需要 pygame 才能播放背景音乐：\n{e}")
            return False

    def _on_import_music(self):
        path = filedialog.askopenfilename(
            title="选择背景音乐",
            filetypes=[("音频文件", "*.mp3 *.wav"), ("MP3", "*.mp3"), ("WAV", "*.wav")],
        )
        if not path:
            return

        if not self._load_pygame():
            return

        name = os.path.basename(path)
        try:
            # 预加载并校验格式，格式错误不会导致崩溃
            self._pygame.mixer.music.load(path)
            self._pygame.mixer.music.set_volume(BGM_VOLUME)   # 低音量，低于人声与鼓点
            self.bgm_path = path
            self.bgm_status.configure(text=f"当前音乐：{name}")

            # 读取同名音乐的 BPM 记忆（截断到合法范围）
            saved = self._music_config.get("music_bpm", {}).get(name)
            if saved is not None:
                try:
                    self.bpm = max(BPM_MIN, min(BPM_MAX, int(saved)))
                    self.bpm_slider.set(self.bpm)
                    self.bpm_value.configure(text=str(self.bpm))
                except Exception:
                    pass
        except Exception as e:
            self.bgm_path = None
            self.bgm_status.configure(text="未选择音乐")
            messagebox.showerror("音乐加载失败", f"无法加载该音频文件（格式可能不正确）：\n{e}")

    def _ensure_bgm_playing(self):
        """开始喊麦时：若已导入背景音乐则循环播放，未导入则静音。"""
        if not self.bgm_path:
            return
        if self._pygame is None:
            if not self._load_pygame():
                return
        try:
            if not self._pygame.mixer.music.get_busy():
                self._pygame.mixer.music.load(self.bgm_path)
                self._pygame.mixer.music.set_volume(BGM_VOLUME)
                self._pygame.mixer.music.play(-1)
        except Exception as e:
            print("[音乐] 播放失败：", e)

    # ==========================================================================
    # 数据导入（自动识别新旧格式与模式）
    # ==========================================================================
    def _on_import(self):
        path = filedialog.askopenfilename(
            title="选择数据文件",
            filetypes=[("数据文件", "*.xlsx *.txt"),
                       ("Excel 文件", "*.xlsx"),
                       ("文本文件", "*.txt")],
        )
        if not path:
            return

        ext = os.path.splitext(path)[1].lower()
        try:
            if ext == ".xlsx":
                rows = self._read_xlsx_rows(path)
            elif ext == ".txt":
                rows = self._read_txt_rows(path)
            else:
                messagebox.showerror("不支持的文件", "仅支持 .xlsx 和 .txt 文件。")
                return
        except Exception as e:
            messagebox.showerror("导入失败", f"读取文件时出错：\n{e}")
            return

        items, mode = self._parse_rows(rows)
        if not items:
            messagebox.showwarning(
                "提示",
                "未读取到任何词条，请检查文件格式。\n\n"
                "英语变位：原型,过去式,过去分词,中文释义（如 go,went,gone,去）\n"
                "语文词汇：词汇,拼音（如 苹果,píng guǒ 或 苹果 píng guǒ）")
            return

        self.words = items
        self.import_status.configure(text=f"已导入 {len(items)} 条")
        self._apply_mode(mode)
        self.reset_game()

    @staticmethod
    def _read_xlsx_rows(path: str):
        wb = openpyxl.load_workbook(path, read_only=True, data_only=True)
        rows = []
        try:
            ws = wb.active
            for row in ws.iter_rows(values_only=True):
                if row is None:
                    continue
                cells = [("" if c is None else str(c).strip()) for c in row]
                while cells and cells[-1] == "":
                    cells.pop()
                if cells:
                    rows.append(cells)
        finally:
            wb.close()
        return rows

    @staticmethod
    def _read_txt_rows(path: str):
        raw = None
        for enc in ("utf-8-sig", "gbk", "utf-8"):
            try:
                with open(path, "r", encoding=enc) as f:
                    raw = f.read()
                break
            except (UnicodeDecodeError, LookupError):
                continue
        if raw is None:
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                raw = f.read()

        rows = []
        for line in raw.splitlines():
            fields = WordShouterApp._txt_line_to_fields(line)
            if fields:
                rows.append(fields)
        return rows

    @staticmethod
    def _txt_line_to_fields(line: str):
        line = line.strip()
        if not line:
            return []
        if re.search(r"[,，;；\t]", line):
            return [f.strip() for f in re.split(r"[,，;；\t]+", line) if f.strip()]
        parts = re.split(r"\s+", line, maxsplit=1)
        return [p.strip() for p in parts if p.strip()]

    @staticmethod
    def _parse_rows(rows):
        clean = [r for r in rows if r]
        if not clean:
            return [], None

        if clean[0][0].lower() in HEADER_KEYS:
            clean = clean[1:]
        if not clean:
            return [], None

        if _has_cjk(clean[0][0]):
            mode = "zh"
        else:
            mode = "en" if len(clean[0]) >= 3 else "basic"

        items = []
        for r in clean:
            item = {"base": "", "past": "", "pp": "",
                    "meaning": "", "word": "", "pinyin": ""}
            if mode == "en":
                if len(r) >= 4:
                    item["base"], item["past"], item["pp"] = r[0], r[1], r[2]
                    item["meaning"] = " ".join(r[3:])
                elif len(r) == 3:
                    item["base"], item["past"], item["pp"] = r[0], r[1], r[2]
                elif len(r) == 2:
                    item["base"], item["meaning"] = r[0], r[1]
                else:
                    item["base"] = r[0]
            elif mode == "basic":
                item["base"] = r[0]
                if len(r) >= 2:
                    item["meaning"] = " ".join(r[1:])
            else:
                item["word"] = r[0]
                if len(r) >= 2:
                    item["pinyin"] = " ".join(r[1:])
            items.append(item)
        return items, mode

    # ==========================================================================
    # 退出
    # ==========================================================================
    def _on_close(self):
        self.running = False
        self.pause_event.set()
        self.speech.shutdown()
        if self._pygame is not None:
            try:
                self._pygame.mixer.music.stop()
                self._pygame.mixer.quit()
            except Exception:
                pass
        self.destroy()


def main():
    app = WordShouterApp()
    app.mainloop()


if __name__ == "__main__":
    main()
