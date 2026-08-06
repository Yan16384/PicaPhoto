import json
import os
import shutil
import subprocess
import sys
import threading
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, Toplevel

from PIL import Image, ImageTk, ImageOps, ImageDraw, ImageFont

# 图片工具必须能处理高分辨率大图（手机照片、超长截图可超过 1 亿像素）。
# 放开 PIL 默认 8900 万像素上限，避免 DecompressionBomb 警告/报错。
Image.MAX_IMAGE_PIXELS = None

try:
    import cv2
except Exception:
    cv2 = None

try:
    import ctypes
except Exception:
    ctypes = None


# ── Windows 高分屏适配 ─────────────────────────────────────────────
def _enable_dpi_awareness() -> None:
    """声明进程 DPI 感知，避免 tkinter 被系统按位图放大导致界面模糊。"""
    if sys.platform != "win32" or ctypes is None:
        return
    try:
        ctypes.windll.user32.SetProcessDpiAwarenessContext(ctypes.c_void_p(-4))
        return
    except Exception:
        pass
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
        return
    except Exception:
        pass
    try:
        ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass


def _get_system_dpi() -> float:
    """返回系统逻辑 DPI（默认 96）。"""
    if sys.platform != "win32" or ctypes is None:
        return 96.0
    try:
        dpi = int(ctypes.windll.user32.GetDpiForSystem())
        if dpi > 0:
            return float(dpi)
    except Exception:
        pass
    return 96.0


def _get_primary_scale() -> float:
    """主显示器 UI 缩放系数：125% → 1.25，200% → 2.0。"""
    if sys.platform != "win32" or ctypes is None:
        return 1.0
    try:
        pct = int(ctypes.windll.shcore.GetScaleFactorForDevice(0))
        if pct > 0:
            return pct / 100.0
    except Exception:
        pass
    try:
        dpi = int(ctypes.windll.user32.GetDpiForSystem())
        if dpi > 0:
            return dpi / 96.0
    except Exception:
        pass
    return 1.0


_enable_dpi_awareness()
UI_SCALE = _get_primary_scale()


def ui(v: float) -> int:
    """把设计稿像素按系统缩放换算为实际像素。"""
    return max(1, int(round(v * UI_SCALE)))


CONFIG_FILE = "album_config.json"
DEFAULT_IMAGE_EXT = [".jpg", ".jpeg", ".png", ".bmp", ".gif", ".tiff", ".webp"]
DEFAULT_VIDEO_EXT = [".mp4", ".mov", ".avi", ".mkv", ".flv", ".wmv", ".webm", ".m4v"]
THUMB_SIZE = (ui(160), ui(160))
PREVIEW_GAP = ui(12)
ALBUM_BAR_HEIGHT = ui(100)
SIDEBAR_WIDTH = ui(250)
AUTO_REFRESH_MS = 5000
MAX_WORKERS = max(4, min(16, os.cpu_count() or 4))

THEMES = {
    # 深色：飞书/微信深色风格（深蓝灰 + 品牌蓝）
    "dark": {
        "root_bg": "#17181c",
        "main_bg": "#1f2128",
        "panel_bg": "#262931",
        "card_bg": "#2e323b",
        "hover_bg": "#3a3f4b",
        "border": "#333844",
        "text": "#f2f4f8",
        "subtext": "#9aa3b2",
        "accent": "#4d8dff",
        "accent_hover": "#6ea2ff",
        "accent_soft": "#1f2c47",
        "green": "#2fd08a",
        "yellow": "#f4c95d",
        "red": "#ff6b6b",
        "status_bg": "#1a1c21",
        "input_bg": "#1f2128",
        "divider": "#2b2f38",
    },
    # 浅色：微信/飞书浅色风格（浅灰底 + 白卡片 + 飞书蓝）
    "light": {
        "root_bg": "#f2f3f5",
        "main_bg": "#ffffff",
        "panel_bg": "#ffffff",
        "card_bg": "#f5f7fa",
        "hover_bg": "#ebeff5",
        "border": "#e4e6eb",
        "text": "#1f2329",
        "subtext": "#8a919f",
        "accent": "#3370ff",
        "accent_hover": "#5c8dff",
        "accent_soft": "#eef3ff",
        "green": "#00b578",
        "yellow": "#c9a227",
        "red": "#e54545",
        "status_bg": "#f7f8fa",
        "input_bg": "#ffffff",
        "divider": "#eceef2",
    },
}

# ── 微信风格开关（胶囊形 Toggle） ──────────────────────────────────
class _Switch(tk.Canvas):
    """胶囊形开关：on=绿色，off=灰；点击切换，回调可选。PIL 高倍率渲染，边缘平滑无锯齿。"""

    ON_COLOR = "#07c160"

    def __init__(self, master, var, off_color="#d8d8d8", width=None, height=None, on_change=None):
        self._sw_w = width or ui(46)
        self._sw_h = height or ui(24)
        super().__init__(master, width=self._sw_w, height=self._sw_h,
                         bg=master.cget("bg"), highlightthickness=0, bd=0, cursor="hand2")
        self.var = var
        self.off_color = off_color
        self.on_change = on_change
        self._photo = None
        self.bind("<Button-1>", self._on_click)
        self._draw()

    def _draw(self):
        try:
            from PIL import Image as _Img, ImageDraw as _IDraw, ImageTk as _ITk
            w, h = self._sw_w, self._sw_h
            ss = 4  # 4 倍超采样
            W, H = w * ss, h * ss
            img = _Img.new("RGBA", (W, H), (0, 0, 0, 0))
            d = _IDraw.Draw(img)
            on = bool(self.var.get())
            color = self.ON_COLOR if on else self.off_color
            d.rounded_rectangle((0, 0, W - 1, H - 1), radius=H // 2, fill=color)
            # 内圈高光（轻微立体感）
            d.rounded_rectangle((int(W*0.04), int(H*0.12), int(W*0.96), int(H*0.88)), radius=int(H*0.36),
                                outline=(255, 255, 255, 60), width=max(1, int(H*0.04)))
            # 滑块
            r = H // 2
            kx = (W - H + r) if on else r
            pad = max(2, H // 7)
            d.ellipse((kx - r + pad, pad, kx + r - pad, H - pad), fill=(255, 255, 255, 255))
            img = img.resize((w, h), _Img.Resampling.LANCZOS)
            self._photo = _ITk.PhotoImage(img)
            self.delete("all")
            self.create_image(0, 0, image=self._photo, anchor="nw")
        except Exception:
            self.delete("all")
            on = bool(self.var.get())
            w, h = self._sw_w, self._sw_h
            r = h // 2
            color = self.ON_COLOR if on else self.off_color
            self.create_oval(0, 0, h, h, fill=color, outline=color)
            self.create_rectangle(r, 0, w - r, h, fill=color, outline=color)
            self.create_oval(w - h, 0, w, h, fill=color, outline=color)
            kx = (w - h + r) if on else r
            pad = max(2, h // 6)
            self.create_oval(kx - r + pad, pad, kx + r - pad, h - pad, fill="white", outline="")

    def _on_click(self, _event):
        self.var.set(not bool(self.var.get()))
        self._draw()
        if self.on_change:
            self.on_change()


def _theme_control(parent, t, theme_var):
    """外观主题单选控件。"""
    f = tk.Frame(parent, bg=t["main_bg"])
    for text, val in (("浅色", "light"), ("深色", "dark")):
        ttk.Radiobutton(f, text=text, value=val, variable=theme_var, style="TRadiobutton").pack(side=tk.LEFT, padx=(0, ui(10)))
    return f


def _conflict_combo(parent, t, items, var, holder):
    """重名策略下拉控件，并把实例存入 holder 供保存时读取。"""
    combo = ttk.Combobox(parent, state="readonly", width=14, font=("微软雅黑", 10))
    combo["values"] = [label for label, _v in items]
    current_label = next((label for label, v in items if v == var.get()), items[0][0])
    combo.set(current_label)
    holder["combo"] = combo
    return combo


# ── 内置应用图标（高分辨率 PNG，base64 编码） ──
_APP_ICON_B64 = (
    "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"
)

class MediaSorterApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("PicaPhoto")
        self.root.geometry(f"{ui(1500)}x{ui(920)}")
        try:
            # Tk 点-像素换算：DPI 感知进程里 winfo_fpixels("1i") 返回当前 DPI，
            # 用它设置 tk scaling 让文字随系统缩放同步变大、不发虚。
            phys_dpi = float(self.root.winfo_fpixels("1i")) or _get_system_dpi() or 96.0
            self.root.tk.call("tk", "scaling", max(1.0, phys_dpi / 72.0))
        except Exception:
            pass
        try:
            self.root.state("zoomed")
        except Exception:
            pass

        self.executor = ThreadPoolExecutor(max_workers=MAX_WORKERS)
        self.auto_refresh_job = None
        self.current_scan_token = 0
        self.current_preview_token = 0
        self.current_single_token = 0
        self._closed = False

        self.config = self.load_config()
        self.theme_name = self.config.get("theme", "light")
        self.theme = THEMES.get(self.theme_name, THEMES["dark"])

        self.root_dir = ""
        self.current_dir = ""
        self.current_filter = "all"
        self.albums = list(self.config.get("albums", []))
        self.current_files = []
        self.current_idx = 0
        self.selected_files = set()
        self.last_selected_idx = -1
        self.is_preview_mode = False
        self.auto_refresh_enabled = bool(self.config.get("auto_refresh", False))
        self.move_history = list(self.config.get("temp_history", []))[-100:]
        self.recent_ops = list(self.config.get("recent_ops", []))[-30:]

        self.thumb_pil_cache = {}
        self.video_info_cache = {}
        self.preview_photo_refs = []
        self.single_photo = None
        self.temp_single_image = None
        self.video_placeholder_pil = None
        self.video_placeholder_photo = None
        self.single_preview_cache = {}
        self.single_loading_keys = set()
        self.preview_thumb_item_ids = {}
        self.preview_thumb_source_pil = {}
        self.hover_video_frames_cache = {}
        self.hover_state = {"idx": None, "job": None, "photos": [], "token": 0}
        self._resize_job = None
        self.album_btn_map = {}
        self.preview_index_map = {}
        self.tree_node_map = {}
        self.loading_previews = set()
        self._suspend_tree_callback = False
        self.is_animating = False
        self.anim_photo = None
        self.album_drag = {
            "album": None,
            "widget": None,
            "start_x": 0,
            "start_y": 0,
            "start_index": -1,
            "dragging": False,
            "target_index": -1,
            "ghost": None,
            "indicator": None,
            "click_block": False,
        }

        self.apply_root_theme()
        self.build_app_icon()
        self.apply_window_icon(self.root)
        self.build_ui()
        self.build_video_placeholder()
        self.refresh_album_bar()
        self.refresh_tree()
        self.bind_hotkeys()

        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.bind("<Configure>", self.on_root_configure)

        if self.auto_refresh_enabled:
            self.start_auto_refresh()

    # -------------------------- 基础配置 --------------------------
    def load_config(self):
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                    cfg = json.load(f)
            except Exception:
                cfg = {}
        else:
            cfg = {}
        cfg.setdefault("albums", [])
        cfg.setdefault("theme", "light")
        cfg.setdefault("auto_refresh", False)
        cfg.setdefault("image_ext", DEFAULT_IMAGE_EXT[:])
        cfg.setdefault("video_ext", DEFAULT_VIDEO_EXT[:])
        cfg.setdefault("progress", {})
        cfg.setdefault("temp_history", [])
        cfg.setdefault("recent_ops", [])
        cfg.setdefault("conflict_strategy", "rename")
        cfg.setdefault("preload_count", 6)
        return cfg

    def save_config(self):
        self.config["albums"] = self.albums
        self.config["theme"] = self.theme_name
        self.config["auto_refresh"] = self.auto_refresh_enabled
        self.config["temp_history"] = self.move_history[-100:]
        self.config["recent_ops"] = self.recent_ops[-30:]
        try:
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(self.config, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def get_image_ext(self):
        return tuple(x.lower() for x in self.config.get("image_ext", DEFAULT_IMAGE_EXT))

    def get_video_ext(self):
        return tuple(x.lower() for x in self.config.get("video_ext", DEFAULT_VIDEO_EXT))

    def get_media_ext(self):
        return self.get_image_ext() + self.get_video_ext()

    def normalize_ext_text(self, text: str):
        items = []
        for part in text.replace("；", ",").replace(";", ",").split(","):
            item = part.strip().lower()
            if not item:
                continue
            if not item.startswith("."):
                item = "." + item
            items.append(item)
        return sorted(dict.fromkeys(items))

    # -------------------------- 线程辅助 --------------------------
    def run_async(self, fn, callback=None, error_callback=None):
        future = self.executor.submit(fn)

        def _done(fut):
            if self._closed:
                return
            try:
                result = fut.result()
            except Exception as exc:
                if error_callback:
                    self.root.after(0, lambda e=exc: error_callback(e))
                return
            if callback:
                self.root.after(0, lambda r=result: callback(r))

        future.add_done_callback(_done)
        return future

    # -------------------------- 主题 --------------------------
    def apply_root_theme(self):
        self.root.configure(bg=self.theme["root_bg"])

    def build_app_icon(self):
        """使用内置高分辨率图标生成窗口图标与品牌徽标（含兜底绘制）。"""
        pil = None
        try:
            import base64 as _b64
            import io as _io
            pil = Image.open(_io.BytesIO(_b64.b64decode(_APP_ICON_B64))).convert("RGBA")
        except Exception:
            pil = None
        if pil is None:
            # 兜底：蓝色圆角 + 白色 P
            size = 256
            img = Image.new("RGBA", (size, size), (0, 0, 0, 0))
            d = ImageDraw.Draw(img)
            d.rounded_rectangle((6, 6, size - 6, size - 6), radius=52, fill="#2e58e8")
            try:
                f = ImageFont.truetype("msyh.ttc", 150)
            except Exception:
                f = ImageFont.load_default()
            d.text((size // 2, size // 2), "P", fill="white", anchor="mm", font=f)
            pil = img
        self.app_icon_pil = pil
        self.app_icon_image = ImageTk.PhotoImage(pil.resize((64, 64), Image.Resampling.LANCZOS))
        self.brand_logo_image = ImageTk.PhotoImage(pil.resize((28, 28), Image.Resampling.LANCZOS))

    def apply_window_icon(self, window):
        try:
            if getattr(self, "app_icon_image", None) is not None:
                window.iconphoto(True, self.app_icon_image)
        except Exception:
            pass

    def center_window(self, window, width=None, height=None, parent=None):
        try:
            window.update_idletasks()
            if width is None:
                width = max(1, window.winfo_width())
            if height is None:
                height = max(1, window.winfo_height())
            host = parent or self.root
            host.update_idletasks()
            if host is self.root and self.root.state() == "zoomed":
                sw = self.root.winfo_screenwidth()
                sh = self.root.winfo_screenheight()
                x = (sw - width) // 2
                y = (sh - height) // 2 - 20
            else:
                x = host.winfo_rootx() + max(0, (host.winfo_width() - width) // 2)
                y = host.winfo_rooty() + max(0, (host.winfo_height() - height) // 2)
            window.geometry(f"{width}x{height}+{int(x)}+{int(y)}")
        except Exception:
            pass

    def configure_ttk(self):
        self.style = ttk.Style()
        self.style.theme_use("clam")
        t = self.theme
        # 通用按钮：扁平、留白充足（飞书式）
        self.style.configure(
            "TButton",
            font=("微软雅黑", 10),
            padding=(ui(14), ui(7)),
            background=t["card_bg"],
            foreground=t["text"],
            bordercolor=t["card_bg"],
            lightcolor=t["card_bg"],
            darkcolor=t["card_bg"],
            relief="flat",
            focusthickness=0,
        )
        self.style.map(
            "TButton",
            background=[("active", t["hover_bg"]), ("pressed", t["hover_bg"])],
            bordercolor=[("active", t["hover_bg"]), ("pressed", t["hover_bg"])],
        )
        # 主操作按钮：品牌蓝
        self.style.configure(
            "Accent.TButton",
            font=("微软雅黑", 10, "bold"),
            padding=(ui(16), ui(7)),
            background=t["accent"],
            foreground="#ffffff",
            bordercolor=t["accent"],
            lightcolor=t["accent"],
            darkcolor=t["accent"],
            relief="flat",
            focusthickness=0,
        )
        self.style.map(
            "Accent.TButton",
            background=[("active", t["accent_hover"]), ("pressed", t["accent_hover"])],
            bordercolor=[("active", t["accent_hover"]), ("pressed", t["accent_hover"])],
        )
        # 输入框
        self.style.configure(
            "TEntry",
            fieldbackground=t["input_bg"],
            foreground=t["text"],
            insertcolor=t["text"],
            bordercolor=t["border"],
            lightcolor=t["border"],
            darkcolor=t["border"],
            padding=(ui(8), ui(6)),
            relief="flat",
        )
        self.style.map("TEntry", bordercolor=[("focus", t["accent"])])
        # 目录树
        self.style.configure(
            "Treeview",
            background=t["panel_bg"],
            foreground=t["text"],
            fieldbackground=t["panel_bg"],
            rowheight=ui(30),
            bordercolor=t["border"],
            font=("微软雅黑", 10),
        )
        self.style.map(
            "Treeview",
            background=[("selected", t["accent_soft"]), ("active", t["hover_bg"])],
            foreground=[("selected", t["accent"])],
        )
        self.style.configure(
            "Treeview.Heading",
            background=t["panel_bg"],
            foreground=t["subtext"],
            font=("微软雅黑", 10, "bold"),
            relief="flat",
        )
        self.style.map("Treeview.Heading", background=[("active", t["hover_bg"])])
        # 滚动条
        self.style.configure(
            "TScrollbar",
            background=t["border"],
            troughcolor=t["panel_bg"],
            bordercolor=t["panel_bg"],
            arrowcolor=t["subtext"],
            relief="flat",
        )
        self.style.map("TScrollbar", background=[("active", t["accent"])])
        # 复选框 / 单选按钮（clam 主题渲染更平滑，去锯齿）
        self.style.configure(
            "TCheckbutton",
            background=t["panel_bg"],
            foreground=t["text"],
            font=("微软雅黑", 10),
            focusthickness=0,
            padding=(0, ui(5)),
            indicatorcolor=t["accent_soft"],
        )
        self.style.map(
            "TCheckbutton",
            background=[("active", t["panel_bg"])],
            foreground=[("active", t["text"])],
        )
        self.style.configure(
            "TRadiobutton",
            background=t["panel_bg"],
            foreground=t["text"],
            font=("微软雅黑", 10),
            focusthickness=0,
            padding=(0, ui(5)),
            indicatorcolor=t["accent_soft"],
        )
        self.style.map(
            "TRadiobutton",
            background=[("active", t["panel_bg"])],
            foreground=[("active", t["text"])],
        )
        # 微调框
        self.style.configure(
            "TSpinbox",
            fieldbackground=t["input_bg"],
            foreground=t["text"],
            arrowcolor=t["subtext"],
            bordercolor=t["border"],
            lightcolor=t["border"],
            darkcolor=t["border"],
            padding=(ui(8), ui(4)),
            relief="flat",
            insertcolor=t["text"],
        )
        self.style.map("TSpinbox", bordercolor=[("focus", t["accent"])])

    def switch_theme(self, theme_name: str):
        if theme_name not in THEMES:
            return
        self.theme_name = theme_name
        self.theme = THEMES[theme_name]
        self.apply_root_theme()
        self.configure_ttk()
        self.restyle_widgets()
        self.build_video_placeholder()
        self.preview_photo_refs.clear()
        self.thumb_pil_cache.clear()
        self.single_preview_cache.clear()
        self.preview_thumb_item_ids.clear()
        self.preview_thumb_source_pil.clear()
        self.stop_hover_video_preview()
        self.refresh_album_bar()
        self.refresh_tree()
        if self.is_preview_mode:
            self.refresh_preview_grid()
        else:
            self.refresh_single_view()
        self.save_config()

    def restyle_widgets(self):
        t = self.theme
        self.configure_ttk()
        self.top_bar.configure(bg=t["root_bg"])
        self.main_container.configure(bg=t["root_bg"])
        self.sidebar_frame.configure(bg=t["panel_bg"], highlightbackground=t["border"], highlightthickness=1)
        self.right_frame.configure(bg=t["root_bg"])
        self.single_frame.configure(bg=t["main_bg"])
        self.single_canvas.configure(bg=t["main_bg"])
        self.preview_frame.configure(bg=t["root_bg"])
        self.preview_canvas.configure(bg=t["main_bg"])
        self.preview_ops_bar.configure(bg=t["panel_bg"], highlightbackground=t["border"], highlightthickness=1)
        self.bottom_bar.configure(bg=t["panel_bg"], highlightbackground=t["border"], highlightthickness=1)
        self.album_canvas.configure(bg=t["panel_bg"])
        self.album_frame.configure(bg=t["panel_bg"])
        self.status_bar.configure(bg=t["status_bg"], fg=t["subtext"])
        self.path_label.configure(bg=t["root_bg"], fg=t["text"])
        self.tree_label.configure(bg=t["panel_bg"], fg=t["subtext"])
        self.recent_ops_label.configure(bg=t["panel_bg"], fg=t["subtext"])
        self.recent_ops_list.configure(bg=t["card_bg"], fg=t["text"], selectbackground=t["accent_soft"], selectforeground=t["accent"], highlightbackground=t["border"], highlightthickness=1)
        self.brand_badge.configure(bg=t["accent"], fg="white")
        self.mode_label.configure(bg=t["root_bg"], fg=t["subtext"])
        self.selection_label.configure(bg=t["panel_bg"], fg=t["accent"])
        self.add_album_btn.configure(bg=t["accent"], fg="white", activebackground=t["accent_hover"])
        self.select_dir_btn.configure(bg=t["accent"], fg="white", activebackground=t["accent_hover"])
        for btn in (self.settings_btn, self.open_folder_btn, self.preview_toggle_btn, self.undo_btn):
            btn.configure(bg=t["card_bg"], fg=t["text"], activebackground=t["hover_bg"])

    def build_ui(self):
        self.configure_ttk()
        t = self.theme

        # ── 顶部栏：品牌 + 路径 + 右侧操作（飞书式） ──
        self.top_bar = tk.Frame(self.root, bg=t["root_bg"])
        self.top_bar.pack(fill=tk.X, padx=ui(18), pady=(ui(12), ui(8)))

        self.brand_badge = tk.Label(
            self.top_bar,
            text="  PicaPhoto",
            image=getattr(self, "brand_logo_image", None),
            compound=tk.LEFT,
            bg=t["accent"],
            fg="white",
            font=("Segoe UI", 10, "bold"),
            padx=ui(10),
            pady=ui(5),
            highlightthickness=0,
        )
        self.brand_badge.pack(side=tk.LEFT, padx=(0, ui(14)))

        self.path_label = tk.Label(self.top_bar, text="未选择目录", bg=t["root_bg"], fg=t["text"], font=("微软雅黑", 12, "bold"), anchor="w")
        self.path_label.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, ui(12)))

        self.mode_label = tk.Label(self.top_bar, text="单图模式 · 滚轮切换", bg=t["root_bg"], fg=t["subtext"], font=("微软雅黑", 10), anchor="e")
        self.mode_label.pack(side=tk.RIGHT, padx=(ui(12), 0))

        def _tool(parent, text, command, primary=False):
            kw = dict(
                command=command, relief=tk.FLAT, font=("微软雅黑", 10),
                padx=ui(10), pady=ui(5), bd=0, highlightthickness=0, cursor="hand2",
            )
            if primary:
                kw.update(bg=t["accent"], fg="white", activebackground=t["accent_hover"])
            else:
                kw.update(bg=t["card_bg"], fg=t["text"], activebackground=t["hover_bg"])
            return tk.Button(parent, text=text, **kw)

        # 右侧按钮组（从右到左：设置、撤销、预览、打开文件夹、选择目录）
        self.settings_btn = _tool(self.top_bar, "设置", self.open_settings_dialog)
        self.settings_btn.pack(side=tk.RIGHT, padx=(ui(6), 0))
        self.undo_btn = _tool(self.top_bar, "撤销 Ctrl+Z", self.undo_last_move)
        self.undo_btn.pack(side=tk.RIGHT, padx=(ui(6), 0))
        self.preview_toggle_btn = _tool(self.top_bar, "资源预览 Tab", self.toggle_preview_mode)
        self.preview_toggle_btn.pack(side=tk.RIGHT, padx=(ui(6), 0))
        self.open_folder_btn = _tool(self.top_bar, "打开文件夹", self.open_current_folder)
        self.open_folder_btn.pack(side=tk.RIGHT, padx=(ui(6), 0))
        self.select_dir_btn = _tool(self.top_bar, "选择目录", self.select_root_dir, primary=True)
        self.select_dir_btn.pack(side=tk.RIGHT, padx=(ui(6), 0))

        # ── 主体：左侧导航栏 + 右侧内容区（微信式侧栏） ──
        self.main_container = tk.Frame(self.root, bg=t["root_bg"])
        self.main_container.pack(fill=tk.BOTH, expand=True, padx=ui(18), pady=ui(4))

        self.sidebar_frame = tk.Frame(self.main_container, bg=t["panel_bg"], width=SIDEBAR_WIDTH, highlightbackground=t["border"], highlightthickness=1)
        self.sidebar_frame.pack(side=tk.LEFT, fill=tk.Y)
        self.sidebar_frame.pack_propagate(False)

        self.tree_label = tk.Label(self.sidebar_frame, text="资源目录", bg=t["panel_bg"], fg=t["subtext"], font=("微软雅黑", 10, "bold"), anchor="w")
        self.tree_label.pack(fill=tk.X, padx=ui(12), pady=(ui(12), ui(6)))

        self.tree = ttk.Treeview(self.sidebar_frame, show="tree")
        self.tree.pack(fill=tk.BOTH, expand=True, padx=ui(8), pady=(0, ui(6)))
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        self.tree.bind("<Button-3>", self.on_tree_right_click)

        tk.Frame(self.sidebar_frame, bg=t["divider"], height=1).pack(fill=tk.X, padx=ui(10), pady=(0, ui(4)))

        self.recent_ops_label = tk.Label(self.sidebar_frame, text="最近操作", bg=t["panel_bg"], fg=t["subtext"], font=("微软雅黑", 10, "bold"), anchor="w")
        self.recent_ops_label.pack(fill=tk.X, padx=ui(12), pady=(ui(4), ui(4)))
        recent_bar = tk.Frame(self.sidebar_frame, bg=t["panel_bg"])
        recent_bar.pack(fill=tk.BOTH, expand=False, padx=ui(8), pady=(0, ui(8)))
        self.recent_ops_list = tk.Listbox(recent_bar, height=8, bg=t["card_bg"], fg=t["text"], selectbackground=t["accent_soft"], selectforeground=t["accent"], highlightthickness=1, highlightbackground=t["border"], relief=tk.FLAT, font=("微软雅黑", 9))
        self.recent_ops_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.recent_scroll = ttk.Scrollbar(recent_bar, orient=tk.VERTICAL, command=self.recent_ops_list.yview)
        self.recent_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.recent_ops_list.configure(yscrollcommand=self.recent_scroll.set)
        self.recent_ops_list.bind("<Double-Button-1>", lambda e: self.open_current_folder())

        self.right_frame = tk.Frame(self.main_container, bg=t["root_bg"])
        self.right_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(ui(12), 0))

        # 单图模式画布
        self.single_frame = tk.Frame(self.right_frame, bg=t["main_bg"])
        self.single_frame.pack(fill=tk.BOTH, expand=True)
        self.single_canvas = tk.Canvas(self.single_frame, bg=t["main_bg"], highlightthickness=0)
        self.single_canvas.pack(fill=tk.BOTH, expand=True)
        self.single_canvas.bind("<Button-3>", self.on_single_right_click)

        # 预览模式
        self.preview_frame = tk.Frame(self.right_frame, bg=t["root_bg"])
        self.preview_canvas = tk.Canvas(self.preview_frame, bg=t["main_bg"], highlightthickness=0)
        self.preview_vbar = ttk.Scrollbar(self.preview_frame, orient=tk.VERTICAL, command=self.preview_canvas.yview)
        self.preview_canvas.configure(yscrollcommand=self.preview_vbar.set)
        self.preview_vbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.preview_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.preview_canvas.bind("<Button-1>", self.on_preview_left_click)
        self.preview_canvas.bind("<Double-Button-1>", self.on_preview_double_click)
        self.preview_canvas.bind("<Button-3>", self.on_preview_right_click)
        self.preview_canvas.bind("<MouseWheel>", self.on_preview_mousewheel)
        self.preview_canvas.bind("<Button-4>", self.on_preview_mousewheel)
        self.preview_canvas.bind("<Button-5>", self.on_preview_mousewheel)
        self.preview_canvas.bind("<Motion>", self.on_preview_motion)
        self.preview_canvas.bind("<Leave>", self.on_preview_leave)

        # 预览操作条
        self.preview_ops_bar = tk.Frame(self.root, bg=t["panel_bg"], height=ui(48), highlightbackground=t["border"], highlightthickness=1)
        self.selection_label = tk.Label(self.preview_ops_bar, text="0 个已选择", bg=t["panel_bg"], fg=t["accent"], font=("微软雅黑", 10, "bold"))
        self.selection_label.pack(side=tk.LEFT, padx=ui(16))
        ttk.Button(self.preview_ops_bar, text="全选", command=self.select_all_in_preview).pack(side=tk.LEFT, padx=ui(4))
        ttk.Button(self.preview_ops_bar, text="取消全选", command=self.clear_preview_selection).pack(side=tk.LEFT, padx=ui(4))
        ttk.Button(self.preview_ops_bar, text="批量移动", command=self.move_selected_to_album_dialog, style="Accent.TButton").pack(side=tk.LEFT, padx=ui(4))
        ttk.Button(self.preview_ops_bar, text="移回未整理", command=self.move_selected_back_to_unsorted).pack(side=tk.LEFT, padx=ui(4))
        ttk.Button(self.preview_ops_bar, text="关闭预览", command=self.exit_preview_mode).pack(side=tk.RIGHT, padx=ui(16))

        # 底部相册栏（卡片式）
        self.bottom_bar = tk.Frame(self.root, bg=t["panel_bg"], height=ALBUM_BAR_HEIGHT, highlightbackground=t["border"], highlightthickness=1)
        self.bottom_bar.pack(fill=tk.X, side=tk.BOTTOM, padx=ui(18), pady=(ui(6), ui(8)))

        self.add_album_btn = tk.Button(self.bottom_bar, text="＋ 新建相册", command=self.create_album_dialog, bg=t["accent"], fg="white", font=("微软雅黑", 10, "bold"), relief=tk.FLAT, activebackground=t["accent_hover"], bd=0, padx=ui(12), pady=ui(8), cursor="hand2")
        self.add_album_btn.pack(side=tk.LEFT, padx=(ui(12), ui(8)))

        self.album_canvas = tk.Canvas(self.bottom_bar, bg=t["panel_bg"], height=ALBUM_BAR_HEIGHT - ui(20), highlightthickness=0)
        self.album_hbar = ttk.Scrollbar(self.bottom_bar, orient=tk.HORIZONTAL, command=self.album_canvas.xview)
        self.album_canvas.configure(xscrollcommand=self.album_hbar.set)
        self.album_hbar.pack(side=tk.BOTTOM, fill=tk.X)
        self.album_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, ui(10)), pady=(ui(8), 0))
        self.album_canvas.bind("<MouseWheel>", self.on_album_mousewheel)
        self.album_canvas.bind("<Button-4>", self.on_album_mousewheel)
        self.album_canvas.bind("<Button-5>", self.on_album_mousewheel)

        self.album_frame = tk.Frame(self.album_canvas, bg=t["panel_bg"])
        self.album_canvas.create_window((0, 0), window=self.album_frame, anchor="nw")
        self.album_frame.bind("<Configure>", lambda e: self.album_canvas.configure(scrollregion=self.album_canvas.bbox("all")))

        # 状态栏（最底部，相册栏之下）
        self.status_bar = tk.Label(self.root, text="PicaPhoto 已就绪，请先选择目录", bg=t["status_bg"], fg=t["subtext"], anchor="w", padx=ui(18), pady=ui(6), font=("微软雅黑", 9))
        self.status_bar.pack(fill=tk.X, side=tk.BOTTOM, before=self.bottom_bar)

    def bind_hotkeys(self):
        for i in range(1, 10):
            self.root.bind(str(i), lambda e, idx=i - 1: self.handle_album_shortcut(idx))
        self.root.bind("<Right>", lambda e: self.skip_current() if not self.is_preview_mode else None)
        self.root.bind("<Left>", lambda e: self.prev_current() if not self.is_preview_mode else None)
        self.root.bind("<Control-z>", self.undo_last_move)
        self.root.bind("<Escape>", self.handle_escape)
        self.root.bind("<Tab>", lambda e: self.toggle_preview_mode() or "break")
        self.root.bind("<Control-a>", self.select_all_in_preview)
        self.root.bind("r", lambda e: self.rotate_current() if not self.is_preview_mode else None)
        self.root.bind("R", lambda e: self.rotate_current() if not self.is_preview_mode else None)
        self.root.bind("f", lambda e: self.flip_current() if not self.is_preview_mode else None)
        self.root.bind("F", lambda e: self.flip_current() if not self.is_preview_mode else None)
        self.single_canvas.bind("<MouseWheel>", self.on_single_mousewheel)
        self.single_canvas.bind("<Button-4>", self.on_single_mousewheel)
        self.single_canvas.bind("<Button-5>", self.on_single_mousewheel)

    # -------------------------- 目录与树 --------------------------
    def refresh_tree(self):
        self.tree_node_map.clear()
        self._suspend_tree_callback = True
        try:
            for item in self.tree.get_children():
                self.tree.delete(item)

            unsorted_root = self.tree.insert("", tk.END, text="📂 未整理", open=True)
            n_all = self.tree.insert(unsorted_root, tk.END, text=f"全部文件 ({self.get_file_count(self.root_dir, 'all')})")
            n_img = self.tree.insert(unsorted_root, tk.END, text=f"照片 ({self.get_file_count(self.root_dir, 'image')})")
            n_vid = self.tree.insert(unsorted_root, tk.END, text=f"视频 ({self.get_file_count(self.root_dir, 'video')})")
            self.tree_node_map[n_all] = ("unsorted", "all")
            self.tree_node_map[n_img] = ("unsorted", "image")
            self.tree_node_map[n_vid] = ("unsorted", "video")

            sorted_root = self.tree.insert("", tk.END, text="📂 已整理", open=True)
            for album in self.albums:
                folder = os.path.join(self.root_dir, album) if self.root_dir else ""
                node = self.tree.insert(sorted_root, tk.END, text=f"{album} ({self.get_file_count(folder, 'all')})")
                self.tree_node_map[node] = ("album", album)
        finally:
            self._suspend_tree_callback = False
        self.refresh_recent_ops_panel()
        self.is_animating = False
        self.anim_photo = None
        self.album_drag = {
            "album": None,
            "widget": None,
            "start_x": 0,
            "start_y": 0,
            "start_index": -1,
            "dragging": False,
            "target_index": -1,
            "ghost": None,
            "indicator": None,
            "click_block": False,
        }

    def select_unsorted_all_node(self, load=True):
        for node_id, value in self.tree_node_map.items():
            if value == ("unsorted", "all"):
                self.tree.selection_set(node_id)
                self.tree.focus(node_id)
                self.tree.see(node_id)
                if load:
                    self.load_from_tree_selection()
                return

    def select_album_node(self, album_name: str):
        for node_id, value in self.tree_node_map.items():
            if value == ("album", album_name):
                self.tree.selection_set(node_id)
                self.tree.focus(node_id)
                self.tree.see(node_id)
                self.load_from_tree_selection()
                return

    def on_tree_select(self, event=None):
        if self._suspend_tree_callback:
            return
        self.load_from_tree_selection()

    def load_from_tree_selection(self):
        selected = self.tree.selection()
        if not selected:
            return
        value = self.tree_node_map.get(selected[0])
        if not value:
            return
        kind, arg = value
        self.selected_files.clear()
        self.last_selected_idx = -1
        self.update_selection_label()

        if kind == "unsorted":
            self.current_dir = self.root_dir
            self.current_filter = arg
            self.status(f"已切换到未整理 / {arg}")
        else:
            self.current_dir = os.path.join(self.root_dir, arg)
            self.current_filter = "all"
            self.status(f"已切换到相册 / {arg}")

        self.scan_and_show(ask_restore=False)

    def on_tree_right_click(self, event):
        item = self.tree.identify_row(event.y)
        if not item:
            return
        self.tree.selection_set(item)
        value = self.tree_node_map.get(item)
        if not value or value[0] != "album":
            return
        album = value[1]
        menu = tk.Menu(self.root, tearoff=0, bg=self.theme["card_bg"], fg=self.theme["text"], activebackground=self.theme["hover_bg"])
        menu.add_command(label="打开相册", command=lambda a=album: self.select_album_node(a))
        menu.add_command(label="打开文件夹", command=lambda a=album: self.open_folder_path(os.path.join(self.root_dir, a)))
        menu.add_command(label="删除相册项", command=lambda a=album: self.delete_album_entry(a))
        menu.post(event.x_root, event.y_root)

    def open_folder_path(self, path: str):
        if not path or not os.path.exists(path):
            messagebox.showwarning("提示", "路径不存在")
            return
        try:
            if os.name == "nt":
                os.startfile(path)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", path])
            else:
                subprocess.Popen(["xdg-open", path])
        except Exception as exc:
            messagebox.showerror("错误", f"打开失败：{exc}")

    def open_file_path(self, path: str):
        if not path or not os.path.exists(path):
            messagebox.showwarning("提示", "文件不存在")
            return
        try:
            if os.name == "nt":
                os.startfile(path)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", path])
            else:
                subprocess.Popen(["xdg-open", path])
        except Exception as exc:
            messagebox.showerror("错误", f"打开失败：{exc}")

    def open_current_folder(self):
        path = self.current_dir or self.root_dir
        if not path:
            messagebox.showwarning("提示", "请先选择目录")
            return
        self.open_folder_path(path)

    def open_current_file(self):
        if not self.current_files:
            messagebox.showwarning("提示", "当前没有可打开的文件")
            return
        if self.current_idx < 0 or self.current_idx >= len(self.current_files):
            messagebox.showwarning("提示", "当前没有可打开的文件")
            return
        path = os.path.join(self.current_dir, self.current_files[self.current_idx])
        self.open_file_path(path)

    def on_single_right_click(self, event=None):
        menu = tk.Menu(self.root, tearoff=0, bg=self.theme["card_bg"], fg=self.theme["text"], activebackground=self.theme["hover_bg"])
        menu.add_command(label="打开当前文件", command=self.open_current_file)
        menu.add_command(label="打开当前文件夹", command=self.open_current_folder)
        try:
            menu.post(event.x_root, event.y_root)
        except Exception:
            menu.post(self.root.winfo_pointerx(), self.root.winfo_pointery())

    # -------------------------- 目录选择与扫描 --------------------------
    def select_root_dir(self):
        folder = filedialog.askdirectory()
        if not folder:
            return
        self.root_dir = folder
        self.current_dir = folder
        self.current_filter = "all"
        self.current_idx = 0
        self.selected_files.clear()
        self.last_selected_idx = -1
        self.preview_photo_refs.clear()
        self.thumb_pil_cache.clear()
        self.single_preview_cache.clear()
        self.preview_thumb_item_ids.clear()
        self.preview_thumb_source_pil.clear()
        self.stop_hover_video_preview()
        self.path_label.configure(text=folder)
        self.sync_albums_from_root_folders()
        self.refresh_tree()
        self.refresh_album_bar()
        self.select_unsorted_all_node(load=False)
        self.scan_and_show(ask_restore=True)

    def scan_current_files(self):
        files = []
        if not self.current_dir or not os.path.isdir(self.current_dir):
            return files
        for name in os.listdir(self.current_dir):
            full = os.path.join(self.current_dir, name)
            if not os.path.isfile(full):
                continue
            lower = name.lower()
            if self.current_filter == "all" and lower.endswith(self.get_media_ext()):
                files.append(name)
            elif self.current_filter == "image" and lower.endswith(self.get_image_ext()):
                files.append(name)
            elif self.current_filter == "video" and lower.endswith(self.get_video_ext()):
                files.append(name)
        files.sort(key=str.lower)
        return files

    def scan_and_show(self, ask_restore=False):
        if not self.current_dir:
            return
        self.current_scan_token += 1
        token = self.current_scan_token
        self.status("正在扫描文件…")

        def job():
            return self.scan_current_files()

        def done(files):
            if token != self.current_scan_token:
                return
            self.current_files = files
            max_valid = max(0, len(files) - 1)
            if ask_restore and self.current_dir == self.root_dir:
                saved = int(self.config.get("progress", {}).get(self.root_dir, 0))
                if 0 < saved <= max_valid:
                    if messagebox.askyesno("恢复进度", f"检测到上次整理到第 {saved + 1} 张，是否恢复？"):
                        self.current_idx = saved
                    else:
                        self.current_idx = 0
                else:
                    self.current_idx = min(self.current_idx, max_valid)
            else:
                self.current_idx = min(self.current_idx, max_valid) if files else 0
            self.refresh_tree()
            self.refresh_album_bar()
            if self.is_preview_mode:
                self.refresh_preview_grid()
            else:
                self.refresh_single_view()

        self.run_async(job, done, lambda e: self.status(f"扫描失败：{e}"))

    def get_file_count(self, folder_path: str, filter_type="all"):
        if not folder_path or not os.path.isdir(folder_path):
            return 0
        count = 0
        for name in os.listdir(folder_path):
            full = os.path.join(folder_path, name)
            if not os.path.isfile(full):
                continue
            lower = name.lower()
            if filter_type == "all" and lower.endswith(self.get_media_ext()):
                count += 1
            elif filter_type == "image" and lower.endswith(self.get_image_ext()):
                count += 1
            elif filter_type == "video" and lower.endswith(self.get_video_ext()):
                count += 1
        return count


    def sync_albums_from_root_folders(self):
        if not self.root_dir or not os.path.isdir(self.root_dir):
            return
        subfolders = []
        try:
            for name in os.listdir(self.root_dir):
                full = os.path.join(self.root_dir, name)
                if os.path.isdir(full):
                    subfolders.append(name)
        except Exception:
            return

        # 已存在于目录中的文件夹自动作为已整理相册载入；保留当前手动排序，新增文件夹追加到末尾
        current = [name for name in self.albums if name in subfolders]
        extras = [name for name in sorted(subfolders, key=str.lower) if name not in current]
        self.albums = current + extras
        self.save_config()

    # -------------------------- 单图模式 --------------------------
    def refresh_single_view(self):
        self.current_single_token += 1
        token = self.current_single_token
        self.single_canvas.delete("all")
        if not self.current_files:
            if not self.root_dir:
                empty_text = "请先选择目录，开始整理照片与视频"
            else:
                empty_text = "当前目录没有可整理的媒体文件"
            self.single_canvas.create_text(
                max(ui(200), self.single_canvas.winfo_width() // 2),
                max(ui(120), self.single_canvas.winfo_height() // 2),
                text=empty_text,
                fill=self.theme["text"],
                font=("微软雅黑", 16, "bold"),
            )
            self.mode_label.configure(text="单图模式")
            self.status(empty_text)
            return

        self.current_idx = max(0, min(self.current_idx, len(self.current_files) - 1))
        self.status(f"共 {len(self.current_files)} 个媒体文件 · 第 {self.current_idx + 1}/{len(self.current_files)} 个")
        filename = self.current_files[self.current_idx]
        path = os.path.join(self.current_dir, filename)
        is_video = path.lower().endswith(self.get_video_ext())
        self.mode_label.configure(text="单图模式")
        key = self.get_single_cache_key(path)

        if key in self.single_preview_cache:
            self.render_single_media(self.single_preview_cache[key], filename, is_video, token)
            return

        def job():
            return self.load_media_preview_sync(path, (1280, 900))

        def done(img):
            try:
                self.single_preview_cache[key] = img.copy()
            except Exception:
                pass
            self.render_single_media(img, filename, is_video, token)

        self.run_async(job, done, lambda e: self.status(f"加载失败：{e}"))

    def save_progress(self):
        if self.root_dir and self.current_dir == self.root_dir:
            self.config.setdefault("progress", {})[self.root_dir] = self.current_idx
            self.save_config()

    def skip_current(self):
        if not self.current_files:
            return
        self.current_idx = min(self.current_idx + 1, len(self.current_files) - 1)
        self.status("已跳到下一项")
        self.refresh_single_view()

    def prev_current(self):
        if not self.current_files:
            return
        self.current_idx = max(self.current_idx - 1, 0)
        self.refresh_single_view()

    def rotate_current(self):
        if self.is_preview_mode or self.temp_single_image is None:
            return
        self.temp_single_image = self.temp_single_image.rotate(-90, expand=True)
        img = self.temp_single_image.copy()
        width = max(600, self.single_canvas.winfo_width() - 60)
        height = max(400, self.single_canvas.winfo_height() - 80)
        img.thumbnail((width, height), Image.Resampling.LANCZOS)
        self.single_photo = ImageTk.PhotoImage(img)
        self.single_canvas.delete("all")
        self.single_canvas.create_image(self.single_canvas.winfo_width() // 2, self.single_canvas.winfo_height() // 2, image=self.single_photo, anchor=tk.CENTER)
        self.status("已临时旋转预览")

    def flip_current(self):
        if self.is_preview_mode or self.temp_single_image is None:
            return
        self.temp_single_image = ImageOps.mirror(self.temp_single_image)
        img = self.temp_single_image.copy()
        width = max(600, self.single_canvas.winfo_width() - 60)
        height = max(400, self.single_canvas.winfo_height() - 80)
        img.thumbnail((width, height), Image.Resampling.LANCZOS)
        self.single_photo = ImageTk.PhotoImage(img)
        self.single_canvas.delete("all")
        self.single_canvas.create_image(self.single_canvas.winfo_width() // 2, self.single_canvas.winfo_height() // 2, image=self.single_photo, anchor=tk.CENTER)
        self.status("已临时镜像预览")

    # -------------------------- 预览模式 --------------------------
    def enter_preview_mode(self):
        if self.is_preview_mode:
            return
        self.is_preview_mode = True
        self.single_frame.pack_forget()
        self.preview_frame.pack(fill=tk.BOTH, expand=True)
        self.preview_ops_bar.pack(fill=tk.X, padx=14, pady=(0, 6), before=self.bottom_bar)
        self.preview_toggle_btn.configure(text="关闭预览 Esc")
        self.mode_label.configure(text="预览模式")
        self.root.after(30, self.refresh_preview_grid)

    def exit_preview_mode(self, event=None):
        if not self.is_preview_mode:
            return
        self.is_preview_mode = False
        self.preview_frame.pack_forget()
        self.preview_ops_bar.pack_forget()
        self.single_frame.pack(fill=tk.BOTH, expand=True)
        self.preview_toggle_btn.configure(text="资源预览 Tab")
        self.mode_label.configure(text="单图模式")
        self.selected_files.clear()
        self.last_selected_idx = -1
        self.update_selection_label()
        self.refresh_single_view()

    def toggle_preview_mode(self):
        if self.is_preview_mode:
            self.exit_preview_mode()
        else:
            self.enter_preview_mode()
        return "break"

    def build_video_placeholder(self):
        img = Image.new("RGB", THUMB_SIZE, self.theme["card_bg"])
        draw = ImageDraw.Draw(img)
        try:
            font = ImageFont.truetype("msyh.ttc", ui(20))
        except Exception:
            font = ImageFont.load_default()
        draw.rounded_rectangle((ui(10), ui(10), THUMB_SIZE[0] - ui(10), THUMB_SIZE[1] - ui(10)), radius=ui(18), outline=self.theme["border"], width=2, fill=self.theme["panel_bg"])
        draw.polygon([(ui(60), ui(50)), (ui(60), ui(110)), (ui(112), ui(80))], fill=self.theme["accent"])
        draw.text((THUMB_SIZE[0] // 2, THUMB_SIZE[1] - ui(22)), "VIDEO", fill=self.theme["text"], anchor="mm", font=font)
        self.video_placeholder_pil = self._rounded_pil(img, ui(10))
        self.video_placeholder_photo = ImageTk.PhotoImage(self.video_placeholder_pil)

    def get_video_preview_pil(self, path: str, max_size=None):
        if cv2 is None:
            return self.video_placeholder_pil.copy()
        cap = None
        try:
            cap = cv2.VideoCapture(path)
            if not cap.isOpened():
                return self.video_placeholder_pil.copy()

            frame_count = int(cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0)
            candidate_frames = [0, 1, 3, 5, 10]
            if frame_count > 1:
                candidate_frames.extend([max(0, frame_count // 10), max(0, frame_count // 4)])

            frame = None
            for pos in candidate_frames:
                if frame_count > 0:
                    pos = min(pos, max(0, frame_count - 1))
                cap.set(cv2.CAP_PROP_POS_FRAMES, pos)
                ok, current = cap.read()
                if not ok or current is None:
                    continue
                # 跳过几乎全黑的首帧/转场帧
                try:
                    if float(current.mean()) < 3:
                        continue
                except Exception:
                    pass
                frame = current
                break

            if frame is None:
                cap.set(cv2.CAP_PROP_POS_FRAMES, 0)
                ok, current = cap.read()
                if not ok or current is None:
                    return self.video_placeholder_pil.copy()
                frame = current

            frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            img = Image.fromarray(frame)
            if max_size:
                img.thumbnail(max_size, Image.Resampling.LANCZOS)
            return img
        except Exception:
            return self.video_placeholder_pil.copy()
        finally:
            if cap is not None:
                try:
                    cap.release()
                except Exception:
                    pass

    def get_preview_item_from_event(self, event):
        current = self.preview_canvas.find_withtag("current")
        if not current:
            return None
        tags = self.preview_canvas.gettags(current[0])
        for tag in tags:
            if tag.startswith("item_"):
                try:
                    return int(tag.split("_")[1])
                except Exception:
                    return None
        return None

    def on_preview_left_click(self, event):
        idx = self.get_preview_item_from_event(event)
        if idx is None or idx >= len(self.current_files):
            return
        filename = self.current_files[idx]
        ctrl = bool(event.state & 0x4)
        shift = bool(event.state & 0x1)
        if shift and self.last_selected_idx >= 0:
            start = min(self.last_selected_idx, idx)
            end = max(self.last_selected_idx, idx)
            for i in range(start, end + 1):
                self.selected_files.add(self.current_files[i])
        elif ctrl:
            if filename in self.selected_files:
                self.selected_files.remove(filename)
            else:
                self.selected_files.add(filename)
            self.last_selected_idx = idx
        else:
            self.selected_files = {filename}
            self.last_selected_idx = idx
        self.update_selection_label()
        self.refresh_preview_grid()

    def on_preview_double_click(self, event):
        idx = self.get_preview_item_from_event(event)
        if idx is None or idx >= len(self.current_files):
            return
        filename = self.current_files[idx]
        path = os.path.join(self.current_dir, filename)
        win = Toplevel(self.root)
        win.title(f"PicaPhoto 预览 · {filename}")
        win.geometry("1200x800")
        win.configure(bg=self.theme["main_bg"])
        self.apply_window_icon(win)
        self.center_window(win, 1200, 800, self.root)
        canvas = tk.Canvas(win, bg=self.theme["main_bg"], highlightthickness=0)
        canvas.pack(fill=tk.BOTH, expand=True)

        def render():
            try:
                width = max(400, canvas.winfo_width() - 40)
                height = max(300, canvas.winfo_height() - 40)
                if path.lower().endswith(self.get_video_ext()):
                    img = self.get_video_preview_pil(path, (width, height))
                else:
                    img = Image.open(path)
                    img = ImageOps.exif_transpose(img)
                    img.thumbnail((width, height), Image.Resampling.LANCZOS)
                photo = ImageTk.PhotoImage(img)
                canvas.delete("all")
                canvas.create_image(canvas.winfo_width() // 2, canvas.winfo_height() // 2, image=photo, anchor=tk.CENTER)
                if path.lower().endswith(self.get_video_ext()):
                    dur = self.get_video_info(path).get("duration", "")
                    tip = f"视频首帧预览  ·  时长 {dur}" if dur else "视频首帧预览"
                    canvas.create_text(canvas.winfo_width() // 2, 28, text=tip, fill=self.theme["text"], font=("微软雅黑", 10, "bold"))
                canvas.image = photo
            except Exception as exc:
                canvas.delete("all")
                canvas.create_text(200, 120, text=f"预览失败：{exc}", fill=self.theme["text"], anchor="nw")

        win.bind("<Configure>", lambda e: render())
        win.bind("<Escape>", lambda e: win.destroy())
        render()

    def on_preview_right_click(self, event):
        idx = self.get_preview_item_from_event(event)
        clicked_name = None
        if idx is not None and idx < len(self.current_files):
            clicked_name = self.current_files[idx]
            if clicked_name not in self.selected_files:
                self.selected_files = {clicked_name}
                self.last_selected_idx = idx
                self.update_selection_label()
                self.refresh_preview_grid()

        menu = tk.Menu(self.root, tearoff=0, bg=self.theme["card_bg"], fg=self.theme["text"], activebackground=self.theme["hover_bg"])

        if clicked_name:
            file_path = os.path.join(self.current_dir, clicked_name)
            menu.add_command(label="打开文件", command=lambda p=file_path: self.open_file_path(p))

        menu.add_command(label="打开当前文件夹", command=self.open_current_folder)

        if self.selected_files:
            menu.add_separator()
            menu.add_command(label="移动到相册", command=self.move_selected_to_album_dialog)
            if self.current_dir != self.root_dir:
                menu.add_command(label="移回未整理", command=self.move_selected_back_to_unsorted)
            menu.add_separator()
            menu.add_command(label="取消全选", command=self.clear_preview_selection)

        menu.post(event.x_root, event.y_root)

    def on_preview_mousewheel(self, event):
        if getattr(event, "num", None) == 4:
            self.preview_canvas.yview_scroll(-1, "units")
        elif getattr(event, "num", None) == 5:
            self.preview_canvas.yview_scroll(1, "units")
        else:
            self.preview_canvas.yview_scroll(-int(event.delta / 120), "units")


    def clear_runtime_caches(self, refresh_view=True):
        self.stop_hover_video_preview(restore=False)
        self.thumb_pil_cache.clear()
        self.single_preview_cache.clear()
        self.preview_thumb_item_ids.clear()
        self.preview_thumb_source_pil.clear()
        self.video_info_cache.clear()
        self.hover_video_frames_cache.clear()
        self.loading_previews.clear()
        self.single_loading_keys.clear()
        if refresh_view:
            if self.is_preview_mode:
                self.refresh_preview_grid()
            else:
                self.refresh_single_view()

    def on_preview_motion(self, event):
        if not self.is_preview_mode:
            return
        idx = self.get_preview_item_from_event(event)
        if idx is None or idx >= len(self.current_files):
            self.stop_hover_video_preview()
            return
        filename = self.current_files[idx]
        if not filename.lower().endswith(self.get_video_ext()):
            self.stop_hover_video_preview()
            return
        if self.hover_state.get("idx") == idx:
            return
        self.start_hover_video_preview(idx)

    def on_preview_leave(self, event=None):
        self.stop_hover_video_preview()

    def prepare_hover_video_frames_sync(self, path: str):
        cache_key = (path, os.path.getmtime(path) if os.path.exists(path) else 0, "hover")
        if cache_key in self.hover_video_frames_cache:
            return self.hover_video_frames_cache[cache_key]
        if cv2 is None or not os.path.exists(path):
            return []
        cap = None
        frames = []
        try:
            cap = cv2.VideoCapture(path)
            if not cap or not cap.isOpened():
                return []
            frame_count = int(cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0)
            if frame_count <= 0:
                return []
            sample_count = 6
            positions = []
            for i in range(sample_count):
                pos = int((frame_count - 1) * (i / max(1, sample_count - 1)))
                positions.append(max(0, pos))
            seen = set()
            for pos in positions:
                if pos in seen:
                    continue
                seen.add(pos)
                cap.set(cv2.CAP_PROP_POS_FRAMES, pos)
                ok, frame = cap.read()
                if not ok or frame is None:
                    continue
                frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                img = Image.fromarray(frame)
                img.thumbnail(THUMB_SIZE, Image.Resampling.LANCZOS)
                frames.append(img)
        except Exception:
            frames = []
        finally:
            if cap is not None:
                try:
                    cap.release()
                except Exception:
                    pass
        self.hover_video_frames_cache[cache_key] = frames
        return frames

    def start_hover_video_preview(self, idx: int):
        self.stop_hover_video_preview()
        if idx < 0 or idx >= len(self.current_files):
            return
        filename = self.current_files[idx]
        path = os.path.join(self.current_dir, filename)
        item_id = self.preview_thumb_item_ids.get(idx)
        if item_id is None:
            return
        token = self.hover_state.get("token", 0) + 1
        self.hover_state = {"idx": idx, "job": None, "photos": [], "token": token}

        def job():
            return self.prepare_hover_video_frames_sync(path)

        def done(frames):
            if self.hover_state.get("token") != token:
                return
            if not frames:
                return
            photos = [ImageTk.PhotoImage(img) for img in frames]
            self.hover_state["photos"] = photos

            def animate(frame_idx=0):
                if self.hover_state.get("token") != token:
                    return
                current_item_id = self.preview_thumb_item_ids.get(idx)
                if current_item_id is None:
                    return
                if not photos:
                    return
                self.preview_canvas.itemconfigure(current_item_id, image=photos[frame_idx % len(photos)])
                job_id = self.root.after(120, lambda: animate(frame_idx + 1))
                self.hover_state["job"] = job_id

            animate()

        self.run_async(job, done)

    def stop_hover_video_preview(self, restore=True):
        job_id = self.hover_state.get("job")
        if job_id:
            try:
                self.root.after_cancel(job_id)
            except Exception:
                pass
        idx = self.hover_state.get("idx")
        if restore and idx is not None:
            item_id = self.preview_thumb_item_ids.get(idx)
            pil_img = self.preview_thumb_source_pil.get(idx)
            if item_id is not None and pil_img is not None:
                photo = ImageTk.PhotoImage(pil_img)
                self.preview_photo_refs.append(photo)
                try:
                    self.preview_canvas.itemconfigure(item_id, image=photo)
                except Exception:
                    pass
        self.hover_state = {"idx": None, "job": None, "photos": [], "token": self.hover_state.get("token", 0) + 1}

    def refresh_preview_grid(self):
        self.current_preview_token += 1
        token = self.current_preview_token
        self.stop_hover_video_preview()
        self.preview_canvas.delete("all")
        self.preview_photo_refs = []
        self.preview_index_map = {}
        self.preview_thumb_item_ids = {}
        self.preview_thumb_source_pil = {}

        if not self.current_files:
            if not self.root_dir:
                empty_text = "请先选择目录，开始整理照片与视频"
            else:
                empty_text = "当前目录没有可预览的媒体文件"
            self.preview_canvas.create_text(
                max(ui(220), self.preview_canvas.winfo_width() // 2),
                max(ui(120), self.preview_canvas.winfo_height() // 2),
                text=empty_text,
                fill=self.theme["text"],
                font=("微软雅黑", 16, "bold"),
            )
            self.status(empty_text)
            return
        self.status(f"预览模式 · 共 {len(self.current_files)} 个媒体文件")

        canvas_width = max(800, self.preview_canvas.winfo_width())
        cell_w = THUMB_SIZE[0] + PREVIEW_GAP * 2
        cell_h = THUMB_SIZE[1] + ui(74)
        cols = max(1, canvas_width // cell_w)

        for idx, filename in enumerate(self.current_files):
            row = idx // cols
            col = idx % cols
            x = col * cell_w + PREVIEW_GAP
            y = row * cell_h + PREVIEW_GAP
            x2 = x + THUMB_SIZE[0]
            y2 = y + THUMB_SIZE[1]
            selected = filename in self.selected_files
            border = self.theme["accent"] if selected else self.theme["border"]
            fill = self.theme["card_bg"]
            self.preview_canvas.create_rectangle(x, y, x2, y2, fill=fill, outline=border, width=2, tags=(f"item_{idx}",))
            self.preview_canvas.create_text(x + 8, y + 10, text="加载中…", fill=self.theme["subtext"], anchor="nw", font=("微软雅黑", 9), tags=(f"item_{idx}", f"loading_{idx}"))
            short_name = filename if len(filename) <= 20 else filename[:18] + "…"
            self.preview_canvas.create_text(x, y2 + 8, text=short_name, fill=self.theme["text"], anchor="nw", font=("微软雅黑", 9), width=THUMB_SIZE[0], tags=(f"item_{idx}",))
            if filename.lower().endswith(self.get_video_ext()):
                duration_text = self.get_video_info(os.path.join(self.current_dir, filename)).get("duration", "")
                if duration_text:
                    self.preview_canvas.create_text(x, y2 + 30, text=f"时长 {duration_text}", fill=self.theme["subtext"], anchor="nw", font=("微软雅黑", 8), width=THUMB_SIZE[0], tags=(f"item_{idx}",))
            if selected:
                self.preview_canvas.create_oval(x2 - 24, y + 6, x2 - 6, y + 24, fill=self.theme["yellow"], outline="")
                self.preview_canvas.create_text(x2 - 15, y + 15, text="✓", fill="black", font=("微软雅黑", 10, "bold"), tags=(f"item_{idx}",))
            self.preview_index_map[idx] = (x, y)
            self.load_thumbnail_async(token, idx, filename, x, y)

        rows = (len(self.current_files) + cols - 1) // cols
        self.preview_canvas.configure(scrollregion=(0, 0, canvas_width, rows * cell_h + PREVIEW_GAP))

    def load_thumbnail_async(self, token: int, idx: int, filename: str, x: int, y: int):
        path = os.path.join(self.current_dir, filename)
        cache_key = (path, os.path.getmtime(path) if os.path.exists(path) else 0)

        if cache_key in self.thumb_pil_cache:
            self.render_thumb(token, idx, filename, x, y, self.thumb_pil_cache[cache_key])
            return

        if cache_key in self.loading_previews:
            return
        self.loading_previews.add(cache_key)

        def job():
            try:
                if path.lower().endswith(self.get_video_ext()):
                    img = self.get_video_preview_pil(path, THUMB_SIZE)
                else:
                    img = Image.open(path)
                    img = ImageOps.exif_transpose(img)
                    img.thumbnail(THUMB_SIZE, Image.Resampling.LANCZOS)
                return self._rounded_pil(img, ui(10))
            except Exception:
                return None

        def done(pil_img):
            self.loading_previews.discard(cache_key)
            if pil_img is None:
                self.render_thumb_failed(token, idx, filename)
                return
            self.thumb_pil_cache[cache_key] = pil_img.copy()
            self.render_thumb(token, idx, filename, x, y, pil_img)

        self.run_async(job, done)

    def render_thumb(self, token: int, idx: int, filename: str, x: int, y: int, pil_img: Image.Image):
        if token != self.current_preview_token or idx >= len(self.current_files):
            return
        if self.current_files[idx] != filename:
            return
        self.preview_canvas.delete(f"loading_{idx}")
        photo = ImageTk.PhotoImage(pil_img)
        self.preview_photo_refs.append(photo)
        px = x + (THUMB_SIZE[0] - photo.width()) // 2
        py = y + (THUMB_SIZE[1] - photo.height()) // 2
        img_id = self.preview_canvas.create_image(px, py, image=photo, anchor="nw", tags=(f"item_{idx}", f"thumbimg_{idx}"))
        self.preview_thumb_item_ids[idx] = img_id
        try:
            self.preview_thumb_source_pil[idx] = pil_img.copy()
        except Exception:
            self.preview_thumb_source_pil[idx] = pil_img
        if filename.lower().endswith(self.get_video_ext()):
            duration_text = self.get_video_info(os.path.join(self.current_dir, filename)).get("duration", "")
            if duration_text:
                bx1, by1, bx2, by2 = px + max(0, photo.width() - 64), py + max(0, photo.height() - 24), px + photo.width() - 4, py + photo.height() - 6
                self.preview_canvas.create_rectangle(bx1, by1, bx2, by2, fill="#000000", outline="", stipple="gray50", tags=(f"item_{idx}",))
                self.preview_canvas.create_text((bx1+bx2)/2, (by1+by2)/2, text=duration_text, fill="white", font=("微软雅黑", 8, "bold"), tags=(f"item_{idx}",))

    def _rounded_pil(self, img: Image.Image, radius: int) -> Image.Image:
        """给 PIL 图像加圆角（四角透明），用于缩略图/占位图。"""
        try:
            if img.mode != "RGBA":
                img = img.convert("RGBA")
            mask = Image.new("L", img.size, 0)
            d = ImageDraw.Draw(mask)
            d.rounded_rectangle((0, 0, img.width - 1, img.height - 1), radius=max(1, radius), fill=255)
            img.putalpha(mask)
        except Exception:
            pass
        return img

    def render_thumb_failed(self, token: int, idx: int, filename: str):
        """缩略图读取失败时，在该格显示占位提示而不是一直停留“加载中…”。"""
        if token != self.current_preview_token or idx >= len(self.current_files):
            return
        if self.current_files[idx] != filename:
            return
        self.preview_canvas.delete(f"loading_{idx}")
        x, y = self.preview_index_map.get(idx, (0, 0))
        self.preview_canvas.create_text(
            x + THUMB_SIZE[0] // 2, y + THUMB_SIZE[1] // 2,
            text="无法读取", fill=self.theme["subtext"], anchor="center",
            font=("微软雅黑", 9), tags=(f"item_{idx}",))

    def update_selection_label(self):
        self.selection_label.configure(text=f"{len(self.selected_files)} 个已选择")

    def select_all_in_preview(self, event=None):
        if not self.is_preview_mode:
            return "break"
        self.selected_files = set(self.current_files)
        self.last_selected_idx = len(self.current_files) - 1 if self.current_files else -1
        self.update_selection_label()
        self.refresh_preview_grid()
        return "break"

    def clear_preview_selection(self):
        self.selected_files.clear()
        self.last_selected_idx = -1
        self.update_selection_label()
        if self.is_preview_mode:
            self.refresh_preview_grid()

    # -------------------------- 相册栏 --------------------------
    def refresh_album_bar(self):
        for widget in self.album_frame.winfo_children():
            widget.destroy()
        self.album_btn_map.clear()
        self.album_card_map = {}
        for idx, album in enumerate(self.albums):
            frame = tk.Frame(self.album_frame, bg=self.theme["panel_bg"], bd=0, highlightthickness=0)
            frame.pack(side=tk.LEFT, padx=ui(8), pady=ui(8))

            card = tk.Frame(frame, bg=self.theme["card_bg"], highlightbackground=self.theme["border"], highlightthickness=1, bd=0)
            card.pack()

            btn = tk.Label(
                card,
                text=album,
                relief=tk.FLAT,
                bg=self.theme["card_bg"],
                fg=self.theme["text"],
                font=("微软雅黑", 10, "bold"),
                padx=ui(14),
                pady=ui(8),
                cursor="hand2",
            )
            btn.pack(fill=tk.X)

            count = self.get_file_count(os.path.join(self.root_dir, album), "all") if self.root_dir else 0
            hotkey = f"快捷键 {idx + 1}" if idx < 9 else ""
            info = f"{count} 项"
            if hotkey:
                info += f"  ·  {hotkey}"
            info_label = tk.Label(frame, text=info, bg=self.theme["panel_bg"], fg=self.theme["subtext"], font=("微软雅黑", 9))
            info_label.pack(pady=(ui(4), 0))

            for widget in (frame, card, btn, info_label):
                widget.bind("<Enter>", lambda e, b=btn, c=card: (b.configure(bg=self.theme["hover_bg"]), c.configure(bg=self.theme["hover_bg"], highlightbackground=self.theme["hover_bg"])))
                widget.bind("<Leave>", lambda e, b=btn, c=card: (b.configure(bg=self.theme["card_bg"]), c.configure(bg=self.theme["card_bg"], highlightbackground=self.theme["border"])))
                widget.bind("<ButtonPress-1>", lambda e, a=album, c=frame: self.start_album_drag(e, a, c))
                widget.bind("<B1-Motion>", self.on_album_drag_motion)
                widget.bind("<ButtonRelease-1>", self.end_album_drag)
                widget.bind("<Button-3>", lambda e, a=album: self.on_album_right_click(e, a))

            self.album_btn_map[album] = btn
            self.album_card_map[album] = frame
        self.album_canvas.update_idletasks()
        self.album_canvas.configure(scrollregion=self.album_canvas.bbox("all"))

    def on_album_mousewheel(self, event):
        if getattr(event, "num", None) == 4:
            self.album_canvas.xview_scroll(-2, "units")
        elif getattr(event, "num", None) == 5:
            self.album_canvas.xview_scroll(2, "units")
        else:
            self.album_canvas.xview_scroll(-int(event.delta / 120) * 2, "units")

    def start_album_drag(self, event, album_name: str, widget=None):
        if album_name not in self.albums:
            return
        self.clear_album_drag_visuals()
        self.album_drag = {
            "album": album_name,
            "widget": widget,
            "start_x": event.x_root,
            "start_y": event.y_root,
            "start_index": self.albums.index(album_name),
            "dragging": False,
            "target_index": self.albums.index(album_name),
            "ghost": None,
            "indicator": None,
            "click_block": False,
        }

    def clear_album_drag_visuals(self):
        ghost = self.album_drag.get("ghost")
        if ghost is not None:
            try:
                ghost.destroy()
            except Exception:
                pass
        indicator = self.album_drag.get("indicator")
        if indicator is not None:
            try:
                self.album_canvas.delete(indicator)
            except Exception:
                pass

    def create_album_drag_ghost(self, album_name: str):
        ghost = tk.Toplevel(self.root)
        ghost.overrideredirect(True)
        ghost.attributes("-topmost", True)
        try:
            ghost.attributes("-alpha", 0.88)
        except Exception:
            pass
        outer = tk.Frame(ghost, bg=self.theme["accent"], bd=0)
        outer.pack()
        inner = tk.Frame(outer, bg=self.theme["card_bg"], padx=14, pady=10)
        inner.pack(padx=2, pady=2)
        tk.Label(inner, text=album_name, bg=self.theme["card_bg"], fg=self.theme["text"], font=("微软雅黑", 10, "bold")).pack()
        return ghost

    def show_album_insert_indicator(self, target_index: int):
        try:
            if self.album_drag.get("indicator") is not None:
                self.album_canvas.delete(self.album_drag["indicator"])
        except Exception:
            pass
        cards = [self.album_card_map.get(name) for name in self.albums if self.album_card_map.get(name)]
        if not cards:
            return
        self.album_canvas.update_idletasks()
        if target_index >= len(cards):
            ref = cards[-1]
            x = ref.winfo_x() + ref.winfo_width() + 3
        else:
            ref = cards[target_index]
            x = ref.winfo_x() - 3
        y1 = 6
        y2 = max(40, self.album_canvas.winfo_height() - 10)
        indicator = self.album_canvas.create_rectangle(x, y1, x + 4, y2, fill=self.theme["accent"], outline="")
        self.album_drag["indicator"] = indicator

    def compute_album_drop_index(self, x_root: int):
        cards = [self.album_card_map.get(name) for name in self.albums if self.album_card_map.get(name)]
        if not cards:
            return 0
        for idx, card in enumerate(cards):
            center = card.winfo_rootx() + card.winfo_width() / 2
            if x_root < center:
                return idx
        return len(cards)

    def on_album_drag_motion(self, event):
        album_name = self.album_drag.get("album")
        if not album_name or album_name not in self.albums:
            return
        dx = event.x_root - self.album_drag.get("start_x", 0)
        dy = event.y_root - self.album_drag.get("start_y", 0)
        if not self.album_drag.get("dragging"):
            if abs(dx) < 8 and abs(dy) < 8:
                return
            ghost = self.create_album_drag_ghost(album_name)
            ghost.geometry(f"+{event.x_root + 14}+{event.y_root + 10}")
            self.album_drag["ghost"] = ghost
            self.album_drag["dragging"] = True
            self.album_drag["click_block"] = True
        ghost = self.album_drag.get("ghost")
        if ghost is not None:
            ghost.geometry(f"+{event.x_root + 14}+{event.y_root + 10}")
        target_index = self.compute_album_drop_index(event.x_root)
        self.album_drag["target_index"] = target_index
        self.show_album_insert_indicator(target_index)

    def end_album_drag(self, event=None):
        album_name = self.album_drag.get("album")
        if not album_name:
            return
        dragging = self.album_drag.get("dragging")
        start_index = self.album_drag.get("start_index", -1)
        target_index = self.album_drag.get("target_index", start_index)
        click_block = self.album_drag.get("click_block", False)
        self.clear_album_drag_visuals()

        if dragging and album_name in self.albums:
            old_index = self.albums.index(album_name)
            self.albums.pop(old_index)
            if target_index > old_index:
                target_index -= 1
            target_index = max(0, min(target_index, len(self.albums)))
            self.albums.insert(target_index, album_name)
            self.save_config()
            self.refresh_album_bar()
            self.refresh_tree()
            self.status("已更新相册顺序与快捷键")
        elif not dragging and not click_block:
            self.on_album_pressed(album_name)

        self.album_drag = {
            "album": None,
            "widget": None,
            "start_x": 0,
            "start_y": 0,
            "start_index": -1,
            "dragging": False,
            "target_index": -1,
            "ghost": None,
            "indicator": None,
            "click_block": False,
        }

    def on_album_right_click(self, event, album_name):
        menu = tk.Menu(self.root, tearoff=0, bg=self.theme["card_bg"], fg=self.theme["text"], activebackground=self.theme["hover_bg"])
        menu.add_command(label="打开相册", command=lambda a=album_name: self.select_album_node(a))
        menu.add_command(label="打开文件夹", command=lambda a=album_name: self.open_folder_path(os.path.join(self.root_dir, a)))
        menu.add_command(label="删除相册项", command=lambda a=album_name: self.delete_album_entry(a))
        menu.post(event.x_root, event.y_root)

    def create_album_dialog(self):
        t = self.theme
        dialog = Toplevel(self.root)
        dialog.title("新建相册")
        dialog.geometry(f"{ui(380)}x{ui(210)}")
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.configure(bg=t["panel_bg"])
        self.apply_window_icon(dialog)

        tk.Label(dialog, text="新建相册", bg=t["panel_bg"], fg=t["text"], font=("微软雅黑", 13, "bold")).pack(pady=(ui(18), ui(4)))
        tk.Label(dialog, text="请输入相册名称", bg=t["panel_bg"], fg=t["subtext"], font=("微软雅黑", 9)).pack(pady=(0, ui(10)))
        entry = ttk.Entry(dialog, width=30, font=("微软雅黑", 11))
        entry.pack(pady=ui(4), ipady=ui(4))
        entry.focus_set()

        btn_bar = tk.Frame(dialog, bg=t["panel_bg"])
        btn_bar.pack(pady=ui(14))

        def confirm():
            name = entry.get().strip()
            if not name:
                messagebox.showwarning("提示", "相册名称不能为空", parent=dialog)
                return
            if name in self.albums:
                messagebox.showwarning("提示", "相册已存在", parent=dialog)
                return
            self.albums.append(name)
            self.save_config()
            self.refresh_album_bar()
            self.refresh_tree()
            dialog.destroy()
            self.status(f"已创建相册：{name}")

        def cancel():
            dialog.destroy()

        ttk.Button(btn_bar, text="取消", command=cancel, width=6).pack(side=tk.LEFT, padx=ui(8))
        ttk.Button(btn_bar, text="确认", command=confirm, style="Accent.TButton", width=6).pack(side=tk.LEFT, padx=ui(8))
        dialog.bind("<Return>", lambda e: confirm())
        dialog.bind("<Escape>", lambda e: cancel())
        self.center_window(dialog, ui(380), ui(210), self.root)

    def delete_album_entry(self, album_name: str):
        if album_name not in self.albums:
            return
        if not messagebox.askyesno("确认", f"删除相册项「{album_name}」？\n仅删除软件中的分类项，不删除实际文件夹。"):
            return
        self.albums.remove(album_name)
        self.save_config()
        self.refresh_album_bar()
        self.refresh_tree()
        self.status(f"已删除相册项：{album_name}")

    def handle_album_shortcut(self, album_idx: int):
        if self.is_preview_mode and self.is_animating:
            return
        if album_idx >= len(self.albums):
            return
        self.on_album_pressed(self.albums[album_idx])

    def on_album_pressed(self, album_name: str):
        if self.is_preview_mode:
            if self.selected_files:
                self.move_selected_to_album(album_name)
            elif self.current_files:
                self.move_current_to_album(album_name)
            else:
                self.status("当前没有可整理的项目")
            return
        self.move_current_to_album(album_name)


    def flash_album_button(self, album_name: str):
        btn = self.album_btn_map.get(album_name)
        if not btn:
            return
        normal_bg = self.theme["card_bg"]
        flash_bg = self.theme["accent"]
        normal_fg = self.theme["text"]

        def set_state(bg, fg):
            try:
                btn.configure(bg=bg, fg=fg)
            except Exception:
                pass

        set_state(flash_bg, "white")
        self.root.after(80, lambda: set_state(normal_bg, normal_fg))
        self.root.after(160, lambda: set_state(flash_bg, "white"))
        self.root.after(240, lambda: set_state(normal_bg, normal_fg))

    # -------------------------- 移动/撤销 --------------------------
    def load_media_preview_sync(self, path: str, max_size):
        try:
            if path.lower().endswith(self.get_video_ext()):
                return self.get_video_preview_pil(path, max_size)
            img = Image.open(path)
            img = ImageOps.exif_transpose(img)
            img.thumbnail(max_size, Image.Resampling.LANCZOS)
            return img
        except Exception:
            fallback = self.video_placeholder_pil.copy()
            fallback.thumbnail(max_size, Image.Resampling.LANCZOS)
            return fallback

    def get_single_cache_key(self, path: str):
        return (path, os.path.getmtime(path) if os.path.exists(path) else 0)

    def prefetch_single_neighbors(self, center_idx=None, ahead=4):
        if not self.current_files:
            return
        if center_idx is None:
            center_idx = self.current_idx
        start = max(0, center_idx)
        end = min(len(self.current_files), center_idx + ahead + 1)
        for idx in range(start, end):
            try:
                path = os.path.join(self.current_dir, self.current_files[idx])
            except Exception:
                continue
            key = self.get_single_cache_key(path)
            if key in self.single_preview_cache or key in self.single_loading_keys:
                continue
            self.single_loading_keys.add(key)
            def job(p=path):
                return self.load_media_preview_sync(p, (1280, 900))
            def done(img, k=key):
                self.single_loading_keys.discard(k)
                try:
                    self.single_preview_cache[k] = img.copy()
                except Exception:
                    pass
            def err(exc, k=key):
                self.single_loading_keys.discard(k)
            self.run_async(job, done, err)

    def render_single_media(self, pil_img, filename: str, is_video: bool, token: int):
        if token != self.current_single_token:
            return
        self.temp_single_image = pil_img.copy()
        img = pil_img.copy()
        width = max(600, self.single_canvas.winfo_width() - 60)
        height = max(400, self.single_canvas.winfo_height() - 80)
        img.thumbnail((width, height), Image.Resampling.LANCZOS)
        self.single_photo = ImageTk.PhotoImage(img)
        self.single_canvas.delete("all")
        self.single_canvas.create_image(
            self.single_canvas.winfo_width() // 2,
            self.single_canvas.winfo_height() // 2,
            image=self.single_photo,
            anchor=tk.CENTER,
        )
        extra = ""
        if is_video:
            dur = self.get_video_info(os.path.join(self.current_dir, filename)).get("duration", "")
            extra = f" | 时长 {dur}" if dur else " | 视频文件"
        title = f"第 {self.current_idx + 1}/{len(self.current_files)} 个 | {filename}{extra}"
        self.single_canvas.create_text(
            self.single_canvas.winfo_width() // 2,
            ui(32),
            text=title,
            fill=self.theme["text"],
            font=("微软雅黑", 11, "bold"),
        )
        self.save_progress()
        self.prefetch_single_neighbors(self.current_idx, int(self.config.get("preload_count", 6)))

    def resolve_conflict_destination(self, dst_dir: str, filename: str):
        strategy = self.config.get("conflict_strategy", "rename")
        base_dst = os.path.join(dst_dir, filename)
        if not os.path.exists(base_dst):
            return {"status": "moved", "dst_path": base_dst, "strategy": strategy, "renamed": False}
        if strategy == "skip":
            return {"status": "skipped", "dst_path": base_dst, "strategy": strategy, "renamed": False}
        if strategy == "replace":
            return {"status": "replace", "dst_path": base_dst, "strategy": strategy, "renamed": False}
        stem, ext = os.path.splitext(filename)
        i = 1
        while True:
            candidate_name = f"{stem} ({i}){ext}"
            candidate = os.path.join(dst_dir, candidate_name)
            if not os.path.exists(candidate):
                return {"status": "moved", "dst_path": candidate, "strategy": strategy, "renamed": True}
            i += 1

    def execute_move_strategy(self, src: str, dst_dir: str, filename: str):
        decision = self.resolve_conflict_destination(dst_dir, filename)
        status = decision["status"]
        if status == "skipped":
            return decision
        dst_path = decision["dst_path"]
        if status == "replace" and os.path.exists(dst_path):
            try:
                os.remove(dst_path)
            except Exception:
                os.replace(src, dst_path)
                decision["status"] = "moved"
                return decision
        shutil.move(src, dst_path)
        decision["status"] = "moved"
        return decision

    def start_single_fly_animation(self, album_name: str, current_preview):
        btn = self.album_btn_map.get(album_name)
        if not btn or current_preview is None:
            return
        try:
            self.root.update_idletasks()
            canvas_w = max(400, self.single_canvas.winfo_width())
            canvas_h = max(300, self.single_canvas.winfo_height())
            start_x = self.single_canvas.winfo_rootx() + canvas_w / 2
            start_y = self.single_canvas.winfo_rooty() + canvas_h / 2
            target_x = btn.winfo_rootx() + btn.winfo_width() / 2
            target_y = btn.winfo_rooty() + btn.winfo_height() / 2
            fly_img = current_preview.copy()
            fly_img.thumbnail((300, 210), Image.Resampling.LANCZOS)
            photo = ImageTk.PhotoImage(fly_img)
        except Exception:
            return
        ghost = tk.Toplevel(self.root)
        ghost.overrideredirect(True)
        ghost.attributes("-topmost", True)
        try:
            ghost.attributes("-alpha", 0.96)
        except Exception:
            pass
        label = tk.Label(ghost, image=photo, bd=0, highlightthickness=0, bg=self.theme["root_bg"])
        label.image = photo
        label.pack()
        ghost.geometry(f"+{int(start_x - photo.width() / 2)}+{int(start_y - photo.height() / 2)}")
        frames = 10
        delay = 30
        def step(i=0):
            if self._closed:
                try:
                    ghost.destroy()
                except Exception:
                    pass
                return
            if i > frames:
                try:
                    ghost.destroy()
                except Exception:
                    pass
                return
            p = i / frames
            cur_x = start_x + (target_x - start_x) * p
            cur_y = start_y + (target_y - start_y) * p
            ghost.geometry(f"+{int(cur_x - photo.width() / 2)}+{int(cur_y - photo.height() / 2)}")
            self.root.after(delay, lambda: step(i + 1))
        step()

    def animate_preview_selection_into_album(self, album_name: str, targets, on_finish):
        if not targets:
            on_finish()
            return
        btn = self.album_btn_map.get(album_name)
        if not btn:
            on_finish()
            return
        first_name = targets[0]
        try:
            idx = self.current_files.index(first_name)
        except ValueError:
            on_finish()
            return
        pos = self.preview_index_map.get(idx)
        if not pos:
            on_finish()
            return
        try:
            self.root.update_idletasks()
            x, y = pos
            start_x = x + THUMB_SIZE[0] / 2
            start_y = y + THUMB_SIZE[1] / 2 - int(self.preview_canvas.canvasy(0))
            target_x = btn.winfo_rootx() + btn.winfo_width() / 2 - self.preview_canvas.winfo_rootx()
            target_y = btn.winfo_rooty() + btn.winfo_height() / 2 - self.preview_canvas.winfo_rooty()
            path = os.path.join(self.current_dir, first_name)
            pil = self.load_media_preview_sync(path, (200, 160))
            self.anim_photo = ImageTk.PhotoImage(pil)
        except Exception:
            on_finish()
            return

        frames = 10
        self.is_animating = True
        anim_id = self.preview_canvas.create_image(start_x, start_y, image=self.anim_photo, anchor=tk.CENTER, tags="preview_anim")
        badge_id = None
        if len(targets) > 1:
            badge_id = self.preview_canvas.create_oval(start_x + 44, start_y - 54, start_x + 76, start_y - 22, fill=self.theme["yellow"], outline="")
            text_id = self.preview_canvas.create_text(start_x + 60, start_y - 38, text=str(len(targets)), fill="black", font=("微软雅黑", 10, "bold"))
        else:
            text_id = None

        def step(i=0):
            if i > frames:
                self.preview_canvas.delete(anim_id)
                if badge_id is not None:
                    self.preview_canvas.delete(badge_id)
                if text_id is not None:
                    self.preview_canvas.delete(text_id)
                self.is_animating = False
                on_finish()
                return
            p = i / frames
            cur_x = start_x + (target_x - start_x) * p
            cur_y = start_y + (target_y - start_y) * p
            self.preview_canvas.coords(anim_id, cur_x, cur_y)
            if badge_id is not None:
                self.preview_canvas.coords(badge_id, cur_x + 44, cur_y - 54, cur_x + 76, cur_y - 22)
            if text_id is not None:
                self.preview_canvas.coords(text_id, cur_x + 60, cur_y - 38)
            self.root.after(30, lambda: step(i + 1))

        step()

    def animate_file_into_album(self, album_name: str, current_preview, next_preview, on_finish):
        btn = self.album_btn_map.get(album_name)
        if not btn or current_preview is None:
            on_finish()
            return
        try:
            self.root.update_idletasks()
            canvas_w = max(400, self.single_canvas.winfo_width())
            canvas_h = max(300, self.single_canvas.winfo_height())
            target_x = btn.winfo_rootx() + btn.winfo_width() / 2 - self.single_canvas.winfo_rootx()
            target_y = btn.winfo_rooty() + btn.winfo_height() / 2 - self.single_canvas.winfo_rooty()

            bg_img = next_preview.copy() if next_preview is not None else current_preview.copy()
            bg_img.thumbnail((max(600, canvas_w - 60), max(400, canvas_h - 80)), Image.Resampling.LANCZOS)
            self.single_photo = ImageTk.PhotoImage(bg_img)

            fly_img = current_preview.copy()
            fly_img.thumbnail((300, 210), Image.Resampling.LANCZOS)
            self.anim_photo = ImageTk.PhotoImage(fly_img)
        except Exception:
            on_finish()
            return

        self.is_animating = True
        self.single_canvas.delete("all")
        self.single_canvas.create_image(canvas_w / 2, canvas_h / 2, image=self.single_photo, anchor=tk.CENTER)
        cur_id = self.single_canvas.create_image(canvas_w / 2, canvas_h / 2, image=self.anim_photo, anchor=tk.CENTER, tags="album_move_anim")

        frames = 10
        start_x = canvas_w / 2
        start_y = canvas_h / 2

        def step(i=0):
            if i > frames:
                self.single_canvas.delete(cur_id)
                self.is_animating = False
                on_finish()
                return
            p = i / frames
            cur_x = start_x + (target_x - start_x) * p
            cur_y = start_y + (target_y - start_y) * p
            self.single_canvas.coords(cur_id, cur_x, cur_y)
            scale = 1.0 - 0.55 * p
            try:
                temp = current_preview.copy()
                base_w = min(300, temp.width)
                base_h = min(210, temp.height)
                tw = max(40, int(base_w * scale))
                th = max(30, int(base_h * scale))
                temp.thumbnail((tw, th), Image.Resampling.LANCZOS)
                self.anim_photo = ImageTk.PhotoImage(temp)
                self.single_canvas.itemconfigure(cur_id, image=self.anim_photo)
            except Exception:
                pass
            self.root.after(30, lambda: step(i + 1))

        step()

    def move_current_to_album(self, album_name: str):
        if not self.current_files:
            return
        if self.current_idx >= len(self.current_files):
            self.current_idx = max(0, len(self.current_files) - 1)
        if self.current_idx < 0 or self.current_idx >= len(self.current_files):
            return
        filename = self.current_files[self.current_idx]
        src_dir = self.current_dir
        src = os.path.join(src_dir, filename)
        dst_dir = os.path.join(self.root_dir, album_name)
        os.makedirs(dst_dir, exist_ok=True)

        path = os.path.join(src_dir, filename)
        cache_key = self.get_single_cache_key(path)
        if cache_key in self.single_preview_cache:
            current_preview = self.single_preview_cache[cache_key].copy()
        else:
            current_preview = self.load_media_preview_sync(path, (1280, 900))

        # 逻辑先推进，立即让界面里的后续项目补位
        removed_index = self.current_idx
        try:
            self.current_files.pop(removed_index)
        except Exception:
            pass
        if self.current_idx >= len(self.current_files):
            self.current_idx = max(0, len(self.current_files) - 1)

        if self.is_preview_mode:
            self.refresh_preview_grid()
        else:
            self.prefetch_single_neighbors(self.current_idx, int(self.config.get("preload_count", 6)))
            if self.current_files:
                self.refresh_single_view()
            else:
                self.single_canvas.delete("all")
                self.single_canvas.create_text(
                    max(200, self.single_canvas.winfo_width() // 2),
                    max(120, self.single_canvas.winfo_height() // 2),
                    text="当前目录没有可整理的媒体文件",
                    fill=self.theme["text"],
                    font=("微软雅黑", 16, "bold"),
                )
        self.flash_album_button(album_name)
        if not self.is_preview_mode:
            self.start_single_fly_animation(album_name, current_preview)

        def job():
            return self.execute_move_strategy(src, dst_dir, filename)

        def done(result):
            status = result.get("status")
            final_dst = result.get("dst_path", "")
            moved_name = os.path.basename(final_dst) if final_dst else filename
            if status == "moved":
                self.move_history.append({
                    "filename": moved_name,
                    "src_dir": src_dir,
                    "dst_dir": dst_dir,
                })
                self.add_recent_op("移动", moved_name, album_name)
                if result.get("renamed"):
                    self.status(f"已移动到相册：{album_name} / {filename} → {moved_name}")
                else:
                    self.status(f"已移动到相册：{album_name} / {moved_name}")
                self.refresh_album_bar()
                self.refresh_tree()
            elif status == "skipped":
                self.status(f"同名已存在，按策略跳过：{filename}")
                self.scan_and_show(ask_restore=False)
                return
            else:
                self.status(f"移动结果未知：{filename}")
                self.scan_and_show(ask_restore=False)
                return
            self.save_config()

        def err(exc):
            self.status(f"移动失败：{exc}")
            self.scan_and_show(ask_restore=False)

        self.run_async(job, done, err)

    def move_selected_to_album_dialog(self):
        if not self.selected_files:
            messagebox.showwarning("提示", "请先在预览模式里选中文件", parent=self.root)
            return
        if not self.albums:
            messagebox.showwarning("提示", "请先创建相册", parent=self.root)
            return
        dialog = Toplevel(self.root)
        dialog.title("选择目标相册")
        dialog.geometry("360x360")
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.configure(bg=self.theme["panel_bg"])
        self.apply_window_icon(dialog)

        tk.Label(dialog, text="请选择目标相册", bg=self.theme["panel_bg"], fg=self.theme["text"], font=("微软雅黑", 13, "bold")).pack(pady=(16, 10))
        tk.Label(dialog, text=f"已选中 {len(self.selected_files)} 个项目", bg=self.theme["panel_bg"], fg=self.theme["subtext"], font=("微软雅黑", 9)).pack(pady=(0, 8))

        listbox = tk.Listbox(
            dialog,
            font=("微软雅黑", 10),
            selectmode=tk.SINGLE,
            bg=self.theme["main_bg"],
            fg=self.theme["text"],
            selectbackground=self.theme["accent"],
            selectforeground="white",
            highlightthickness=1,
            highlightbackground=self.theme["border"],
            relief=tk.FLAT,
            activestyle="none",
        )
        listbox.pack(fill=tk.BOTH, expand=True, padx=14, pady=8)
        for idx, album in enumerate(self.albums):
            count = self.get_file_count(os.path.join(self.root_dir, album))
            hotkey = f"  ·  快捷键 {idx + 1}" if idx < 9 else ""
            listbox.insert(tk.END, f"{album}    ({count} 项){hotkey}")
        if self.albums:
            listbox.selection_set(0)

        btn_bar = tk.Frame(dialog, bg=self.theme["panel_bg"])
        btn_bar.pack(fill=tk.X, padx=14, pady=(4, 14))

        def confirm():
            sel = listbox.curselection()
            if not sel:
                messagebox.showwarning("提示", "请选择一个相册", parent=dialog)
                return
            album = self.albums[sel[0]]
            dialog.destroy()
            self.move_selected_to_album(album)

        tk.Button(btn_bar, text="确定", command=confirm, bg=self.theme["accent"], fg="white", relief=tk.FLAT, font=("微软雅黑", 10, "bold"), activebackground=self.theme["accent"]).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(0, 6))
        tk.Button(btn_bar, text="取消", command=dialog.destroy, bg=self.theme["card_bg"], fg=self.theme["text"], relief=tk.FLAT, font=("微软雅黑", 10), activebackground=self.theme["hover_bg"]).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(6, 0))
        dialog.bind("<Return>", lambda e: confirm())
        dialog.bind("<Escape>", lambda e: dialog.destroy())
        self.center_window(dialog, 360, 360, self.root)

    def move_selected_to_album(self, album_name: str):
        if not self.selected_files:
            return
        dst_dir = os.path.join(self.root_dir, album_name)
        os.makedirs(dst_dir, exist_ok=True)
        targets = [f for f in self.current_files if f in self.selected_files]

        def do_move():
            def job():
                moved = []
                skipped = []
                for filename in targets:
                    src = os.path.join(self.current_dir, filename)
                    if not os.path.exists(src):
                        continue
                    result = self.execute_move_strategy(src, dst_dir, filename)
                    if result.get("status") == "moved":
                        moved.append({"src_name": filename, "dst_name": os.path.basename(result.get("dst_path", filename))})
                    else:
                        skipped.append(filename)
                return moved, skipped

            def done(payload):
                moved, skipped = payload
                for item in moved:
                    self.move_history.append({
                        "filename": item["dst_name"],
                        "src_dir": self.current_dir,
                        "dst_dir": dst_dir,
                    })
                self.add_recent_op("批量移动", [x["dst_name"] for x in moved], album_name)
                self.selected_files.clear()
                self.last_selected_idx = -1
                self.update_selection_label()
                self.refresh_album_bar()
                self.refresh_tree()
                self.scan_and_show(ask_restore=False)
                msg = f"已批量移动 {len(moved)} 个文件到相册：{album_name}"
                if skipped:
                    msg += f"，跳过 {len(skipped)} 个同名文件"
                self.status(msg)
                self.save_config()

            self.run_async(job, done, lambda e: self.status(f"批量移动失败：{e}"))

        if self.is_preview_mode:
            self.flash_album_button(album_name)
            self.animate_preview_selection_into_album(album_name, targets, do_move)
        else:
            do_move()

    def move_selected_back_to_unsorted(self):
        if not self.selected_files or self.current_dir == self.root_dir:
            return
        targets = [f for f in self.current_files if f in self.selected_files]
        dst_dir = self.root_dir

        def job():
            moved = []
            skipped = []
            for filename in targets:
                src = os.path.join(self.current_dir, filename)
                if not os.path.exists(src):
                    continue
                result = self.execute_move_strategy(src, dst_dir, filename)
                if result.get("status") == "moved":
                    moved.append(os.path.basename(result.get("dst_path", filename)))
                else:
                    skipped.append(filename)
            return moved, skipped

        def done(payload):
            moved, skipped = payload
            self.add_recent_op("移回未整理", moved)
            self.selected_files.clear()
            self.last_selected_idx = -1
            self.update_selection_label()
            self.refresh_tree()
            self.refresh_album_bar()
            self.scan_and_show(ask_restore=False)
            msg = f"已移回未整理：{len(moved)} 个文件"
            if skipped:
                msg += f"，跳过 {len(skipped)} 个同名文件"
            self.status(msg)
            self.save_config()

        self.run_async(job, done, lambda e: self.status(f"移回失败：{e}"))

    def undo_last_move(self, event=None):
        if not self.move_history:
            self.status("没有可撤销的操作")
            return "break"
        item = self.move_history.pop()
        filename = item["filename"]
        src_dir = item["dst_dir"]
        dst_dir = item["src_dir"]

        def job():
            src = os.path.join(src_dir, filename)
            if not os.path.exists(src):
                raise FileNotFoundError(src)
            result = self.execute_move_strategy(src, dst_dir, filename)
            if result.get("status") != "moved":
                raise FileExistsError(filename)
            return os.path.basename(result.get("dst_path", filename))

        def done(restored_name):
            self.refresh_tree()
            self.refresh_album_bar()
            if self.current_dir == dst_dir:
                self.scan_and_show(ask_restore=False)
            elif self.is_preview_mode:
                self.scan_and_show(ask_restore=False)
            else:
                self.refresh_single_view()
            self.add_recent_op("撤销", restored_name)
            self.status(f"已撤销：{restored_name}")
            self.save_config()

        self.run_async(job, done, lambda e: self.status(f"撤销失败：{e}"))
        return "break"

    # -------------------------- 设置 --------------------------
    def open_settings_dialog(self):
        t = self.theme
        dialog = Toplevel(self.root)
        dialog.title("PicaPhoto 设置")
        dialog.geometry(f"{ui(780)}x{ui(700)}")
        dialog.minsize(ui(780), ui(700))
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.configure(bg=t["root_bg"])
        self.apply_window_icon(dialog)

        auto_var = tk.BooleanVar(value=self.auto_refresh_enabled)
        dark_var = tk.BooleanVar(value=(self.theme_name == "dark"))
        img_var = tk.StringVar(value=", ".join(self.get_image_ext()))
        vid_var = tk.StringVar(value=", ".join(self.get_video_ext()))
        conflict_var = tk.StringVar(value=self.config.get("conflict_strategy", "rename"))
        preload_var = tk.IntVar(value=int(self.config.get("preload_count", 6)))
        saved = {"done": False}
        CONFLICT_ITEMS = [("自动重命名", "rename"), ("跳过同名", "skip"), ("覆盖已有文件", "replace")]

        # ── 顶部标题栏 ──
        top = tk.Frame(dialog, bg=t["root_bg"], padx=ui(20), pady=ui(12))
        top.pack(fill=tk.X)
        tk.Label(top, image=getattr(self, "brand_logo_image", None), bg=t["root_bg"]).pack(side=tk.LEFT, padx=(0, ui(10)))
        tk.Label(top, text="PicaPhoto 设置", bg=t["root_bg"], fg=t["text"], font=("微软雅黑", 14, "bold")).pack(side=tk.LEFT)
        tk.Label(top, text="关闭窗口自动保存", bg=t["root_bg"], fg=t["subtext"], font=("微软雅黑", 9)).pack(side=tk.RIGHT)

        # ── 可滚动内容区（微信设置式：整页分组、无侧栏） ──
        body = tk.Frame(dialog, bg=t["root_bg"])
        body.pack(fill=tk.BOTH, expand=True, padx=ui(16), pady=(0, ui(14)))

        canvas = tk.Canvas(body, bg=t["main_bg"], highlightthickness=0, bd=0)
        vbar = ttk.Scrollbar(body, orient=tk.VERTICAL, command=canvas.yview)
        canvas.configure(yscrollcommand=vbar.set)
        vbar.pack(side=tk.RIGHT, fill=tk.Y)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        inner = tk.Frame(canvas, bg=t["main_bg"])
        win = canvas.create_window((0, 0), window=inner, anchor="nw")

        def _update_scrollbar():
            try:
                bb = canvas.bbox("all")
                if bb and (bb[3] - bb[1]) > canvas.winfo_height() + 2:
                    vbar.pack(side=tk.RIGHT, fill=tk.Y)
                else:
                    vbar.pack_forget()
            except Exception:
                pass

        def _on_inner_configure(_e):
            canvas.configure(scrollregion=canvas.bbox("all"))
            _update_scrollbar()

        inner.bind("<Configure>", _on_inner_configure)
        canvas.bind("<Configure>", lambda e: canvas.itemconfigure(win, width=e.width))
        canvas.bind("<MouseWheel>", lambda e: canvas.yview_scroll(-1 * int(e.delta / 120), "units"))
        dialog.bind("<MouseWheel>", lambda e: canvas.yview_scroll(-1 * int(e.delta / 120), "units"), add="+")

        def group_title(text):
            tk.Label(inner, text=text, bg=t["main_bg"], fg=t["subtext"], font=("微软雅黑", 9, "bold")).pack(anchor="w", padx=ui(24), pady=(ui(18), ui(4)))

        def add_row(title, desc="", control_factory=None, divider=True):
            """一行设置：左标题+说明，右控件（右对齐、垂直居中）。"""
            row = tk.Frame(inner, bg=t["main_bg"])
            row.pack(fill=tk.X, padx=ui(24), pady=(ui(10), ui(8)))
            row.columnconfigure(0, weight=1)
            left = tk.Frame(row, bg=t["main_bg"])
            left.grid(row=0, column=0, sticky="w")
            tk.Label(left, text=title, bg=t["main_bg"], fg=t["text"], font=("微软雅黑", 10)).pack(anchor="w")
            if desc:
                tk.Label(left, text=desc, bg=t["main_bg"], fg=t["subtext"], font=("微软雅黑", 9)).pack(anchor="w", pady=(ui(2), 0))
            if control_factory is not None:
                cw = tk.Frame(row, bg=t["main_bg"])
                cw.grid(row=0, column=1, sticky="e", padx=(ui(16), 0))
                ctrl = control_factory(cw)
                ctrl.pack(side=tk.RIGHT)
            if divider:
                tk.Frame(inner, bg=t["divider"], height=1).pack(fill=tk.X, padx=ui(24), pady=(ui(8), 0))

        # ── 基础 ──
        group_title("基础")
        add_row("自动刷新当前目录", "目录内容变化时自动重新扫描",
                lambda p: _Switch(p, auto_var, off_color=t["hover_bg"]))
        add_row("深色模式", "界面使用深色配色",
                lambda p: _Switch(p, dark_var, off_color=t["hover_bg"]))

        # ── 文件类型 ──
        group_title("文件类型")
        add_row("图片后缀", "支持的图片格式，逗号分隔",
                lambda p: ttk.Entry(p, textvariable=img_var, width=30, justify="left"))
        add_row("视频后缀", "支持的视频格式，逗号分隔",
                lambda p: ttk.Entry(p, textvariable=vid_var, width=30, justify="left"))

        # ── 移动策略 ──
        group_title("移动策略")
        combo_holder = {}
        add_row("重名文件处理策略", "移动到相册时遇到同名文件的处理方式",
                lambda p: _conflict_combo(p, t, CONFLICT_ITEMS, conflict_var, combo_holder))

        # ── 性能与缓存 ──
        group_title("性能与缓存")
        add_row("向后预读数量", "单图模式下提前加载的相邻文件数",
                lambda p: ttk.Spinbox(p, from_=1, to=20, textvariable=preload_var, width=6, style="TSpinbox", justify="center"))
        add_row("缓存", "缩略图与视频帧缓存",
                lambda p: tk.Button(p, text="清理并重建", command=lambda: (self.clear_runtime_caches(refresh_view=True), self.status("缓存已清理并重建")), bg=t["card_bg"], fg=t["text"], relief=tk.FLAT, font=("微软雅黑", 9), padx=ui(12), pady=ui(5), activebackground=t["hover_bg"], cursor="hand2", highlightthickness=0))

        # ── 关于 ──
        group_title("关于")
        add_row("版本", "PicaPhoto v1.0 · 图片整理工具")
        add_row("快捷键", "Tab 预览 ｜ ← → 切换 ｜ Ctrl+Z 撤销 ｜ R 旋转 ｜ F 翻转", divider=False)
        tk.Frame(inner, bg=t["main_bg"], height=ui(16)).pack()

        def save_and_close(close_only=False):
            if saved["done"]:
                try:
                    dialog.destroy()
                except Exception:
                    pass
                return
            image_ext = self.normalize_ext_text(img_var.get())
            video_ext = self.normalize_ext_text(vid_var.get())
            if not image_ext:
                messagebox.showwarning("提示", "图片后缀不能为空", parent=dialog)
                return
            if not video_ext:
                messagebox.showwarning("提示", "视频后缀不能为空", parent=dialog)
                return
            self.config["image_ext"] = image_ext
            self.config["video_ext"] = video_ext
            combo = combo_holder.get("combo")
            if combo is not None:
                for label, v in CONFLICT_ITEMS:
                    if combo.get() == label:
                        conflict_var.set(v)
                        break
            self.config["conflict_strategy"] = conflict_var.get()
            self.config["preload_count"] = max(1, min(20, int(preload_var.get() or 6)))
            self.auto_refresh_enabled = auto_var.get()
            if self.auto_refresh_enabled:
                self.start_auto_refresh()
            else:
                self.stop_auto_refresh()
            target_theme = "dark" if dark_var.get() else "light"
            self.save_config()
            saved["done"] = True
            try:
                dialog.destroy()
            except Exception:
                pass
            if target_theme != self.theme_name:
                self.switch_theme(target_theme)
            self.scan_and_show(ask_restore=False)
            self.status("设置已自动保存")

        dialog.protocol("WM_DELETE_WINDOW", save_and_close)
        dialog.bind("<Escape>", lambda e: save_and_close())
        self.center_window(dialog, ui(780), ui(700), self.root)

    def start_auto_refresh(self):
        self.stop_auto_refresh()
        self.stop_hover_video_preview(restore=False)
        if not self.auto_refresh_enabled:
            return

        def _refresh():
            if self._closed or not self.auto_refresh_enabled:
                return
            if self.current_dir:
                self.scan_and_show(ask_restore=False)
            self.auto_refresh_job = self.root.after(AUTO_REFRESH_MS, _refresh)

        self.auto_refresh_job = self.root.after(AUTO_REFRESH_MS, _refresh)

    def stop_auto_refresh(self):
        if self.auto_refresh_job:
            try:
                self.root.after_cancel(self.auto_refresh_job)
            except Exception:
                pass
            self.auto_refresh_job = None

    # -------------------------- 事件 --------------------------
    def handle_escape(self, event=None):
        if self.is_preview_mode:
            self.exit_preview_mode()
            return "break"
        return None

    def on_root_configure(self, event):
        if event.widget is not self.root:
            return
        if self._resize_job:
            try:
                self.root.after_cancel(self._resize_job)
            except Exception:
                pass
        if self.is_preview_mode:
            self._resize_job = self.root.after(120, self.refresh_preview_grid)
        else:
            self._resize_job = self.root.after(120, self.refresh_single_view)

    def status(self, text: str):
        self.status_bar.configure(text=text)

    def add_recent_op(self, action: str, filenames=None, album_name: str = ""):
        if filenames is None:
            filenames = []
        if isinstance(filenames, str):
            filenames = [filenames]
        if filenames:
            if len(filenames) == 1:
                detail = filenames[0]
            else:
                detail = f"{filenames[0]} 等 {len(filenames)} 项"
        else:
            detail = ""
        ts = datetime.now().strftime("%H:%M:%S")
        parts = [f"[{ts}]", action]
        if album_name:
            parts.append(f"→ {album_name}")
        if detail:
            parts.append(detail)
        entry = " | ".join(parts)
        self.recent_ops.append(entry)
        self.recent_ops = self.recent_ops[-30:]
        self.refresh_recent_ops_panel()

    def refresh_recent_ops_panel(self):
        if not hasattr(self, "recent_ops_list"):
            return
        self.recent_ops_list.delete(0, tk.END)
        if not self.recent_ops:
            self.recent_ops_list.insert(tk.END, "暂无操作记录")
            try:
                self.recent_ops_list.itemconfig(0, fg=self.theme["subtext"])
            except Exception:
                pass
        else:
            for item in reversed(self.recent_ops[-30:]):
                self.recent_ops_list.insert(tk.END, item)
        sb = getattr(self, "recent_scroll", None)
        if sb is not None:
            try:
                if self.recent_ops:
                    sb.pack(side=tk.RIGHT, fill=tk.Y)
                else:
                    sb.pack_forget()
            except Exception:
                pass

    def format_duration(self, seconds):
        try:
            total = max(0, int(round(float(seconds))))
        except Exception:
            return ""
        h, rem = divmod(total, 3600)
        m, s = divmod(rem, 60)
        if h > 0:
            return f"{h}:{m:02d}:{s:02d}"
        return f"{m:02d}:{s:02d}"

    def get_video_info(self, path: str):
        key = (path, os.path.getmtime(path) if os.path.exists(path) else 0)
        if key in self.video_info_cache:
            return self.video_info_cache[key]
        info = {"duration": "", "seconds": 0.0}
        if cv2 is not None and os.path.exists(path):
            cap = None
            try:
                cap = cv2.VideoCapture(path)
                if cap is not None and cap.isOpened():
                    fps = float(cap.get(cv2.CAP_PROP_FPS) or 0.0)
                    frames = float(cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0.0)
                    if fps > 0 and frames > 0:
                        secs = frames / fps
                        info["seconds"] = secs
                        info["duration"] = self.format_duration(secs)
            except Exception:
                pass
            finally:
                if cap is not None:
                    try:
                        cap.release()
                    except Exception:
                        pass
        self.video_info_cache[key] = info
        return info

    def on_single_mousewheel(self, event):
        if self.is_preview_mode or self.is_animating:
            return
        if getattr(event, "num", None) == 4:
            self.prev_current()
        elif getattr(event, "num", None) == 5:
            self.skip_current()
        else:
            if event.delta > 0:
                self.prev_current()
            elif event.delta < 0:
                self.skip_current()

    def on_close(self):
        self._closed = True
        self.save_progress()
        self.save_config()
        self.stop_auto_refresh()
        self.stop_hover_video_preview(restore=False)
        self.stop_hover_video_preview(restore=False)
        try:
            self.executor.shutdown(wait=False, cancel_futures=True)
        except TypeError:
            self.executor.shutdown(wait=False)
        self.root.destroy()


if __name__ == "__main__":
    app_root = tk.Tk()
    app = MediaSorterApp(app_root)
    app_root.mainloop()
