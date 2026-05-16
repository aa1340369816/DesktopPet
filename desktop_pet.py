import tkinter as tk
from tkinter import ttk, simpledialog
import random
import os
import sys
import time
import threading
import json
import winreg
from PIL import Image, ImageTk, ImageDraw
import pystray
import ctypes
import imageio
import numpy as np
import shutil

# ==================== 资源路径、存档、开机自启 ====================
def resource_path(relative_path):
    if hasattr(sys, '_MEIPASS'): return os.path.join(sys._MEIPASS, relative_path)
    return os.path.join(os.path.abspath("."), relative_path)

def get_save_path():
    if getattr(sys, 'frozen', False): base = os.path.dirname(sys.executable)
    else: base = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base, 'save.json')
SAVE_FILE = get_save_path()

def get_startup_status():
    try:
        key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\Run", 0, winreg.KEY_READ)
        value, _ = winreg.QueryValueEx(key, "DesktopPet"); winreg.CloseKey(key)
        return value == sys.executable
    except: return False

def set_startup(enable):
    key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\Run", 0, winreg.KEY_SET_VALUE)
    if enable: winreg.SetValueEx(key, "DesktopPet", 0, winreg.REG_SZ, sys.executable)
    else:
        try: winreg.DeleteValue(key, "DesktopPet")
        except: pass
    winreg.CloseKey(key)

# ==================== 游戏时间系统 ====================
class GameTime:
    def __init__(self):
        self.day = 1; self.week = 1; self.weekday = 1; self.hour = 8; self.minute = 0
        self.last_tick = time.time()
        self.weekday_names = ["", "周一", "周二", "周三", "周四", "周五", "周六", "周日"]

    def tick(self):
        if time.time() - self.last_tick >= 3600:
            self.last_tick = time.time(); self.advance_hours(1)
            return True
        return False

    def advance_day(self):
        self.day += 1; self.weekday = (self.weekday % 7) + 1
        if self.weekday == 1: self.week += 1

    def advance_hours(self, h):
        self.hour += h
        while self.hour >= 24: self.hour -= 24; self.advance_day()

    def get_weekday_name(self): return self.weekday_names[self.weekday]
    def get_time_str(self): return f"📅 第{self.week}周 第{self.day}天 {self.hour:02d}:{self.minute:02d}"
    def to_dict(self): return {'day':self.day,'week':self.week,'weekday':self.weekday,'hour':self.hour,'minute':self.minute}
    def from_dict(self, d):
        self.day=d.get('day',1); self.week=d.get('week',1); self.weekday=d.get('weekday',1)
        self.hour=d.get('hour',8); self.minute=d.get('minute',0)

# ==================== 宠物状态（含缩放倍率） ====================
class PetState:
    def __init__(self):
        self.init_defaults()
        self.bubble_msg = ""; self.bubble_timer = 0
        self.idle_time = 0; self.idle_threshold = 3600
        self.water_interval = 45*60; self.eye_interval = 50*60
        self.last_water_reminder = time.time(); self.last_eye_reminder = time.time()
        self.last_danmu_time = time.time(); self.danmu_interval = random.randint(120,300)
        self._last_greeting_day = 0; self._greeted_morning = False; self._greeted_night = False
        self.total_playtime = 0; self.last_milestone_week = 0; self.last_milestone_day = 0
        self.inventory = {}
        self.scale = 1.5          # 当前缩放倍率
        self.base_w = 160         # 基准宽度
        self.base_h = 220         # 基准高度

    def init_defaults(self):
        self.satiety = 60
        self.stamina = 50
        self.hygiene = 80
        self.mood = 60
        self.gold = 50
        self.star = 0
        self.sick = False
        self.resting = False
        self.fatigue = 0
        self.consecutive_train = 0

        self.vocal = random.randint(10, 40)
        self.dance = random.randint(10, 40)
        self.acting = 10
        self.variety = 0
        self.charm = random.randint(10, 45)
        self.popularity = 0
        self.fans = 0

        self.exp = 0; self.level = 1; self.exp_to_next = 50
        self.stage = 1; self.stage_name = "素人 👤"
        self.route = 0

        self.game_time = GameTime()
        self.busy = False
        self.train_boost = {"voice":0,"fitness":0,"expression":0,"shape":0}
        self.mood_decay_reduce = 0

        self.focus_mode = False; self.focus_end_time = 0; self.focus_duration = 25*60

    @property
    def pet_w(self): return int(self.base_w * self.scale)
    @property
    def pet_h(self): return int(self.base_h * self.scale)

    @property
    def health(self): return int((self.satiety + self.stamina + self.hygiene) / 3)
    @property
    def talent(self): return int((self.vocal + self.dance + self.acting + self.variety) / 4)

    def decay(self):
        self.satiety = max(0, self.satiety - 4)
        self.hygiene = max(0, self.hygiene - 3)
        self.mood = max(0, self.mood - 2 * (1 - self.mood_decay_reduce))
        if self.hygiene < 30 and random.random() < 0.15: self.sick = True
        if self.health < 20 and random.random() < 0.3: self.sick = True
        self.game_time.tick()
        if self.stamina <= 0 and not self.resting:
            self.resting = True; self.bubble_msg = "体力耗尽，必须休息！"; self.bubble_timer = 5
        if self.resting:
            self.stamina = min(100, self.stamina + 5)
            if self.stamina >= 30:
                self.resting = False; self.bubble_msg = "体力恢复了！"; self.bubble_timer = 3
        if self.bubble_timer > 0: self.bubble_timer -= 1
        else: self.bubble_msg = ""
        self.check_promotion()

    def feed(self, satiety_amt=20, stamina_amt=0, mood_amt=0):
        if self.resting: return
        self.satiety = min(100, self.satiety + satiety_amt)
        self.stamina = min(100, self.stamina + stamina_amt)
        self.mood = min(100, self.mood + mood_amt)
        self.gain_exp(3)

    def sleep(self, amt=40):
        self.stamina = min(100, self.stamina + amt)
        self.fatigue = max(0, self.fatigue - 15)
        self.resting = False
        self.gain_exp(3)

    def cure(self):
        self.sick = False
        self.hygiene = min(100, self.hygiene + 20)

    def train(self, type_):
        if self.busy: return False, "正在进行其他活动！"
        if self.resting: return False, "需要休息！"
        if self.mood < 30: return False, "心情太差，不想训练！"
        if self.stamina < 20: return False, "体力不足！"
        self.busy = True
        return True, ""

    def do_schedule(self):
        if self.busy: return False, "正在进行其他活动！"
        if self.resting: return False, "需要休息！"
        if self.stamina < 20: return False, "体力不足！"
        self.busy = True
        return True, ""

    def apply_train_result(self, type_, modifier=1.0, extra_msg=""):
        self.busy = False
        boost = 1 + self.train_boost.get(type_, 0)
        mood_factor = 1.0
        if self.mood >= 70: mood_factor += 0.1
        elif self.mood < 30: mood_factor -= 0.3
        satiety_penalty = 1.0
        if self.satiety > 90: satiety_penalty -= 0.05
        stage_bonus = 1.0
        if self.stage < 2: stage_bonus += 0.15
        if self.route == 2: stage_bonus += 0.15
        total_multiplier = mood_factor * satiety_penalty * stage_bonus * boost * modifier

        injury = random.random() < min(0.3, self.fatigue*0.01 + self.consecutive_train*0.03)

        if type_ == "voice":
            gain = int(40 * total_multiplier)
            self.vocal += gain; msg = f"声乐课完成！唱功 +{gain}"
            if random.random() < 0.1: self.vocal += 2; msg += " 🎵开嗓！额外+2"
            cost_stamina, cost_hyg, cost_satiety, cost_mood = 25, 15, 10, 3
        elif type_ == "fitness":
            gain = int(55 * total_multiplier)
            self.dance += gain; msg = f"舞蹈集训完成！舞蹈 +{gain}"
            if random.random() < 0.05: injury = True; msg += " ⚠️加练受伤！"
            cost_stamina, cost_hyg, cost_satiety, cost_mood = 35, 30, 12, 5
        elif type_ == "expression":
            gain_act = int(45 * total_multiplier)
            gain_charm = int(10 * total_multiplier)
            self.acting += gain_act; self.charm += gain_charm
            msg = f"表演课完成！演技 +{gain_act} 魅力 +{gain_charm}"
            cost_stamina, cost_hyg, cost_satiety, cost_mood = 20, 10, 8, 2
        elif type_ == "shape":
            gain_charm = int(35 * total_multiplier)
            self.charm += gain_charm; self.satiety = max(0, self.satiety - 10)
            msg = f"形体管理完成！魅力 +{gain_charm}"
            cost_stamina, cost_hyg, cost_satiety, cost_mood = 30, 20, 10, 3
        else:
            return "未知训练"

        self.stamina = max(0, self.stamina - cost_stamina)
        self.hygiene = max(0, self.hygiene - cost_hyg)
        self.satiety = max(0, self.satiety - cost_satiety)
        self.mood = max(0, self.mood - cost_mood)
        self.fatigue = min(100, self.fatigue + random.randint(5,15))
        self.consecutive_train += 1
        self.gain_exp(8)
        if injury: self.sick = True; msg += " 🤕受伤生病！"
        if extra_msg: msg += " " + extra_msg
        self.train_boost[type_] = 0
        return msg

    def apply_schedule_result(self, modifier=1.0, extra_msg=""):
        self.busy = False
        self.stamina = max(0, self.stamina - random.randint(20,40))
        self.hygiene = max(0, self.hygiene - random.randint(5,25))
        self.satiety = max(0, self.satiety - random.randint(8,12))
        self.fatigue = min(100, self.fatigue + random.randint(5,10))
        rate = min(0.9, (self.talent + self.charm) / 250)
        if self.mood > 70: rate += 0.1
        rate *= modifier
        if random.random() < rate:
            gold = random.randint(20,50) + self.popularity // 5
            pop = random.randint(5,15); fans = random.randint(10,30)
            self.gold += gold; self.popularity += pop; self.fans += fans
            self.mood = min(100, self.mood + 8)
            msg = f"通告成功！💰+{gold} 人气+{pop} 粉丝+{fans}"
        else:
            self.mood = max(0, self.mood - 20); msg = "通告失败……心情大幅下降"
        if extra_msg: msg += " " + extra_msg
        self.gain_exp(10)
        return msg

    def check_promotion(self):
        s = self
        if s.stage == 2:
            if s.vocal >= 80 and s.dance >= 80 and s.charm >= 60:
                s.promote(3, "公开练习生 🌱", route=1)
            elif (s.vocal >= 120 or s.dance >= 120 or s.acting >= 120) and random.random() < 0.05:
                s.promote(4, "未公开练习生 🔒", route=2)
        elif s.stage in (3, 4):
            if s.vocal >= 150 and s.dance >= 150 and s.charm >= 120:
                s.promote(5, "新人偶像 🚀")
        elif s.stage == 5:
            if s.popularity >= 5000 and s.charm >= 200 and (s.vocal >= 250 or s.dance >= 250 or s.acting >= 250):
                s.promote(6, "当红明星 👑")
        elif s.stage == 6:
            if s.popularity >= 15000 and s.charm >= 350 and ((s.vocal >= 400 and s.dance >= 400) or (s.vocal >= 400 and s.acting >= 400) or (s.dance >= 400 and s.acting >= 400)):
                s.promote(7, "时代巨星 🌟")

    def promote(self, new_stage, name, route=None):
        self.stage = new_stage
        self.stage_name = name
        if route is not None: self.route = route
        self.mood = 100
        self.gold += 100
        self.fans += 50

    def gain_exp(self, amt):
        self.exp += amt
        while self.exp >= self.exp_to_next:
            self.exp -= self.exp_to_next; self.level += 1; self.exp_to_next = int(self.exp_to_next * 1.5)

    def to_dict(self):
        return {
            'satiety': self.satiety, 'stamina': self.stamina, 'hygiene': self.hygiene, 'mood': self.mood,
            'gold': self.gold, 'star': self.star, 'sick': self.sick, 'resting': self.resting,
            'fatigue': self.fatigue, 'consecutive_train': self.consecutive_train,
            'vocal': self.vocal, 'dance': self.dance, 'acting': self.acting, 'variety': self.variety,
            'charm': self.charm, 'popularity': self.popularity, 'fans': self.fans,
            'exp': self.exp, 'level': self.level, 'exp_to_next': self.exp_to_next,
            'stage': self.stage, 'stage_name': self.stage_name, 'route': self.route,
            'game_time': self.game_time.to_dict(),
            'focus_mode': self.focus_mode, 'focus_end_time': self.focus_end_time, 'focus_duration': self.focus_duration,
            'total_playtime': self.total_playtime, 'last_milestone_week': self.last_milestone_week, 'last_milestone_day': self.last_milestone_day,
            'inventory': self.inventory,
            'scale': self.scale
        }

    def from_dict(self, d):
        self.satiety = d.get('satiety', d.get('hunger', 60))
        self.stamina = d.get('stamina', d.get('energy', 50))
        self.hygiene = d.get('hygiene', 80)
        self.mood = d.get('mood', 60)
        self.gold = d.get('gold', 50)
        self.star = d.get('star', 0)
        self.sick = d.get('sick', False)
        self.resting = d.get('resting', False)
        self.fatigue = d.get('fatigue', 0)
        self.consecutive_train = d.get('consecutive_train', 0)
        self.vocal = d.get('vocal', random.randint(10,40))
        self.dance = d.get('dance', random.randint(10,40))
        self.acting = d.get('acting', 10)
        self.variety = d.get('variety', 0)
        self.charm = d.get('charm', random.randint(10,45))
        self.popularity = d.get('popularity', 0)
        self.fans = d.get('fans', 0)
        self.exp = d.get('exp', 0)
        self.level = d.get('level', 1)
        self.exp_to_next = d.get('exp_to_next', 50)
        self.stage = d.get('stage', 1)
        self.stage_name = d.get('stage_name', '素人 👤')
        self.route = d.get('route', 0)
        if 'game_time' in d: self.game_time.from_dict(d['game_time'])
        self.focus_mode = d.get('focus_mode', False)
        self.focus_end_time = d.get('focus_end_time', 0)
        self.focus_duration = d.get('focus_duration', 25*60)
        self.total_playtime = d.get('total_playtime', 0)
        self.last_milestone_week = d.get('last_milestone_week', 0)
        self.last_milestone_day = d.get('last_milestone_day', 0)
        self.inventory = d.get('inventory', {})
        self.scale = d.get('scale', 1.5)

    def save(self):
        try:
            with open(SAVE_FILE,'w',encoding='utf-8') as f: json.dump(self.to_dict(), f, ensure_ascii=False, indent=2)
        except Exception as e: print(f"存档失败:{e}")

    def load(self):
        if not os.path.exists(SAVE_FILE): return
        try:
            with open(SAVE_FILE,'r',encoding='utf-8') as f: data = json.load(f); self.from_dict(data)
        except Exception as e: print(f"读档失败:{e}")

# ==================== 通用活动窗口 ====================
class ActivityWindow:
    def __init__(self, parent, title, duration, on_finish, on_cancel=None, pet_x=0, pet_y=0, pet_w=160, pet_h=220):
        self.win = tk.Toplevel(parent); self.win.overrideredirect(True); self.win.wm_attributes("-topmost",True)
        self.win.wm_attributes("-transparentcolor","#F0F0F0"); self.win.configure(bg="#F0F0F0")
        bw, bh = 280, 80
        self.pos_x = pet_x + (pet_w - bw)//2; self.pos_y = pet_y + pet_h + 10
        self.win.geometry(f"{bw}x{bh}+{self.pos_x}+{self.pos_y}")
        tk.Label(self.win, text=title, font=("微软雅黑",10,"bold"), fg="black", bg="#F0F0F0").pack()
        self.bar = tk.Canvas(self.win, width=200, height=15, bg="white", highlightthickness=0); self.bar.pack(pady=5)
        btn_frame = tk.Frame(self.win, bg="#F0F0F0"); btn_frame.pack()
        tk.Button(btn_frame, text="中止", command=self.cancel, bg="#ff4d4d", fg="white", font=("微软雅黑",8)).pack(side=tk.LEFT, padx=5)
        self.on_finish = on_finish; self.on_cancel = on_cancel
        self.duration = duration; self.elapsed = 0; self.step = 0.1; self.cancelled = False
        self.update()

    def update(self):
        if not self.win.winfo_exists(): return
        if self.cancelled: return
        if self.elapsed >= self.duration: self.finish(); return
        self.elapsed += self.step
        pct = min(100, self.elapsed/self.duration*100)
        self.bar.delete("all"); self.bar.create_rectangle(0,0,200*pct/100,15,fill="#4CAF50",outline="")
        self.win.after(100, self.update)

    def cancel(self):
        self.cancelled = True; self.win.destroy()
        if self.on_cancel: self.on_cancel()

    def finish(self):
        if self.cancelled: return
        self.win.destroy()
        if self.on_finish: self.on_finish()

# ==================== 商店 v5.0 ====================
class ShopWindow:
    def __init__(self, parent, pet_state, buy_callback=None):
        self.win = tk.Toplevel(parent); self.win.title("练习生百货 v5.0"); self.win.geometry("480x640")
        self.pet_state = pet_state; self.buy_callback = buy_callback
        self.gold_label = tk.Label(self.win, text=f"💰 {self.pet_state.gold}金币", font=("微软雅黑",11,"bold"))
        self.gold_label.pack(pady=8)
        self.notebook = ttk.Notebook(self.win); self.notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        cats = ["🍽️ 能量补给", "✨ 洁护管理", "📚 自我提升", "👗 造型衣橱", "🎁 社交礼物", "⚡ 便捷服务"]
        for i, cat in enumerate(cats):
            frame = tk.Frame(self.notebook, bg="#F8F8F8"); self.notebook.add(frame, text=cat)
            self.build_category(frame, i)

    def build_category(self, parent, cat_idx):
        canvas = tk.Canvas(parent, width=440, height=480, bg="#F8F8F8", highlightthickness=0)
        scrollbar = tk.Scrollbar(parent, orient="vertical", command=canvas.yview)
        scroll_frame = tk.Frame(canvas, bg="#F8F8F8")
        scroll_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0,0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side="left", fill="both", expand=True); scrollbar.pack(side="right", fill="y")
        items = self.get_items(cat_idx)
        if cat_idx == 0:
            self._build_subgroup(scroll_frame, "🥗 自律轻食", items[0:3], "#E8F5E9")
            self._build_subgroup(scroll_frame, "🥩 高蛋白轻食", items[3:6], "#FFF3E0")
            self._build_subgroup(scroll_frame, "🧋 饮品续命", items[6:10], "#F3E5F5")
            self._build_subgroup(scroll_frame, "🚨 应急充饥", items[10:12], "#FFEBEE")
        elif cat_idx == 1:
            self._build_subgroup(scroll_frame, "💆 精致护肤", items[0:7], "#FCE4EC")
            self._build_subgroup(scroll_frame, "🧖 美容SPA", items[7:10], "#E0F7FA")
        else:
            self._build_subgroup(scroll_frame, "", items, "#F8F8F8")

    def _build_subgroup(self, parent, title, items, bg_color):
        if title:
            labelframe = tk.LabelFrame(parent, text=title, font=("微软雅黑",11,"bold"), fg="#8B5CF6", bg=bg_color, bd=2, relief=tk.RIDGE)
            labelframe.pack(fill=tk.X, padx=10, pady=6)
            container = labelframe
        else:
            container = tk.Frame(parent, bg="#F8F8F8"); container.pack(fill=tk.X, padx=10, pady=6)
        for i, (display_name, price, eff, desc) in enumerate(items):
            card = tk.Frame(container, bg="white" if i%2==0 else "#FAFAFA", bd=1, relief=tk.GROOVE)
            card.pack(fill=tk.X, pady=2, padx=4)
            tk.Label(card, text=display_name, font=("微软雅黑",10,"bold"), bg=card["bg"]).pack(anchor="w", padx=8, pady=(4,0))
            tk.Label(card, text=eff, font=("微软雅黑",8), fg="#666", bg=card["bg"]).pack(anchor="w", padx=8)
            if desc: tk.Label(card, text=desc, font=("微软雅黑",8), fg="gray", bg=card["bg"], wraplength=280).pack(anchor="w", padx=8)
            price_frame = tk.Frame(card, bg=card["bg"]); price_frame.pack(anchor="e", padx=8, pady=(0,4))
            if price == 0:
                btn = tk.Button(price_frame, text="免费", command=lambda d=display_name,p=price: self.buy(d,p), bg="#4CAF50", fg="white", font=("微软雅黑",8))
            else:
                btn = tk.Button(price_frame, text=f"购买 {price}G", command=lambda d=display_name,p=price: self.buy(d,p), bg="#8B5CF6", fg="white", font=("微软雅黑",8))
            btn.pack(side=tk.RIGHT, padx=2)

    def buy(self, display_name, price):
        s = self.pet_state
        clean_name = display_name.split(' ', 1)[1] if ' ' in display_name else display_name
        if price > 0 and s.gold < price: self.show_error("金币不足！"); return
        if price > 0: s.gold -= price
        s.inventory[clean_name] = s.inventory.get(clean_name, 0) + 1
        self.refresh_gold()
        if self.buy_callback: self.buy_callback(clean_name, price)
        self.show_info(f"已购买 {clean_name}，已放入背包")

    def refresh_gold(self): self.gold_label.config(text=f"💰 {self.pet_state.gold}金币")

    def show_error(self, msg):
        top = tk.Toplevel(self.win); top.title("提示")
        tk.Label(top, text=msg, font=("微软雅黑",10)).pack(padx=20,pady=10)
        tk.Button(top, text="确定", command=top.destroy).pack()

    def show_info(self, msg):
        top = tk.Toplevel(self.win); top.title("提示")
        tk.Label(top, text=msg, font=("微软雅黑",10)).pack(padx=20,pady=10)
        tk.Button(top, text="确定", command=top.destroy).pack()
        top.after(2000, top.destroy)

    def get_items(self, idx):
        if idx == 0: return [
            ("🥑 超级食物碗", 12, "🍖+30 ⚡+5 20s", "羽衣甘蓝打底，奇亚籽点缀。"),
            ("🍣 波奇饭便当", 22, "🍖+40 ⚡+8 😊+5 25s", "三文鱼+牛油果，偷偷带进练习室。"),
            ("🥤 绿色排毒果汁", 15, "🍖+15 消除水肿 15s", "一口下去感觉自己变轻了。"),
            ("🥩 牛肉沙拉碗", 28, "🍖+55 ⚡+10 😊+8 35s", "高蛋白低碳水，练完舞来一碗刚好。"),
            ("🍲 泡菜豆腐锅", 20, "🍖+50 ⚡+5 😊+10 40s", "热乎乎辣得刚好，吃完出汗感觉排毒。"),
            ("🍜 荞麦冷面", 18, "🍖+45 ⚡+5 😊+5 30s", "夏天练习室没空调时的救赎。"),
            ("☕ 冰美式", 15, "🍖+5 ⚡+15 消除困倦 15s", "不喝冰美式的练习生不是合格打工人。"),
            ("🍵 抹茶燕麦拿铁", 25, "🍖+10 ⚡+5 😊+20 20s", "魅力+3(半天)，无糖也能喝出高级感。"),
            ("🧋 燕麦拿铁", 22, "🍖+15 ⚡+8 😊+25 20s", "植物奶替代，无糖但心里甜。"),
            ("🫧 气泡冷萃", 20, "🍖+5 ⚡+20 😊+10 15s", "咖啡因+气泡，提神醒脑双重暴击。"),
            ("🍙 三角饭团", 8, "🍖+25 ⚡+3 10s", "便利店的最后救赎，便宜管饱。"),
            ("🍌 能量香蕉", 5, "🍖+15 ⚡+8 8s", "最快充能，没有之一。"),
        ]
        elif idx == 1: return [
            ("💄 唇膜", 8, "✨+5 😊+8 15s", ""),
            ("👁️ 眼膜", 10, "✨+6 消除疲惫 20s", ""),
            ("🧖 清洁泥膜", 12, "🧹+30 ✨+8 25s", ""),
            ("💧 补水面膜", 15, "✨+10 😊+8 30s", ""),
            ("🌿 面部刮痧", 18, "✨+12 😊+5 消除水肿 35s", ""),
            ("🧴 精华导入", 25, "🧹+10 ✨+15 40s", ""),
            ("✨ 一键精致护理", 40, "🧹+40 ✨+20 😊+15 60s", "泥膜→面膜→精华，省12金币"),
            ("🧖 汗蒸排毒", 22, "🧹+70 😊+10 ✨+8 45s", ""),
            ("💆 全身按摩", 35, "⚡+40 😊+30 50s", ""),
            ("🕯️ 香薰水疗", 45, "🧹+100 ⚡+10 😊+40 ✨+12 60s", ""),
        ]
        elif idx == 2: return [
            ("🎧 降噪耳机", 60, "声乐训练+25%", "隔绝世界，只听自己的声音。"),
            ("👟 联名舞鞋", 60, "舞蹈训练+25%", "穿上感觉能多转三圈。"),
            ("🎬 演技拆解课", 60, "表演训练+25%", "教你读懂镜头的语言。"),
            ("🧘 正念冥想课", 55, "😊+50 消除焦虑", "呼吸，然后继续发光。"),
            ("📱 直拍复盘", 250, "随机才华+100", "逐帧分析，连表情管理都不放过。"),
            ("📖 《偶像的品格》", 500, "✨+20 人气获取+5%", "写给想认真做偶像的人。"),
            ("🤖 AI舞蹈评分", 120, "舞蹈训练+35%", "科技赋能，每个角度都被审视。"),
        ]
        elif idx == 3: return [
            ("👕 OVERSIZE卫衣", 80, "✨+3 心情消耗-10%", "偷懒穿搭也是时尚。"),
            ("🧥 长款风衣", 120, "✨+5 雨天额外+8", "氛围感拿捏住了。"),
            ("🎽 复古运动套装", 130, "舞蹈+5% 体力消耗-5%", "90年代复古回潮。"),
            ("🩰 芭蕾核训练服", 150, "舞蹈+3% ✨+5", "把杆上的优雅。"),
            ("✨ 打歌舞台定制装", 400, "✨+15 人气获取+10%", "灯光下的C位。"),
            ("🖤 暗黑概念装", 350, "✨+12 综艺感+8", "概念消化力就是表现力。"),
            ("👑 颁奖典礼高定", 500, "✨+25 全属性+5", "红毯即战场。"),
            ("🎭 周年限定皮肤", 500, "✨+20 特殊互动动画", "感谢你陪我走过。"),
        ]
        elif idx == 4: return [
            ("💐 手写应援信", 30, "好感+15", "一笔一画都是真心。"),
            ("🎂 应援咖啡车", 120, "好感+40", "给队友的生日惊喜。"),
            ("🕶️ 前辈同款墨镜", 100, "好感+30", "致敬前辈。"),
            ("🍷 手酿梅子酒", 80, "好感+35", "给制作人的心意。"),
            ("🎫 演唱会VIP席", 200, "好感+50", "共享高光时刻。"),
            ("📸 双人合照集", 250, "好感+60", "记录我们的瞬间。"),
        ]
        elif idx == 5: return [
            ("🎫 行程加速卡", 30, "训练/通告耗时减半", "时间管理大师。"),
            ("🔄 考核重置券", 80, "周考核可重来一次", "再来一次的机会。"),
            ("📋 自动排程助手", 50, "本周自动最优排课", "AI帮你安排。"),
            ("🌟 幸运符", 60, "当天随机事件偏向正面", "转运神器。"),
        ]
        return []

# ==================== 状态窗口 ====================
class StatusWindow:
    def __init__(self, parent, pet_state):
        self.win = tk.Toplevel(parent); self.win.title("练习生状态"); self.win.geometry("300x500")
        self.pet_state = pet_state
        self.build()

    def build(self):
        for w in self.win.winfo_children(): w.destroy()
        s = self.pet_state
        now = time.localtime()
        weekday_map = ["周一","周二","周三","周四","周五","周六","周日"]
        real_time_str = f"{now.tm_year}-{now.tm_mon:02d}-{now.tm_mday:02d} {weekday_map[now.tm_wday]} {now.tm_hour:02d}:{now.tm_min:02d}:{now.tm_sec:02d}"
        tk.Label(self.win, text=f"🕒 {real_time_str}", font=("微软雅黑",10,"bold")).pack(pady=5)
        tk.Label(self.win, text=s.game_time.get_time_str(), font=("微软雅黑",9), fg="gray").pack()
        tk.Label(self.win, text=f"身份：{s.stage_name} (路线{'公开' if s.route==1 else '未公开' if s.route==2 else '未定'})", font=("微软雅黑",10)).pack()
        tk.Label(self.win, text=f"⭐等级 {s.level}   💰金币 {s.gold}", font=("微软雅黑",10)).pack()
        play_sec = int(s.total_playtime)
        play_str = f"{play_sec//3600}小时{(play_sec%3600)//60}分钟"
        tk.Label(self.win, text=f"⏱️ 陪伴时长：{play_str}", font=("微软雅黑",10)).pack()
        tk.Label(self.win, text=f"❤️ 健康度：{s.health}/100", font=("微软雅黑",10)).pack()
        attrs = [
            f"🍖饱食 {int(s.satiety)}/100     😊心情 {int(s.mood)}/100",
            f"⚡体力 {int(s.stamina)}/100     🧹清洁 {int(s.hygiene)}/100",
            f"😫疲劳 {int(s.fatigue)}     🏥 {'🤒生病' if s.sick else '😄健康'}",
            f"🎤唱功 {int(s.vocal)}     💃舞蹈 {int(s.dance)}",
            f"🎭演技 {int(s.acting)}     🎪综艺 {int(s.variety)}",
            f"✨魅力 {int(s.charm)}     📈人气 {int(s.popularity)}",
            f"👥粉丝 {int(s.fans)}"
        ]
        for attr in attrs: tk.Label(self.win, text=attr, font=("微软雅黑",10)).pack(anchor="w", padx=10)

# ==================== 训练/通告进度条 ====================
class PerformanceWindow:
    def __init__(self, parent, pet_state, act_type, act_sub, callback, pet_x, pet_y, pet_w=160, pet_h=220):
        self.win = tk.Toplevel(parent); self.win.overrideredirect(True); self.win.wm_attributes("-topmost",True)
        self.win.wm_attributes("-transparentcolor","#F0F0F0"); self.win.configure(bg="#F0F0F0")
        bw, bh = 280, 80; self.pet_w = pet_w; self.pet_h = pet_h
        self.pos_x = pet_x + (pet_w - bw)//2; self.pos_y = pet_y + pet_h + 10
        self.win.geometry(f"{bw}x{bh}+{self.pos_x}+{self.pos_y}")
        titles = {("train","voice"):"🎤 声乐课",("train","fitness"):"💃 舞蹈集训",("train","expression"):"🎭 表演工作坊",("train","shape"):"🏋️ 形体管理",("schedule",""):"📺 通告"}
        title = titles.get((act_type,act_sub),"活动中")
        tk.Label(self.win, text=title, font=("微软雅黑",10,"bold"), fg="black", bg="#F0F0F0").pack()
        self.bar = tk.Canvas(self.win, width=250, height=20, bg="white", highlightthickness=0); self.bar.pack(pady=5)
        self.time_label = tk.Label(self.win, text="", font=("微软雅黑",9), fg="black", bg="#F0F0F0"); self.time_label.pack()
        self.pet_state = pet_state; self.act_type = act_type; self.act_sub = act_sub; self.callback = callback
        if act_type=="train":
            base = random.randint(45*60,60*60) if act_sub!="shape" else 40*60
            base += random.randint(-5*60,5*60); self.duration = max(10,base)
            self.game_hours = random.randint(3,4) if act_sub!="shape" else 2.5
        else:
            base = random.randint(60*60,90*60); base += random.randint(-5*60,5*60); self.duration = max(10,base)
            self.game_hours = random.randint(4,6)
        self.elapsed=0; self.step=1; self.event_triggered=False; self.event_modifier=1.0; self.event_msg=""; self.extra_dur=0
        self.update()

    def update(self):
        if not self.win.winfo_exists(): return
        if self.elapsed >= self.duration+self.extra_dur: self.finish(); return
        if not self.event_triggered and self.elapsed >= self.duration//2:
            self.event_triggered = True
            r = random.random()
            if self.act_type=="train":
                if r<0.2: self.extra_dur=-random.randint(5*60,15*60); self.event_modifier=1.1; self.event_msg="提前下课！"
                elif r<0.4: self.extra_dur=random.randint(10*60,20*60); self.event_modifier=0.9; self.event_msg="加练……"
            else:
                if r<0.2: self.extra_dur=-random.randint(10*60,20*60); self.event_modifier=1.1; self.event_msg="提前收工！"
                elif r<0.4: self.extra_dur=random.randint(15*60,30*60); self.event_modifier=0.9; self.event_msg="加戏……"
            if self.event_msg: self.time_label.config(text=self.time_label.cget("text")+f" ({self.event_msg})")
        self.elapsed += self.step; total = self.duration+self.extra_dur
        pct = min(100, self.elapsed/total*100)
        self.bar.delete("all"); self.bar.create_rectangle(0,0,250*pct/100,20,fill="#4CAF50",outline="")
        rem = max(0, total-self.elapsed); self.time_label.config(text=f"剩余 {rem//60:02d}:{rem%60:02d}")
        self.win.after(1000, self.update)

    def finish(self):
        self.pet_state.game_time.advance_hours(self.game_hours)
        if self.act_type=="train":
            msg = self.pet_state.apply_train_result(self.act_sub, modifier=self.event_modifier, extra_msg=self.event_msg)
        else:
            msg = self.pet_state.apply_schedule_result(modifier=self.event_modifier, extra_msg=self.event_msg)
        self.win.destroy()
        if self.callback: self.callback(msg)

    def move_to(self, x, y):
        self.pos_x = x + (self.pet_w-280)//2; self.pos_y = y + self.pet_h + 10
        self.win.geometry(f"+{self.pos_x}+{self.pos_y}")

# ==================== 空闲检测 ====================
class ActivityMonitor:
    @staticmethod
    def get_idle_seconds():
        class LASTINPUTINFO(ctypes.Structure): _fields_ = [('cbSize', ctypes.c_uint), ('dwTime', ctypes.c_uint)]
        lii = LASTINPUTINFO(); lii.cbSize = ctypes.sizeof(LASTINPUTINFO)
        if ctypes.windll.user32.GetLastInputInfo(ctypes.byref(lii)):
            millis = ctypes.windll.kernel32.GetTickCount() - lii.dwTime
            return millis/1000.0
        return 0

# ==================== 桌面宠物主窗口 ====================
class DesktopPet:
    def __init__(self, image_folder="pet_frames"):
        self.state = PetState(); self.state.load()
        self.image_folder = image_folder
        self.active_notifications = []

        self.root = tk.Tk(); self.root.title("练习生桌面宠物"); self.root.geometry("1x1+9999+9999"); self.root.withdraw()
        self.pet_win = tk.Toplevel(self.root); self.pet_win.overrideredirect(True); self.pet_win.wm_attributes("-topmost",True)
        self.pet_win.wm_attributes("-transparentcolor","#F0F0F0"); self.pet_win.configure(bg="#F0F0F0")
        self.pet_w = self.state.pet_w
        self.pet_h = self.state.pet_h
        self.x = self.pet_win.winfo_screenwidth()//2; self.y = self.pet_win.winfo_screenheight()//2
        self.pet_win.geometry(f"{self.pet_w}x{self.pet_h}+{self.x}+{self.y}")

        # 气泡窗口
        self.bubble_win = tk.Toplevel(self.pet_win); self.bubble_win.overrideredirect(True); self.bubble_win.wm_attributes("-topmost",True)
        self.bubble_win.wm_attributes("-transparentcolor","#F0F0F0"); self.bubble_win.configure(bg="#F0F0F0")
        self.bubble_win.geometry(f"200x40+{self.x-20}+{self.y-50}")
        self.bubble_label = tk.Label(self.bubble_win, text="", fg="black", bg="#F0F0F0",
                                     font=("微软雅黑",8), wraplength=190)
        self.bubble_label.pack(); self.bubble_win.withdraw()

        # 动画标签
        self.anim_label = tk.Label(self.pet_win, bd=0, bg="#F0F0F0")
        self.anim_label.pack()

        # 确定基础路径
        if getattr(sys, 'frozen', False):
            self.base_dir = os.path.dirname(sys.executable)
        else:
            self.base_dir = os.path.dirname(os.path.abspath(__file__))

        # 显示进度条，后台生成缓存（界面不会卡死）
        self.show_progress_bar("正在准备动画缓存，请稍候...")
        self.cache_thread = threading.Thread(target=self._generate_caches_async, daemon=True)
        self.cache_thread.start()
        self.root.after(100, self._check_cache_thread)

        self.performance_win = None; self.shop_win = None; self.danmu_win = None; self.current_activity = None
        self.toast_win = None

        self.tray = None; self.create_tray(); threading.Thread(target=self.tray.run, daemon=True).start()

        # 事件绑定和定时循环将在缓存完成后启动
        self.drag_data = {"x":0,"y":0}

    # ---------- 后台缓存生成 ----------
    def _generate_caches_async(self):
        """在子线程中生成所有缓存"""
        scales = [1.5, 2.0, 2.5]
        for scale in scales:
            if not self.cache_exists(scale, "greet"):
                self.ensure_cache_for_scale(scale, "greet")
            if not self.cache_exists(scale, "idle"):
                self.ensure_cache_for_scale(scale, "idle")

    def _check_cache_thread(self):
        """主线程定时检查缓存线程是否结束"""
        if self.cache_thread and self.cache_thread.is_alive():
            self.root.after(100, self._check_cache_thread)
        else:
            if hasattr(self, 'progress_win') and self.progress_win:
                self.progress_win.destroy()
            self._on_cache_ready()

    def _on_cache_ready(self):
        """缓存完成后，加载动画并显示宠物"""
        # 加载动画和静态形象
        self.anim_greet_frames, self.anim_idle_frames = self.load_current_anim_frames()

        self.static_img = None
        self.frames = []; self.current_frame = 0
        self.has_image = self.load_frames(self.image_folder)
        if self.has_image:
            self.static_img = self.frames[0]
        else:
            img = Image.new("RGBA", (self.pet_w, self.pet_h), (0,0,0,0))
            draw = ImageDraw.Draw(img)
            draw.ellipse((30,30,self.pet_w-30,self.pet_h-30), fill="orange", outline="white", width=2)
            self.static_img = ImageTk.PhotoImage(img)

        self.current_anim = None
        self.anim_index = 0
        self.anim_after_id = None

        if self.anim_greet_frames:
            self.play_animation(self.anim_greet_frames, loop=False, callback=self.switch_to_idle)
        else:
            self.anim_label.configure(image=self.static_img)

        # 启动事件绑定和所有定时循环
        self.bind_events()
        self.decay_timer()
        self.companion_loop()
        self.auto_save_loop()

    # ---------- 进度条窗口 ----------
    def show_progress_bar(self, title):
        """显示一个居中的进度条窗口"""
        self.progress_win = tk.Toplevel(self.root)
        self.progress_win.title("加载中")
        self.progress_win.geometry("300x100")
        self.progress_win.resizable(False, False)
        # 居中
        self.progress_win.update_idletasks()
        sw = self.progress_win.winfo_screenwidth()
        sh = self.progress_win.winfo_screenheight()
        x = (sw - 300) // 2
        y = (sh - 100) // 2
        self.progress_win.geometry(f"+{x}+{y}")
        tk.Label(self.progress_win, text=title, font=("微软雅黑", 11)).pack(pady=15)
        self.progress_bar = ttk.Progressbar(self.progress_win, length=250, mode='indeterminate')
        self.progress_bar.pack(pady=10)
        self.progress_bar.start(10)
        self.progress_win.lift()

    # ---------- 缓存相关 ----------
    def cache_exists(self, scale, base_name):
        cache_dir = os.path.join(self.base_dir, f"{base_name}_{scale}x_frames")
        return os.path.isdir(cache_dir) and os.listdir(cache_dir)

    def ensure_cache_for_scale(self, scale, base_name):
        """如果某倍率缓存不存在，则从视频生成"""
        cache_dir = os.path.join(self.base_dir, f"{base_name}_{scale}x_frames")
        if not os.path.isdir(cache_dir) or not os.listdir(cache_dir):
            video_path = None
            for ext in [".webm", ".mp4"]:
                candidate = os.path.join(self.base_dir, f"{base_name}{ext}")
                if os.path.exists(candidate):
                    video_path = candidate
                    break
            if video_path:
                w = int(160 * scale)
                h = int(220 * scale)
                self.process_video_to_cache(video_path, cache_dir, w, h)

    def process_video_to_cache(self, video_path, cache_dir, target_w, target_h):
        """处理视频并保存为透明 PNG 序列（保持比例、居中填充）"""
        try:
            reader = imageio.get_reader(video_path)
            os.makedirs(cache_dir, exist_ok=True)
            ref_r, ref_g, ref_b = 149, 93, 190
            max_dist = 60
            red_protect_r = 200
            red_protect_b = 120
            bg_color = (240, 240, 240, 255)
            for i, frame in enumerate(reader):
                img = Image.fromarray(frame).convert("RGBA")
                arr = np.array(img)
                dist = np.sqrt(np.sum((arr[:,:,:3].astype(np.float32) - np.array([ref_r,ref_g,ref_b]).astype(np.float32))**2, axis=2))
                is_purple = (dist < max_dist) & (arr[:,:,3] > 200)
                is_red_tongue = (arr[:,:,0] > red_protect_r) & (arr[:,:,2] < red_protect_b)
                mask = is_purple & (~is_red_tongue)
                arr[mask] = bg_color
                img = Image.fromarray(arr)
                img.thumbnail((target_w, target_h), Image.LANCZOS)
                canvas = Image.new("RGBA", (target_w, target_h), bg_color)
                paste_x = (target_w - img.width) // 2
                paste_y = (target_h - img.height) // 2
                canvas.paste(img, (paste_x, paste_y), img)
                canvas.save(os.path.join(cache_dir, f"frame_{i:04d}.png"))
            reader.close()
        except Exception as e:
            print(f"生成缓存失败 {cache_dir}: {e}")

    def load_current_anim_frames(self):
        scale = self.state.scale
        greet_dir = os.path.join(self.base_dir, f"greet_{scale}x_frames")
        idle_dir = os.path.join(self.base_dir, f"idle_{scale}x_frames")
        greet_frames = self.load_png_frames(greet_dir)
        idle_frames = self.load_png_frames(idle_dir) if os.path.isdir(idle_dir) else None
        return greet_frames, idle_frames

    def set_scale(self, scale):
        self.state.scale = scale
        self.state.save()
        self.pet_w = self.state.pet_w
        self.pet_h = self.state.pet_h
        self.pet_win.geometry(f"{self.pet_w}x{self.pet_h}+{self.x}+{self.y}")
        self.anim_greet_frames, self.anim_idle_frames = self.load_current_anim_frames()
        self.static_img = None
        self.frames = []
        self.has_image = self.load_frames(self.image_folder) if os.path.isdir(self.image_folder) else False
        if self.has_image:
            self.static_img = self.frames[0]
        else:
            img = Image.new("RGBA", (self.pet_w, self.pet_h), (0,0,0,0))
            draw = ImageDraw.Draw(img)
            draw.ellipse((30,30,self.pet_w-30,self.pet_h-30), fill="orange", outline="white", width=2)
            self.static_img = ImageTk.PhotoImage(img)
        if self.current_anim is not None:
            if self.anim_after_id: self.pet_win.after_cancel(self.anim_after_id)
            if self.current_anim == self.anim_greet_frames:
                self.play_animation(self.anim_greet_frames, loop=False, callback=self.switch_to_idle)
            elif self.current_anim == self.anim_idle_frames:
                self.play_animation(self.anim_idle_frames, loop=True)
            else:
                self.anim_label.configure(image=self.static_img)
        else:
            self.anim_label.configure(image=self.static_img)
        if self.bubble_win and self.bubble_win.winfo_exists():
            self.bubble_win.geometry(f"200x40+{self.x-20}+{self.y-50}")

    def load_png_frames(self, folder_path):
        if not os.path.isdir(folder_path): return None
        files = sorted([f for f in os.listdir(folder_path) if f.lower().endswith('.png')])
        if not files: return None
        frames = []
        for f in files:
            img = Image.open(os.path.join(folder_path, f)).convert("RGBA")
            frames.append(ImageTk.PhotoImage(img))
        return frames

    def load_frames(self, folder):
        if not os.path.isdir(folder): return False
        files = sorted([f for f in os.listdir(folder) if f.lower().endswith((".png",".gif"))])
        if not files: return False
        for f in files:
            try:
                img = Image.open(os.path.join(folder, f)).convert("RGBA")
                img.thumbnail((self.pet_w, self.pet_h), Image.LANCZOS)
                self.frames.append(ImageTk.PhotoImage(img))
            except: pass
        return len(self.frames) > 0

    def play_animation(self, anim_list, loop=False, callback=None):
        if self.anim_after_id: self.pet_win.after_cancel(self.anim_after_id)
        self.current_anim = anim_list
        self.anim_index = 0
        self._animate_frame(loop, callback)

    def _animate_frame(self, loop, callback):
        if not self.current_anim: return
        if self.anim_index >= len(self.current_anim):
            if loop: self.anim_index = 0
            else:
                if callback: callback()
                return
        frame = self.current_anim[self.anim_index]
        self.anim_label.configure(image=frame)
        self.anim_index += 1
        self.anim_after_id = self.pet_win.after(50, self._animate_frame, loop, callback)

    def switch_to_idle(self):
        if self.anim_idle_frames:
            self.play_animation(self.anim_idle_frames, loop=True)
        else:
            if self.static_img:
                self.anim_label.configure(image=self.static_img)

    def bind_events(self):
        self.anim_label.bind("<Button-1>", self.start_drag)
        self.anim_label.bind("<B1-Motion>", self.on_drag)
        self.anim_label.bind("<Double-Button-1>", lambda e: self.hide_pet())
        self.anim_label.bind("<Button-3>", self.right_click_menu)

    feed_effect_map = {
        "超级食物碗": (20, lambda s: s.feed(30,5,0)),
        "波奇饭便当": (25, lambda s: s.feed(40,8,5)),
        "绿色排毒果汁": (15, lambda s: (setattr(s,'satiety',min(100,s.satiety+15)), s.gain_exp(3))),
        "牛肉沙拉碗": (35, lambda s: s.feed(55,10,8)),
        "泡菜豆腐锅": (40, lambda s: s.feed(50,5,10)),
        "荞麦冷面": (30, lambda s: s.feed(45,5,5)),
        "冰美式": (15, lambda s: (setattr(s,'satiety',min(100,s.satiety+5)), setattr(s,'stamina',min(100,s.stamina+15)), s.gain_exp(3))),
        "抹茶燕麦拿铁": (20, lambda s: (setattr(s,'satiety',min(100,s.satiety+10)), setattr(s,'stamina',min(100,s.stamina+5)), setattr(s,'mood',min(100,s.mood+20)), setattr(s,'charm',s.charm+3), s.gain_exp(3))),
        "燕麦拿铁": (20, lambda s: (setattr(s,'satiety',min(100,s.satiety+15)), setattr(s,'stamina',min(100,s.stamina+8)), setattr(s,'mood',min(100,s.mood+25)), s.gain_exp(3))),
        "气泡冷萃": (15, lambda s: (setattr(s,'satiety',min(100,s.satiety+5)), setattr(s,'stamina',min(100,s.stamina+20)), setattr(s,'mood',min(100,s.mood+10)), s.gain_exp(3))),
        "三角饭团": (10, lambda s: s.feed(25,3,0)),
        "能量香蕉": (8, lambda s: s.feed(15,8,0)),
    }
    skincare_effect_map = {
        "唇膜": (15, lambda s: (setattr(s,'charm',s.charm+5), setattr(s,'mood',min(100,s.mood+8)))),
        "眼膜": (20, lambda s: (setattr(s,'charm',s.charm+6),)),
        "清洁泥膜": (25, lambda s: (setattr(s,'hygiene',min(100,s.hygiene+30)), setattr(s,'charm',s.charm+8))),
        "补水面膜": (30, lambda s: (setattr(s,'charm',s.charm+10), setattr(s,'mood',min(100,s.mood+8)))),
        "面部刮痧": (35, lambda s: (setattr(s,'charm',s.charm+12), setattr(s,'mood',min(100,s.mood+5)))),
        "精华导入": (40, lambda s: (setattr(s,'hygiene',min(100,s.hygiene+10)), setattr(s,'charm',s.charm+15))),
        "一键精致护理": (60, lambda s: (setattr(s,'hygiene',min(100,s.hygiene+40)), setattr(s,'charm',s.charm+20), setattr(s,'mood',min(100,s.mood+15)))),
        "汗蒸排毒": (45, lambda s: (setattr(s,'hygiene',min(100,s.hygiene+70)), setattr(s,'mood',min(100,s.mood+10)), setattr(s,'charm',s.charm+8))),
        "全身按摩": (50, lambda s: (setattr(s,'stamina',min(100,s.stamina+40)), setattr(s,'mood',min(100,s.mood+30)))),
        "香薰水疗": (60, lambda s: (setattr(s,'hygiene',min(100,s.hygiene+100)), setattr(s,'stamina',min(100,s.stamina+10)), setattr(s,'mood',min(100,s.mood+40)), setattr(s,'charm',s.charm+12))),
    }

    def right_click_menu(self, event):
        menu = tk.Menu(self.pet_win, tearoff=0)
        s = self.state; inv = s.inventory

        feed_menu = tk.Menu(menu, tearoff=0)
        has_food = False
        for name, qty in inv.items():
            if name in self.feed_effect_map and qty > 0:
                dur, func = self.feed_effect_map[name]
                feed_menu.add_command(label=f"{name} (剩余{qty})", command=lambda n=name,d=dur,f=func: self.use_inventory_item(n,d,f))
                has_food = True
        if not has_food: feed_menu.add_command(label="无食物", state="disabled")
        menu.add_cascade(label="🍽️ 喂食", menu=feed_menu)

        sc_menu = tk.Menu(menu, tearoff=0)
        has_skincare = False
        for name, qty in inv.items():
            if name in self.skincare_effect_map and qty > 0:
                dur, func = self.skincare_effect_map[name]
                sc_menu.add_command(label=f"{name} (剩余{qty})", command=lambda n=name,d=dur,f=func: self.use_inventory_item(n,d,f))
                has_skincare = True
        if not has_skincare: sc_menu.add_command(label="无护肤用品", state="disabled")
        menu.add_cascade(label="✨ 洁护管理", menu=sc_menu)

        basic_menu = tk.Menu(menu, tearoff=0)
        basic_menu.add_command(label="🧴 洗手消毒 (免费)", command=lambda: self.start_activity("洗手消毒",0,5,lambda s: setattr(s,'hygiene',min(100,s.hygiene+15))))
        basic_menu.add_command(label="🧽 快速洗脸 (免费)", command=lambda: self.start_activity("快速洗脸",0,8,lambda s: setattr(s,'hygiene',min(100,s.hygiene+25))))
        basic_menu.add_command(label="🪥 刷牙 (免费)", command=lambda: self.start_activity("刷牙",0,10,lambda s: (setattr(s,'hygiene',min(100,s.hygiene+20)), setattr(s,'charm',s.charm+3))))
        if inv.get("湿巾",0) > 0:
            basic_menu.add_command(label=f"🧻 湿巾擦拭 (剩余{inv['湿巾']})", command=lambda: self.use_inventory_item("湿巾",12,lambda s: setattr(s,'hygiene',min(100,s.hygiene+40))))
        else:
            basic_menu.add_command(label="🧻 湿巾擦拭 (无库存)", state="disabled")
        basic_menu.add_command(label="🚿 快速淋浴 (免费)", command=lambda: self.start_activity("快速淋浴",0,20,lambda s: (setattr(s,'hygiene',min(100,s.hygiene+80)), setattr(s,'stamina',min(100,s.stamina+5)), setattr(s,'mood',min(100,s.mood+5)))))
        basic_menu.add_command(label="🛁 泡澡 (免费)", command=lambda: self.start_activity("泡澡",0,50,lambda s: (setattr(s,'hygiene',min(100,s.hygiene+100)), setattr(s,'stamina',min(100,s.stamina+10)), setattr(s,'mood',min(100,s.mood+20)))))
        menu.add_cascade(label="🧼 基础清洁", menu=basic_menu)

        if s.stage == 1:
            work_menu = tk.Menu(menu, tearoff=0)
            work_menu.add_command(label="🏪 便利店兼职 (+20💰)", command=lambda: self.do_part_time_job("便利店兼职"))
            work_menu.add_command(label="☕ 咖啡店打工 (+15💰, ✨+3)", command=lambda: self.do_part_time_job("咖啡店打工"))
            work_menu.add_command(label="📦 快递分拣 (+30💰, ⚡-15)", command=lambda: self.do_part_time_job("快递分拣"))
            menu.add_cascade(label="💼 打工培训", menu=work_menu)

            train_menu = tk.Menu(menu, tearoff=0)
            train_menu.add_command(label="🎤 社区声乐班 (-30💰)", command=lambda: self.buy_training("声乐班"))
            train_menu.add_command(label="💃 街舞入门课 (-30💰)", command=lambda: self.buy_training("街舞课"))
            train_menu.add_command(label="🎭 表演兴趣班 (-30💰)", command=lambda: self.buy_training("表演班"))
            if s.vocal >= 30:
                train_menu.add_command(label="🎤 进阶声乐班 (-60💰)", command=lambda: self.buy_training("进阶声乐"))
            if s.dance >= 30:
                train_menu.add_command(label="💃 进阶舞蹈班 (-60💰)", command=lambda: self.buy_training("进阶舞蹈"))
            menu.add_cascade(label="📚 自费培训", menu=train_menu)

            menu.add_command(label="🎤 街头表演", command=self.street_performance)
            menu.add_separator()
            menu.add_command(label="🏢 主动面试", command=self.start_interview)
        else:
            train_menu = tk.Menu(menu, tearoff=0)
            for label, t in [("🎤 声乐课","voice"),("💃 舞蹈集训","fitness"),("🎭 表演工作坊","expression"),("🏋️ 形体管理","shape")]:
                train_menu.add_command(label=label, command=lambda tp=t: self.start_train(tp))
            menu.add_cascade(label="🏋️ 训练", menu=train_menu)

            if s.stage >= 5:
                menu.add_command(label="📺 接通告", command=self.start_schedule)

            menu.add_command(label="😴 睡觉", command=self.sleep)

        menu.add_command(label="🛒 商店", command=self.open_shop)
        menu.add_command(label="💊 治疗", command=self.cure)
        menu.add_separator()

        zoom_menu = tk.Menu(menu, tearoff=0)
        zoom_menu.add_command(label="小 (1.5x)", command=lambda: self.set_scale(1.5))
        zoom_menu.add_command(label="中 (2.0x)", command=lambda: self.set_scale(2.0))
        zoom_menu.add_command(label="大 (2.5x)", command=lambda: self.set_scale(2.5))
        zoom_menu.add_separator()
        zoom_menu.add_command(label="自定义倍数...", command=self.custom_scale)
        menu.add_cascade(label="🔲 缩放", menu=zoom_menu)

        menu.add_command(label="🎒 背包", command=self.show_inventory)
        if self.state.focus_mode: menu.add_command(label="🍅 结束专注", command=self.toggle_focus)
        else: menu.add_command(label="🍅 开始专注 (25min)", command=self.toggle_focus)
        menu.add_command(label="隐藏到托盘", command=self.hide_pet)
        if get_startup_status(): menu.add_command(label="✔ 开机自启：开", command=self.toggle_startup)
        else: menu.add_command(label="✔ 开机自启：关", command=self.toggle_startup)
        menu.add_command(label="📋 查看状态", command=self.show_status)
        menu.add_command(label="❌ 退出", command=self.quit_app)
        menu.post(event.x_root, event.y_root)

    def custom_scale(self):
        result = simpledialog.askfloat("自定义大小", "输入缩放倍数（例如 1.8）：",
                                       initialvalue=self.state.scale,
                                       minvalue=0.3, maxvalue=5.0)
        if result is not None and result > 0:
            self.show_progress_bar("正在生成新尺寸缓存...")
            self.ensure_cache_for_scale(result, "greet")
            self.ensure_cache_for_scale(result, "idle")
            if hasattr(self, 'progress_win') and self.progress_win:
                self.progress_win.destroy()
            self.set_scale(result)

    def do_part_time_job(self, job):
        s = self.state
        if job == "便利店兼职": s.gold += 20; msg = "完成便利店兼职，金币+20"
        elif job == "咖啡店打工": s.gold += 15; s.charm += 3; msg = "完成咖啡店打工，金币+15，魅力+3"
        elif job == "快递分拣": s.gold += 30; s.stamina = max(0, s.stamina-15); msg = "完成快递分拣，金币+30，体力-15"
        else: return
        self.show_toast(msg); s.gain_exp(5); s.save()

    def buy_training(self, course):
        s = self.state
        cost = 30; gain = 8
        if "进阶" in course: cost = 60; gain = 15
        if s.gold < cost: self.show_info("金币不足"); return
        s.gold -= cost
        if "声乐" in course: s.vocal += gain; msg = f"声乐培训完成，唱功+{gain}"
        if "舞蹈" in course: s.dance += gain; msg = f"舞蹈培训完成，舞蹈+{gain}"
        if "表演" in course: s.acting += gain; msg = f"表演培训完成，演技+{gain}"
        self.show_toast(msg); s.gain_exp(10); s.save()

    def street_performance(self):
        s = self.state
        gain = random.randint(1,5); s.charm += 5
        if random.random() < 0.5: s.vocal += gain; msg = f"街头表演结束，唱功+{gain}"
        else: s.dance += gain; msg = f"街头表演结束，舞蹈+{gain}"
        self.show_toast(msg); s.gain_exp(5); s.save()

    def start_interview(self):
        s = self.state
        total = s.vocal + s.dance + s.charm
        if total >= 90 and s.vocal >= 25 and s.dance >= 25 and s.charm >= 25:
            s.promote(2, "见习练习生 🎓"); self.show_toast("面试通过！成为见习练习生")
        else:
            self.show_info("面试未通过，继续努力吧")
        s.save()

    def show_inventory(self):
        inv = self.state.inventory
        win = tk.Toplevel(self.pet_win); win.title("背包")
        win.geometry("300x400")
        tk.Label(win, text="🎒 背包", font=("微软雅黑",14,"bold")).pack(pady=10)
        if not inv: tk.Label(win, text="背包空空如也").pack()
        else:
            for name, qty in inv.items(): tk.Label(win, text=f"{name} x{qty}", font=("微软雅黑",10)).pack(anchor="w", padx=20, pady=2)

    def use_inventory_item(self, name, duration, effect_func):
        if self.state.inventory.get(name,0) <= 0: self.show_info("背包中没有该物品！"); return
        self.state.inventory[name] -= 1
        if self.state.inventory[name] == 0: del self.state.inventory[name]
        self.show_toast(f"使用 {name}")
        self.start_activity(name, 0, duration, effect_func)

    def start_activity(self, name, price, duration, effect_func):
        s = self.state
        if price > 0 and s.gold < price: self.show_info("金币不足！"); return
        if price > 0: s.gold -= price
        def on_finish():
            effect_func(s)
            self.show_toast(f"✅ {name}完成")
            s.save()
        def on_cancel():
            if price > 0: s.gold += price
            self.show_toast(f"❌ {name}已取消")
            s.save()
        self.current_activity = ActivityWindow(self.pet_win, f"{name}中...", duration, on_finish, on_cancel,
                                               pet_x=self.x, pet_y=self.y, pet_w=self.pet_w, pet_h=self.pet_h)

    def start_train(self, type_):
        ok, msg = self.state.train(type_)
        if not ok: self.show_info(msg); return
        self.performance_win = PerformanceWindow(self.pet_win, self.state, "train", type_,
                                                 callback=self.on_activity_end, pet_x=self.x, pet_y=self.y,
                                                 pet_w=self.pet_w, pet_h=self.pet_h)

    def start_schedule(self):
        ok, msg = self.state.do_schedule()
        if not ok: self.show_info(msg); return
        self.performance_win = PerformanceWindow(self.pet_win, self.state, "schedule", "",
                                                 callback=self.on_activity_end, pet_x=self.x, pet_y=self.y,
                                                 pet_w=self.pet_w, pet_h=self.pet_h)

    def on_activity_end(self, msg=None):
        self.performance_win = None
        if msg: self.show_info(msg)
        self.state.save()

    def show_info(self, msg):
        self.pet_win.update_idletasks()
        popup = tk.Toplevel(self.root)
        popup.overrideredirect(True)
        popup.wm_attributes("-topmost", True)
        popup.configure(bg="black")
        tk.Label(popup, text=msg, fg="white", bg="black", font=("微软雅黑", 10)).pack(padx=10, pady=5)
        popup.update_idletasks()
        pet_x = self.pet_win.winfo_x()
        pet_y = self.pet_win.winfo_y()
        popup.geometry(f"+{pet_x + self.pet_w + 5}+{pet_y + 5}")
        self.active_notifications.append(popup)
        def destroy_popup():
            if popup in self.active_notifications:
                self.active_notifications.remove(popup)
            popup.destroy()
        popup.after(2000, destroy_popup)

    def show_toast(self, msg, duration=1500):
        if hasattr(self, 'toast_win') and self.toast_win and self.toast_win.winfo_exists():
            self.toast_win.destroy()
        self.pet_win.update_idletasks()
        toast = tk.Toplevel(self.root)
        toast.overrideredirect(True)
        toast.wm_attributes("-topmost", True)
        toast.wm_attributes("-alpha", 0.85)
        toast.configure(bg="#333333")
        tk.Label(toast, text=msg, fg="white", bg="#333333", font=("微软雅黑", 9, "bold"), padx=8, pady=2).pack()
        toast.update_idletasks()
        pet_x = self.pet_win.winfo_x()
        pet_y = self.pet_win.winfo_y()
        toast.geometry(f"+{pet_x + self.pet_w + 5}+{pet_y + 5}")
        self.active_notifications.append(toast)
        def destroy_toast():
            if toast in self.active_notifications:
                self.active_notifications.remove(toast)
            toast.destroy()
        toast.after(duration, destroy_toast)
        self.toast_win = toast

    def move_notifications(self):
        for popup in self.active_notifications[:]:
            try:
                if popup.winfo_exists():
                    pet_x = self.pet_win.winfo_x()
                    pet_y = self.pet_win.winfo_y()
                    popup.geometry(f"+{pet_x + self.pet_w + 5}+{pet_y + 5}")
            except:
                if popup in self.active_notifications:
                    self.active_notifications.remove(popup)

    def show_danmu(self):
        s = self.state; pool = []
        if s.stage>=3: pool+=["昨天梦到拿一位了…","记得给妈妈打电话","舞台上的灯光好美"]
        if s.mood>70: pool+=["今天心情真好！","感觉状态超级棒！"]
        elif s.mood<30: pool+=["好难过…","不想训练…"]
        if s.fatigue>60: pool+=["好累…","今晚一定要早点睡"]
        if s.satiety<30: pool+=["好饿…","想吃炸鸡"]
        pool+=["想喝奶茶…","今天状态不错！","再练一遍","我会出道的吧？","想家了…"]
        text = random.choice(pool) if pool else "加油！"
        if self.danmu_win and self.danmu_win.winfo_exists(): self.danmu_win.destroy()
        danmu = tk.Toplevel(self.pet_win); danmu.overrideredirect(True); danmu.wm_attributes("-topmost",True)
        danmu.wm_attributes("-alpha",0.8); danmu.configure(bg="black")
        sx = self.x+self.pet_w//2; sy = self.y-10; danmu.geometry(f"+{sx}+{sy}")
        tk.Label(danmu, text=text, fg="white", bg="black", font=("微软雅黑",9), padx=5, pady=2).pack()
        self.danmu_win = danmu; self.animate_danmu(sx,sy)

    def animate_danmu(self, x, y, step=0):
        if step>40 or not self.danmu_win or not self.danmu_win.winfo_exists():
            if self.danmu_win: self.danmu_win.destroy(); self.danmu_win = None
            return
        x-=2; y-=1; self.danmu_win.geometry(f"+{x}+{y}")
        if step>20: self.danmu_win.wm_attributes("-alpha", max(0.2, 0.8-(step-20)*0.03))
        self.root.after(100, lambda: self.animate_danmu(x,y,step+1))

    def companion_loop(self):
        s = self.state; now = time.time(); idle = ActivityMonitor.get_idle_seconds(); s.idle_time = idle
        s.total_playtime += 1
        gt = s.game_time
        if gt.week > s.last_milestone_week:
            s.last_milestone_week = gt.week; self.show_toast(f"🎉 第{gt.week}周纪念！一起加油哦！",3000)
        if gt.day > s.last_milestone_day and gt.day % 100 == 0:
            s.last_milestone_day = gt.day; self.show_toast(f"🎈 一起走过{gt.day}天！",3000)
        if s.focus_mode and now > s.focus_end_time:
            s.focus_mode = False; self.show_toast("🍅 专注时间结束！",3000)
        if not s.focus_mode and not s.resting:
            if idle > s.idle_threshold: self.show_toast("💺 坐太久啦，起来活动一下！"); s.idle_time=0
            if now - s.last_water_reminder > s.water_interval: self.show_toast("💧 喝点水吧～"); s.last_water_reminder=now
            if now - s.last_eye_reminder > s.eye_interval: self.show_toast("👀 休息一下眼睛哦"); s.last_eye_reminder=now
        if not s.focus_mode and now - s.last_danmu_time > s.danmu_interval:
            self.show_danmu(); s.last_danmu_time = now; s.danmu_interval = random.randint(120,300)
        self.check_daytime_greeting(now)
        self.root.after(1000, self.companion_loop)

    def check_daytime_greeting(self, now):
        s = self.state; local = time.localtime(now); hour = local.tm_hour
        if not hasattr(s,'_last_greeting_day'): s._last_greeting_day=0; s._greeted_morning=False; s._greeted_night=False
        if s._last_greeting_day != local.tm_yday:
            s._last_greeting_day = local.tm_yday; s._greeted_morning=False; s._greeted_night=False
        if not s._greeted_morning and 6 <= hour <= 9: self.show_toast("☀️ 早上好！今天也要加油哦！",3000); s._greeted_morning=True
        elif not s._greeted_night and 22 <= hour <= 23: self.show_toast("🌙 晚安，早点休息～",3000); s._greeted_night=True
        elif not s._greeted_night and hour >= 2: self.show_toast("😟 还不休息吗？",3000); s._greeted_night=True

    def sleep(self): self.state.sleep(40); self.state.save()
    def cure(self): self.state.cure(); self.state.save()

    def open_shop(self):
        if self.shop_win and self.shop_win.win.winfo_exists(): self.shop_win.win.lift(); return
        self.shop_win = ShopWindow(self.pet_win, self.state)

    def show_status(self):
        win = StatusWindow(self.pet_win, self.state)
        win.win.geometry(f"+{self.x+self.pet_w+10}+{self.y}")

    def toggle_focus(self):
        s = self.state
        if not s.focus_mode: s.focus_mode=True; s.focus_end_time=time.time()+s.focus_duration; self.show_toast("🍅 专注模式开始",2000)
        else: s.focus_mode=False; self.show_toast("专注模式已结束",2000)
        s.save()

    def toggle_startup(self):
        if get_startup_status(): set_startup(False); self.show_toast("开机自启已关闭")
        else: set_startup(True); self.show_toast("开机自启已开启")

    def show_pet(self, *args): self.pet_win.deiconify(); self.pet_win.lift()
    def hide_pet(self, *args): self.pet_win.withdraw()

    def create_tray(self):
        img = Image.new("RGBA",(64,64),(0,0,0,0)); draw = ImageDraw.Draw(img)
        draw.ellipse((8,8,56,56),fill="#8B5CF6"); draw.ellipse((22,22,30,30),fill="white")
        draw.ellipse((34,22,42,30),fill="white"); draw.arc((22,34,42,44),start=0,end=180,fill="white",width=2)
        menu = pystray.Menu(
            pystray.MenuItem("显示宠物", self.show_pet, default=True),
            pystray.MenuItem("专注模式", self.toggle_focus),
            pystray.MenuItem("开机自启", self.toggle_startup, checked=lambda item: get_startup_status()),
            pystray.MenuItem("退出", self.quit_app)
        )
        self.tray = pystray.Icon("pet", img, "练习生", menu)

    def decay_timer(self):
        self.state.decay(); self.root.after(15000, self.decay_timer)

    def start_drag(self, event): self.drag_data["x"]=event.x; self.drag_data["y"]=event.y

    def on_drag(self, event):
        dx=event.x-self.drag_data["x"]; dy=event.y-self.drag_data["y"]
        self.x+=dx; self.y+=dy; self.pet_win.geometry(f"+{self.x}+{self.y}")
        if self.performance_win: self.performance_win.move_to(self.x, self.y)
        if self.current_activity:
            self.current_activity.pos_x = self.x + (self.pet_w-280)//2; self.current_activity.pos_y = self.y+self.pet_h+10
            self.current_activity.win.geometry(f"+{self.current_activity.pos_x}+{self.current_activity.pos_y}")
        self.move_notifications()

    def auto_save_loop(self):
        self.state.save(); self.root.after(30000, self.auto_save_loop)

    def quit_app(self, *args):
        self.state.save()
        if self.tray: self.tray.stop()
        self.bubble_win.destroy(); self.pet_win.destroy(); self.root.destroy()

    def run(self): self.root.mainloop()
        
# ==================== 防多开 ====================
def check_single_instance():
    try:
        mutex = ctypes.windll.kernel32.CreateMutexW(None, True, "DesktopPet_Mutex")
        if ctypes.windll.kernel32.GetLastError() == 183: return False
        return True
    except: return True

if __name__ == "__main__":
    if not check_single_instance():
        import tkinter.messagebox
        tk.messagebox.showwarning("已运行", "练习生桌面宠物已经在运行中，不能重复打开。"); sys.exit(0)
    pet = DesktopPet(image_folder=resource_path("pet_frames"))
    pet.run()
