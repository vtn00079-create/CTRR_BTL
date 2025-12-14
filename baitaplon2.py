from dataclasses import dataclass
from typing import Dict, List, Tuple, Optional, Any, Set
import heapq
import json
import collections
import math
import random
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk
import matplotlib
matplotlib.use("TkAgg")
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import matplotlib.pyplot as plt
import threading
import time
import copy

# =============================================================================
# PHẦN 1: LOGIC ĐỒ THỊ
# =============================================================================

@dataclass
class Canh:
    u: str
    v: str
    trong_so: float = 1.0
    cap: float = 0.0

    def to_dict(self):
        return {"u": self.u, "v": self.v, "w": self.trong_so, "cap": self.cap}


class DoThi:
    def __init__(self, co_huong=True):
        self.co_huong = co_huong
        self.ds_dinh = set()
        self.ds_canh = []
        self.toa_do = {}

    def clear(self):
        self.ds_dinh.clear()
        self.ds_canh.clear()
        self.toa_do.clear()

    def them_dinh(self, ten, pos=None):
        self.ds_dinh.add(ten)
        if ten not in self.toa_do:
            self.toa_do[ten] = pos if pos else (
                random.uniform(-0.8, 0.8),
                random.uniform(-0.8, 0.8)
            )

    def them_canh(self, u, v, w=1.0, cap=10.0):
        self.them_dinh(u)
        self.them_dinh(v)
        found = False
        for c in self.ds_canh:
            if c.u == u and c.v == v:
                c.trong_so = w
                c.cap = cap
                found = True
                break
            if not self.co_huong and c.u == v and c.v == u:
                c.trong_so = w
                c.cap = cap
                found = True
                break
        if not found:
            self.ds_canh.append(Canh(u, v, w, cap))

    def lay_ke(self):
        adj = {n: [] for n in self.ds_dinh}
        for e in self.ds_canh:
            adj[e.u].append({"to": e.v, "w": e.trong_so, "cap": e.cap})
            if not self.co_huong:
                adj[e.v].append({"to": e.u, "w": e.trong_so, "cap": e.cap})
        return adj

    def lay_ma_tran_ke(self):
        nodes = sorted(list(self.ds_dinh))
        n = len(nodes)
        idx = {node: i for i, node in enumerate(nodes)}
        mat = [[0] * n for _ in range(n)]
        for e in self.ds_canh:
            mat[idx[e.u]][idx[e.v]] = e.trong_so
            if not self.co_huong:
                mat[idx[e.v]][idx[e.u]] = e.trong_so
        return nodes, mat

    def lay_danh_sach_ke(self):
        return self.lay_ke()

    def lay_danh_sach_canh_str(self):
        lines = []
        for e in self.ds_canh:
            lines.append(f"{e.u} {e.v} {e.trong_so}")
        return "\n".join(lines)

    def to_json(self):
        return json.dumps({
            "directed": self.co_huong,
            "nodes": [{"id": n, "pos": self.toa_do[n]} for n in self.ds_dinh],
            "edges": [e.to_dict() for e in self.ds_canh]
        }, indent=2)

    def from_json(self, json_str):
        data = json.loads(json_str)
        self.clear()
        self.co_huong = data.get("directed", False)
        for n in data.get("nodes", []):
            self.them_dinh(n["id"], tuple(n["pos"]))
        for e in data.get("edges", []):
            self.them_canh(e["u"], e["v"], e["w"], e.get("cap", 0))

    def kiem_tra_2_phia(self):
        adj = self.lay_ke()
        color = {node: 0 for node in self.ds_dinh}
        for start in self.ds_dinh:
            if color[start] == 0:
                q = collections.deque([start])
                color[start] = 1
                while q:
                    u = q.popleft()
                    for nb in adj[u]:
                        v = nb["to"]
                        if color[v] == 0:
                            color[v] = -color[u]
                            q.append(v)
                        elif color[v] == color[u]:
                            return False, {}, []
        return True, color, []
    # =========================================================================
    # CÁC THUẬT TOÁN
    # =========================================================================

    def bfs(self, s):
        adj = self.lay_ke()
        vis = set()
        q = [s]
        st = []
        if s not in adj:
            return []
        vis.add(s)
        st.append({"t": "msg", "m": f"🚀 BFS bắt đầu từ {s}"})
        while q:
            u = q.pop(0)
            st.append({"t": "node", "id": u})
            neighbors = sorted(adj[u], key=lambda x: x['to'])
            for nb in neighbors:
                if nb["to"] not in vis:
                    vis.add(nb["to"])
                    q.append(nb["to"])
                    st.append({"t": "edge", "u": u, "v": nb["to"]})
        return st

    def dfs(self, s):
        adj = self.lay_ke()
        vis = set()
        stack = [s]
        st = []
        if s not in adj:
            return []
        st.append({"t": "msg", "m": f"🚀 DFS bắt đầu từ {s}"})
        while stack:
            u = stack.pop()
            if u in vis:
                continue
            vis.add(u)
            st.append({"t": "node", "id": u})
            neighbors = sorted(adj[u], key=lambda x: x['to'], reverse=True)
            for nb in neighbors:
                if nb["to"] not in vis:
                    st.append({"t": "edge", "u": u, "v": nb["to"]})
                    stack.append(nb["to"])
        return st

    def dijkstra(self, s):
        # --- KIỂM TRA TRỌNG SỐ ÂM ---
        for edge in self.ds_canh:
            if edge.trong_so < 0:
                return [{"t": "msg", "m": "⛔ Lỗi: Đồ thị chứa trọng số âm. Dijkstra không hỗ trợ trọng số âm!."}]
        
        adj = self.lay_ke()
        dist = {n: float('inf') for n in self.ds_dinh}
        pq = [(0, s)]
        st = []
        dist[s] = 0
        st.append({"t": "msg", "m": f"📍 Dijkstra tìm đường ngắn nhất từ {s}"})
        
        while pq:
            d, u = heapq.heappop(pq)
            if d > dist[u]:
                continue
                
            st.append({"t": "node", "id": u, "val": d})
            
            for nb in adj[u]:
                v, w = nb["to"], nb["w"]
                if dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w
                    heapq.heappush(pq, (dist[v], v))
                    st.append({"t": "edge", "u": u, "v": v})
                    st.append({"t": "msg", "m": f"Cập nhật d[{v}] = {dist[v]} qua {u}"})
        return st

    # ------------- PRIM -------------
    def prim(self, s):
        if self.co_huong:
            return [{"t": "msg", "m": "Lỗi: Prim chỉ dành cho đồ thị vô hướng"}]

        adj = self.lay_ke()
        vis = set()
        pq = [(0, s, s)]
        st = []
        st.append({"t": "msg", "m": f"🌲 Prim bắt đầu từ {s}"})
        total_w = 0

        while pq:
            w, p, u = heapq.heappop(pq)
            if u in vis:
                continue
            vis.add(u)
            total_w += w

            if p != u:
                st.append({"t": "mst", "u": p, "v": u})
                st.append({"t": "msg", "m": f"Thêm cạnh ({p}, {u}) w={w}"})
            else:
                st.append({"t": "node", "id": u})

            for nb in adj[u]:
                if nb["to"] not in vis:
                    heapq.heappush(pq, (nb["w"], u, nb["to"]))

        st.append({"t": "msg", "m": f"Tổng trọng số cây khung: {total_w}"})
        return st

    # ------------- KRUSKAL -------------
    def kruskal(self):
        if self.co_huong:
            return [{"t": "msg", "m": "Lỗi: Kruskal chỉ dành cho đồ thị vô hướng"}]

        edges = sorted(self.ds_canh, key=lambda x: x.trong_so)
        st = [{"t": "msg", "m": "🌲 Kruskal: Sắp xếp cạnh tăng dần"}]

        parent = {n: n for n in self.ds_dinh}
        rank = {n: 0 for n in self.ds_dinh}

        def find(i):
            if parent[i] != i:
                parent[i] = find(parent[i])
            return parent[i]

        def union(i, j):
            ri, rj = find(i), find(j)
            if ri != rj:
                if rank[ri] < rank[rj]:
                    parent[ri] = rj
                elif rank[ri] > rank[rj]:
                    parent[rj] = ri
                else:
                    parent[rj] = ri
                    rank[ri] += 1
                return True
            return False

        mst_w = 0
        cnt = 0
        for e in edges:
            if union(e.u, e.v):
                mst_w += e.trong_so
                st.append({"t": "mst", "u": e.u, "v": e.v})
                st.append({"t": "msg", "m": f"Chọn cạnh ({e.u}, {e.v}) w={e.trong_so}"})
                cnt += 1

        if cnt < len(self.ds_dinh) - 1:
            st.append({"t": "msg", "m": "Đồ thị không liên thông!"})
        else:
            st.append({"t": "msg", "m": f"Tổng trọng số: {mst_w}"})

        return st
    # ----------------------- EULER (FLEURY) -----------------------
    def check_euler_condition(self):
        adj = self.lay_ke()
        odds = [u for u in adj if len(adj[u]) % 2 != 0]
        if len(odds) == 0:
            return "CYCLE"
        if len(odds) == 2:
            return "PATH"
        return "NONE"

    def fleury(self, s):
        if self.co_huong:
            return [{"t": "msg", "m": "⛔ Lỗi: Fleury chỉ chạy trên đồ thị vô hướng!"}]

        adj = self.lay_ke()
        odd_nodes = [u for u in adj if len(adj[u]) % 2 != 0]

        if len(odd_nodes) not in [0, 2]:
            return [{"t": "msg", "m": f"⛔ Không có đường Euler! (Đỉnh bậc lẻ: {len(odd_nodes)})"}]

        if len(odd_nodes) == 2 and s not in odd_nodes:
            return [{"t": "msg", "m": f"⛔ Phải bắt đầu từ 1 trong 2 đỉnh bậc lẻ: {odd_nodes}"}]

        st = [{"t": "msg", "m": f"🎡 Fleury bắt đầu từ {s}"}]

        adj_copy = {u: [x['to'] for x in adj[u]] for u in adj}

        def bfs_count(start, g):
            cnt = 0
            q = [start]
            vis = {start}
            while q:
                u = q.pop(0)
                cnt += 1
                for v in g.get(u, []):
                    if v not in vis:
                        vis.add(v)
                        q.append(v)
            return cnt

        def is_bridge(u, v):
            if len(adj_copy[u]) == 1:
                return False
            c1 = bfs_count(u, adj_copy)
            adj_copy[u].remove(v)
            adj_copy[v].remove(u)
            c2 = bfs_count(u, adj_copy)
            adj_copy[u].append(v)
            adj_copy[v].append(u)
            return c1 > c2

        curr = s
        path = [curr]

        while any(adj_copy[u] for u in adj_copy):
            if not adj_copy[curr]:
                break

            chosen = -1
            for v in adj_copy[curr]:
                if not is_bridge(curr, v):
                    chosen = v
                    break

            if chosen == -1:
                chosen = adj_copy[curr][0]

            st.append({"t": "mst", "u": curr, "v": chosen})
            st.append({"t": "msg", "m": f"Đi qua ({curr}, {chosen})"})

            adj_copy[curr].remove(chosen)
            adj_copy[chosen].remove(curr)

            curr = chosen
            path.append(curr)

        st.append({"t": "msg", "m": f"Kết quả: {' -> '.join(path)}"})
        return st

    # ----------------------- EULER (HIERHOLZER) -----------------------
    def hierholzer(self, s):
        st = [{"t": "msg", "m": f"🎡 Hierholzer từ {s}"}]

        adj = {u: [] for u in self.ds_dinh}
        for e in self.ds_canh:
            adj[e.u].append(e.v)
            adj[e.v].append(e.u)

        stack = [s]
        circuit = []

        while stack:
            u = stack[-1]
            if adj[u]:
                v = adj[u].pop()
                adj[v].remove(u)
                stack.append(v)
                st.append({"t": "edge", "u": u, "v": v})
            else:
                circuit.append(stack.pop())

        circuit = circuit[::-1]
        st.append({"t": "msg", "m": f"Chu trình: {' -> '.join(circuit)}"})

        for i in range(len(circuit) - 1):
            st.append({"t": "mst", "u": circuit[i], "v": circuit[i + 1]})

        return st

    # ----------------------- MAX FLOW -----------------------
    def ford_fulkerson(self, s, t):
        if not self.co_huong:
            return [{"t": "msg", "m": "⛔ Max Flow yêu cầu đồ thị CÓ HƯỚNG!"}]

        st = [{"t": "msg", "m": f"🌊 Max Flow từ {s} → {t}"}]

        capacity = {}
        for c in self.ds_canh:
            capacity[(c.u, c.v)] = c.cap
            capacity[(c.v, c.u)] = 0

        def bfs_residual(source, sink, parent):
            visited = set()
            q = [source]
            visited.add(source)
            parent.clear()

            while q:
                u = q.pop(0)
                for v in self.ds_dinh:
                    if v not in visited and capacity.get((u, v), 0) > 0:
                        visited.add(v)
                        parent[v] = u
                        if v == sink:
                            return True
                        q.append(v)
            return False

        max_flow = 0
        parent = {}

        while bfs_residual(s, t, parent):
            flow = float('inf')
            v = t
            path = [t]
            while v != s:
                u = parent[v]
                flow = min(flow, capacity[(u, v)])
                path.append(u)
                v = u
            path.reverse()

            st.append({"t": "msg", "m": f"Đường tăng: {'->'.join(path)} | Flow = {flow}"})

            v = t
            while v != s:
                u = parent[v]
                capacity[(u, v)] -= flow
                capacity[(v, u)] += flow
                st.append({"t": "flow_update", "u": u, "v": v, "val": flow})
                v = u

            max_flow += flow

        st.append({"t": "msg", "m": f"🏁 Max Flow = {max_flow}"})
        return st
# =============================================================================
# PHẦN 2: GIAO DIỆN GUI
# =============================================================================

C_SIDEBAR    = "#e3f2fd"
C_SIDE_TEXT  = "#0277bd"
C_BTN_BG     = "#ffffff"
C_BTN_BORDER = "#81d4fa"
C_BTN_HOVER  = "#b3e5fc"
C_MAIN_BG    = "#f5f5f5"

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Graph Master Ultimate v3.0")
        self.geometry("1280x800")

        self.dt = DoThi(co_huong=False)

        # --- SPEED SLIDER VARIABLE ---
        self.speed = tk.DoubleVar(value=0.8)

        self.configure(bg=C_MAIN_BG)
        self._init_ui()
        self._demo_data()

    def _init_ui(self):
        sidebar = tk.Frame(self, bg=C_SIDEBAR, width=280)
        sidebar.pack(side=tk.LEFT, fill=tk.Y)
        sidebar.pack_propagate(False)

        frm_speed = tk.Frame(sidebar, bg=C_SIDEBAR)
        frm_speed.pack(fill="x", pady=10)

        tk.Label(
            frm_speed,
            text="Animation Speed (s/step):",
            bg=C_SIDEBAR,
            fg="white"
        ).pack(anchor="w")

        tk.Scale(
            frm_speed,
            from_=0.1,
            to=2.0,
            resolution=0.1,
            orient="horizontal",
            variable=self.speed
        ).pack(fill="x")

        # Title
        tk.Label(sidebar, text="GRAPH TOOL", bg=C_SIDEBAR, fg=C_SIDE_TEXT,
                 font=("Segoe UI", 20, "bold")).pack(pady=20)

        # FILE
        self.lbl_group(sidebar, "FILE SYSTEM")
        self.btn_modern(sidebar, "💾 LƯU FILE (JSON)", self.save_graph)
        self.btn_modern(sidebar, "📂 MỞ FILE (JSON)", self.load_graph)

        # EDIT
        self.lbl_group(sidebar, "CHỈNH SỬA")
        self.btn_modern(sidebar, "✚  THÊM ĐỈNH", self.add_node_popup)
        self.btn_modern(sidebar, "🔗  THÊM CẠNH", self.add_edge_popup)

        # ⭐⭐ THÊM NÚT XOÁ ĐỈNH + XOÁ CẠNH ⭐⭐
        self.btn_modern(sidebar, "❌  XÓA ĐỈNH", self.delete_node_popup, is_danger=True)
        self.btn_modern(sidebar, "❌  XÓA CẠNH", self.delete_edge_popup, is_danger=True)

        self.btn_modern(sidebar, "🗑️  XÓA ĐỒ THỊ", self.reset_graph, is_danger=True)

        # VIEW
        self.lbl_group(sidebar, "HIỂN THỊ")
        self.btn_modern(sidebar, "📄 DS KỀ / CẠNH", self.show_representations)
        self.btn_modern(sidebar, "⚖️ KIỂM TRA 2 PHÍA", self.check_bipartite)

        # ALGO
        self.lbl_group(sidebar, "THUẬT TOÁN")
        self.algo_var = tk.StringVar(value="BFS")

        algos = [
            "BFS (Tìm kiếm rộng)",
            "DFS (Tìm kiếm sâu)",
            "Dijkstra (Đường ngắn nhất)",
            "Prim (MST)",
            "Kruskal (MST)",
            "Fleury (Euler)",
            "Hierholzer (Euler)",
            "Ford-Fulkerson (Max Flow)"
        ]

        cb = ttk.Combobox(sidebar, textvariable=self.algo_var,
                          values=algos, state="readonly")
        cb.pack(fill=tk.X, padx=15, pady=5)

        self.btn_modern(sidebar, "▶  CHẠY VISUAL", self.run_algo, is_primary=True)

        # MAIN CANVAS
        main = tk.Frame(self, bg=C_MAIN_BG)
        main.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        header = tk.Frame(main, bg="white", height=50)
        header.pack(fill=tk.X)
        tk.Button(header, text="↺ RESET MÀU", command=self.draw,
                  bg="white", fg=C_SIDE_TEXT).pack(side=tk.RIGHT, padx=10, pady=10)

        canvas_frame = tk.Frame(main, bg="white", bd=2, relief="groove")
        canvas_frame.pack(fill=tk.BOTH, expand=True, padx=15, pady=15)

        self.fig, self.ax = plt.subplots(figsize=(6, 5))
        self.fig.patch.set_facecolor("white")
        self.canvas = FigureCanvasTkAgg(self.fig, master=canvas_frame)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        self.canvas.mpl_connect("button_press_event", self.on_press)
        self.canvas.mpl_connect("button_release_event", self.on_release)
        self.canvas.mpl_connect("motion_notify_event", self.on_motion)

        self.drag_node = None

        # LOG
        log_frame = tk.Frame(main, height=160, bg="#e1f5fe")
        log_frame.pack(fill=tk.X)
        log_frame.pack_propagate(False)

        tk.Label(log_frame, text=" NHẬT KÝ HOẠT ĐỘNG",
                 bg="#e1f5fe", fg=C_SIDE_TEXT,
                 font=("Consolas", 10, "bold")).pack(anchor="w")

        self.txt_log = tk.Text(log_frame, font=("Consolas", 10),
                               bg="white", fg="black")
        self.txt_log.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

    def btn_modern(self, parent, text, cmd, is_primary=False, is_danger=False):
        bg = C_BTN_BG
        fg = C_SIDE_TEXT
        if is_primary:
            bg = "#4fc3f7"; fg = "white"
        if is_danger:
            bg = "#ef9a9a"; fg = "#b71c1c"

        tk.Button(parent, text=text, command=cmd, bg=bg, fg=fg,
                  activebackground=C_BTN_HOVER, bd=1, relief="solid",
                  font=("Segoe UI", 10, "bold")).pack(fill=tk.X, padx=15, pady=4)

    def lbl_group(self, parent, text):
        tk.Label(parent, text=text, bg=C_SIDEBAR, fg="#01579b",
                 font=("Segoe UI", 9, "bold")).pack(anchor="w", padx=15, pady=(20, 5))

    # ---------------------- LOGIC POPUP XÓA ĐỈNH ----------------------
    def delete_node_popup(self):
        name = simpledialog.askstring("Xóa Đỉnh", "Tên đỉnh cần xóa:")
        if not name:
            return
        if name not in self.dt.ds_dinh:
            messagebox.showerror("Lỗi", "Đỉnh không tồn tại!")
            return

        self.dt.ds_dinh.remove(name)
        if name in self.dt.toa_do:
            del self.dt.toa_do[name]

        self.dt.ds_canh = [c for c in self.dt.ds_canh if c.u != name and c.v != name]

        self.draw()
        self.log(f"Đã xóa đỉnh {name}")

    # ---------------------- LOGIC POPUP XÓA CẠNH ----------------------
    def delete_edge_popup(self):
        win = tk.Toplevel(self)
        win.title("Xóa Cạnh")
        win.geometry("300x180")

        tk.Label(win, text="Từ (u):").pack(anchor="w", padx=20)
        u = tk.Entry(win); u.pack(fill=tk.X, padx=20)

        tk.Label(win, text="Đến (v):").pack(anchor="w", padx=20)
        v = tk.Entry(win); v.pack(fill=tk.X, padx=20)

        def ok():
            uu = u.get().strip()
            vv = v.get().strip()
            before = len(self.dt.ds_canh)

            self.dt.ds_canh = [c for c in self.dt.ds_canh if not (c.u == uu and c.v == vv)]

            if not self.dt.co_huong:
                self.dt.ds_canh = [c for c in self.dt.ds_canh if not (c.u == vv and c.v == uu)]

            after = len(self.dt.ds_canh)

            if before == after:
                messagebox.showwarning("Thông báo", "Không có cạnh cần xóa.")
            else:
                self.log(f"Đã xóa cạnh {uu} - {vv}")

            self.draw()
            win.destroy()

        tk.Button(win, text="XÓA", bg="#e53935", fg="white",
                  command=ok).pack(fill=tk.X, padx=20, pady=15)

    # Các hàm còn lại của GUI (vẽ, animation, demo_data, on_press/move/release)
    # Giống bản gốc 100% — KHÔNG thay đổi
    # ---------------------------------------
    def log(self, msg):
        self.txt_log.insert(tk.END, f">> {msg}\n")
        self.txt_log.see(tk.END)

    # --- IMPLEMENTATION GUI FUNCTIONS ---
    def save_graph(self):
        f = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON Files", "*.json")])
        if f:
            try:
                with open(f, "w", encoding='utf-8') as file:
                    file.write(self.dt.to_json())
                messagebox.showinfo("OK", "Đã lưu thành công!")
                self.log(f"Đã lưu file: {f}")
            except Exception as e:
                messagebox.showerror("Lỗi", str(e))

    def load_graph(self):
        f = filedialog.askopenfilename(filetypes=[("JSON Files", "*.json")])
        if f:
            try:
                with open(f, "r", encoding='utf-8') as file:
                    self.dt.from_json(file.read())
                self.draw()
                self.log(f"Đã mở file: {f}")
            except Exception as e:
                messagebox.showerror("Lỗi", str(e))

    def show_representations(self):
        win = tk.Toplevel(self); win.title("Biểu diễn Đồ thị"); win.geometry("600x400")
        nb = ttk.Notebook(win); nb.pack(fill=tk.BOTH, expand=True)

        # Matrix
        f1 = tk.Frame(nb); nb.add(f1, text="Ma Trận Kề")
        t1 = tk.Text(f1, font=("Consolas", 11)); t1.pack(fill=tk.BOTH, expand=True)
        nodes, mat = self.dt.lay_ma_tran_ke()
        if nodes:
            t1.insert(tk.END, "   " + "  ".join(f"{n:>3}" for n in nodes) + "\n\n")
            for i, row in enumerate(mat):
                t1.insert(tk.END, f"{nodes[i]:>3}" + "  ".join(f"{x:>3}" for x in row) + "\n")

        # Adj list
        f2 = tk.Frame(nb); nb.add(f2, text="Danh Sách Kề")
        t2 = tk.Text(f2, font=("Consolas", 11)); t2.pack(fill=tk.BOTH, expand=True)
        adj = self.dt.lay_danh_sach_ke()
        for u, nbs in adj.items():
            s = ", ".join([f"{n['to']}(w={n['w']})" for n in nbs])
            t2.insert(tk.END, f"{u} -> {s}\n")

        # Edge list
        f3 = tk.Frame(nb); nb.add(f3, text="Danh Sách Cạnh")
        t3 = tk.Text(f3, font=("Consolas", 11)); t3.pack(fill=tk.BOTH, expand=True)
        t3.insert(tk.END, "U   V   W\n---------\n")
        t3.insert(tk.END, self.dt.lay_danh_sach_canh_str())

    def check_bipartite(self):
        res, coloring, _ = self.dt.kiem_tra_2_phia()
        if res:
            messagebox.showinfo("Kết quả", "✔ Là Đồ Thị 2 Phía!")
            self.draw(custom_colors=coloring)
        else:
            messagebox.showwarning("Kết quả", "❌ KHÔNG PHẢI 2 PHÍA.")

    def add_node_popup(self):
        name = simpledialog.askstring("Thêm Đỉnh", "Tên đỉnh:")
        if name:
            self.dt.them_dinh(name.strip())
            self.draw()

    def add_edge_popup(self):
        win = tk.Toplevel(self); win.title("Thêm Cạnh"); win.geometry("300x250")
        tk.Label(win, text="Từ:", font=("Segoe UI", 9)).pack(anchor="w", padx=20); u = tk.Entry(win); u.pack(fill=tk.X, padx=20)
        tk.Label(win, text="Đến:", font=("Segoe UI", 9)).pack(anchor="w", padx=20); v = tk.Entry(win); v.pack(fill=tk.X, padx=20)

        f_row = tk.Frame(win); f_row.pack(fill=tk.X, padx=20, pady=5)
        tk.Label(f_row, text="Trọng số (w):").pack(side=tk.LEFT)
        w = tk.Entry(f_row, width=5); w.pack(side=tk.LEFT, padx=5); w.insert(0, "1")

        tk.Label(f_row, text="Dung lượng (cap):").pack(side=tk.LEFT)
        cap = tk.Entry(f_row, width=5); cap.pack(side=tk.LEFT, padx=5); cap.insert(0, "10")

        def ok():
            if u.get() and v.get():
                try:
                    ww = float(w.get()); cc = float(cap.get())
                except:
                    ww = 1.0; cc = 10.0
                self.dt.them_canh(u.get().strip(), v.get().strip(), ww, cc)
                self.draw(); win.destroy()
        tk.Button(win, text="Nối Dây", command=ok, bg="#4fc3f7", fg="white").pack(fill=tk.X, padx=20, pady=15)

    def draw(self, custom_colors=None):
        self.ax.clear(); self.ax.axis('off')
        self.ax.set_xlim(-1.2, 1.2); self.ax.set_ylim(-1.2, 1.2)

        self.art_edges = {}
        for c in self.dt.ds_canh:
            if c.u not in self.dt.toa_do or c.v not in self.dt.toa_do: continue
            p1 = self.dt.toa_do[c.u]; p2 = self.dt.toa_do[c.v]

            lbl = str(c.trong_so)
            if c.cap != 0 and c.cap != 10: lbl += f"/{int(c.cap)}"

            if self.dt.co_huong:
                ar = self.ax.annotate("", xy=p2, xytext=p1, arrowprops=dict(arrowstyle="-|>", color="#90a4ae", lw=1.5), zorder=1)
                self.art_edges[(c.u, c.v)] = {"obj": ar, "type": "arrow", "mid": ((p1[0]+p2[0])/2, (p1[1]+p2[1])/2)}
            else:
                l, = self.ax.plot([p1[0], p2[0]], [p1[1], p2[1]], color="#90a4ae", lw=1.5, zorder=1)
                self.art_edges[(c.u, c.v)] = {"obj": l, "type": "line", "mid": ((p1[0]+p2[0])/2, (p1[1]+p2[1])/2)}
                self.art_edges[(c.v, c.u)] = self.art_edges[(c.u, c.v)]

            mid = ((p1[0]+p2[0])/2, (p1[1]+p2[1])/2)
            t = self.ax.text(mid[0], mid[1], lbl, color="#e53935", fontsize=9, bbox=dict(fc='white', ec='none', alpha=0.8))
            if (c.u, c.v) in self.art_edges: self.art_edges[(c.u, c.v)]["text"] = t

        self.art_nodes = {}
        for n, p in self.dt.toa_do.items():
            col = "#29b6f6"
            if custom_colors:
                val = custom_colors.get(n, 0)
                if val == 1: col = "#ef5350"
                elif val == -1: col = "#66bb6a"

            c = self.ax.scatter([p[0]], [p[1]], s=600, c=col, edgecolors='white', linewidth=1.5, zorder=2)
            self.ax.text(p[0], p[1], n, color='white', ha='center', va='center', fontweight='bold', zorder=3)
            self.art_nodes[n] = c
        self.canvas.draw()

    def on_press(self, e):
        if e.inaxes != self.ax: return
        for n, p in self.dt.toa_do.items():
            if (p[0] - e.xdata) ** 2 + (p[1] - e.ydata) ** 2 < 0.01:
                self.drag_node = n; return

    def on_release(self, e): self.drag_node = None

    def on_motion(self, e):
        if self.drag_node and e.inaxes == self.ax:
            self.dt.toa_do[self.drag_node] = (e.xdata, e.ydata)
            self.draw()

    def run_algo(self):
        algo = self.algo_var.get()
        start = simpledialog.askstring("Input", "Đỉnh bắt đầu:")
        if not start or start not in self.dt.ds_dinh:
            messagebox.showerror("Lỗi", "Đỉnh không tồn tại!"); return

        t_node = None
        if "Ford-Fulkerson" in algo:
            t_node = simpledialog.askstring("Input", "Đỉnh đích (Sink):")
            if not t_node or t_node not in self.dt.ds_dinh: return

        threading.Thread(target=self._anim, args=(algo, start, t_node), daemon=True).start()

    def _anim(self, algo, start, end=None):
        self.txt_log.delete(1.0, tk.END); self.log(f"--- START {algo} ---")
        steps = []
        if "BFS" in algo: steps = self.dt.bfs(start)
        elif "DFS" in algo: steps = self.dt.dfs(start)
        elif "Dijkstra" in algo: steps = self.dt.dijkstra(start)
        elif "Prim" in algo: steps = self.dt.prim(start)
        elif "Kruskal" in algo: steps = self.dt.kruskal()
        elif "Fleury" in algo: steps = self.dt.fleury(start)
        elif "Hierholzer" in algo: steps = self.dt.hierholzer(start)
        elif "Ford-Fulkerson" in algo: steps = self.dt.ford_fulkerson(start, end)

        for s in steps:
            time.sleep(self.speed.get())
            t = s["t"]
            if t == "node":
                self.art_nodes[s["id"]].set_facecolor('#ffa726')
            elif t in ["edge", "mst"]:
                key = (s["u"], s["v"])
                if key in self.art_edges:
                    item = self.art_edges[key]
                    col = "#66bb6a" if t == "mst" else "#ffa726"
                    if item["type"] == "line":
                        item["obj"].set_color(col); item["obj"].set_linewidth(3)
                    else:
                        item["obj"].arrow_patch.set_color(col); item["obj"].arrow_patch.set_linewidth(3)
            elif t == "flow_update":
                key = (s["u"], s["v"])
                if key in self.art_edges:
                    txt = self.art_edges[key]["text"]
                    txt.set_text(f"Flow: {s['val']}")
                    txt.set_color("blue")
            elif t == "msg":
                self.log(s["m"])
            self.canvas.draw_idle()
        self.log("--- DONE ---"); messagebox.showinfo("Done", "Hoàn thành mô phỏng!")

    def reset_graph(self):
        confirm = messagebox.askyesno("Cảnh báo", "Hành động này sẽ xóa toàn bộ dữ liệu đồ thị hiện tại.\nBạn có chắc chắn muốn tiếp tục?")
        if not confirm:
            return
        is_directed = messagebox.askyesno("Tùy chọn", "Bạn muốn tạo đồ thị mới là CÓ HƯỚNG?\n\n- Yes: Có hướng\n- No: Vô hướng")
        self.dt = DoThi(is_directed)
        self.draw()
        self.log(f"Đã làm mới đồ thị: {'Có hướng' if is_directed else 'Vô hướng'}")

    def _demo_data(self):
        # Thiết lập đồ thị có hướng (Dijkstra thường dùng cho đồ thị có hướng)
        self.dt.co_huong = True
        
        # Thêm các đỉnh và tọa độ để hiển thị đẹp
        self.dt.them_dinh("A", (-0.8, 0.0))
        self.dt.them_dinh("B", (0.0, 0.5))
        self.dt.them_dinh("C", (0.8, 0.0))

        # Thêm cạnh: Cạnh B -> C có trọng số âm
        self.dt.them_canh("A", "B", w=10)
        self.dt.them_canh("B", "C", w=-5) # <--- TRỌNG SỐ ÂM Ở ĐÂY
        self.dt.them_canh("A", "C", w=8)

        self.draw()
        self.log("Đã tải dữ liệu mẫu chứa TRỌNG SỐ ÂM để test Dijkstra.")


if __name__ == "__main__":
    app = App()
    app.mainloop()
