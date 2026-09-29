# -*- coding: utf-8 -*-
"""表格长度优化：给飞书文档和 Markdown 里的每张表，在「表格宽度」和「表格高度」之间选最优比。

不是把表拉满页宽。每张表单独算：
  1. 从每列的下限（表头不折行、短词不拆）起步，把宽度一点点加给「每 px 能少折最多行」的那一列，
     得到一条「表格宽度 → 表格高度」曲线；
  2. 在曲线上取「高度 + 宽度 × 比价」最小的一点：加宽 --ratio px（默认 150）至少要换回 1 行高度才值得加，
     换不回就停。内容短的表停在刚好一行放下的宽度，长说明多的表才会拉到满宽；
  3. 在选定宽度上再做列间挪宽度的微调，取行数最少的分法。

用法：
  python3 表格长度优化.py <目标> [<目标> ...]           只出报告，不改
  python3 表格长度优化.py <目标> ... --apply            写回
  目标可以是：
    飞书文档 / 知识库链接或 docx token      → 直接改文档里每张表的列宽（只动列宽，不动文字，飞书历史版本可回退）
    飞书文件夹链接（加 --recursive 连子文件夹） → 文件夹里每篇 docx 都处理
    本地 .md 文件                            → 默认把表格改写成带列宽的表格标签：飞书导入（docs +create / +update
                                               --doc-format markdown）按这个列宽建表，MacDown / Typora 预览也认；
                                               --md-format pipe 则保留 | 表格，只按中英文宽度把源码对齐
  可选：
    --ratio 150        宽高比价：加宽多少 px 至少要省 1 行才加宽。调小 → 表更窄更高，调大 → 表更宽更矮
    --max-width 738    表格最宽（飞书标准页宽正文满宽；宽版页面用 938）
    -o 输出.md          只处理一个 .md 时，写到别的文件而不是原地覆盖（仍需 --apply）
"""
import argparse
import html
import json
import math
import re
import subprocess
import sys
import time
import unicodedata
from functools import lru_cache
from pathlib import Path

# ---------- 排版模型（按飞书标准页宽的渲染效果校准） ----------
UNIT_PX = 7         # 半角字符宽；全角（含 ≥ × 【】 等歧义宽度符号）算 2 个单位 = 14px
PAD_PX = 28        # 单元格左右内边距 + 边框，含估算余量
LINE_PX = 24       # 单元格里一行字的高
ROW_PAD_PX = 18    # 每行上下内边距
MIN_COL = 64       # 最窄一列
SHORT_CELL = 16    # 8 个汉字以内的短格整格不折行
ORPHAN = 0.4       # 折行后末行只剩 1～3 个字，算 0.4 行的难看
SMOOTH = 0.1       # 行高没变时，某格少折一行也算一点分，引导宽度给真正折行的格
LONG_ROWS = 15     # 数据行超过这个数，提示拆表
TALL_CELL = 6      # 某行折到这么多行，提示长说明挪到表外
NO_BREAK = re.compile(r"【[^】]{1,8}】|[≥≤<>]?\s?[A-Za-z0-9_.\-/:%+#@]+(?:\s?[%％])?")


# ====================== 通用：宽度模型与优化 ======================

def units(s):
    return sum(2 if unicodedata.east_asian_width(c) in ("W", "F", "A") else 1 for c in s)


# 断行单位：英文 / 数字串整体换行；开头括号粘后一个字，收尾标点粘前一个字（中文排版避头尾）
TOKEN = re.compile(r"[「『（(【《“‘\[]*(?:[A-Za-z0-9_.\-/:%+#@&=~^$€¥£°]+|.)[，。、；：！？」』）)】》”’…,.;:!?\]]*\s?", re.S)


def tokenize(line):
    return tuple(units(t) for t in TOKEN.findall(line)) or (0,)


@lru_cache(maxsize=None)
def wrap(tokens, cap):
    """按真实断行模拟：返回（行数，末行宽度单位）。"""
    n, cur = 1, 0
    for w in tokens:
        if cur + w <= cap:
            cur += w
        elif w <= cap:
            n, cur = n + 1, w
        else:  # 比一行还长的串只能硬拆
            rest = w - (cap - cur)
            extra = -(-rest // cap)
            n += extra
            cur = rest - (extra - 1) * cap
    return n, cur


def wrap_steps(tokens, cap, limit_cap, count=3):
    """比 cap 更宽的前 count 个「少一行」的断点（单位宽）。"""
    out = []
    k = wrap(tokens, cap)[0]
    lo = cap
    while k > 1 and len(out) < count and lo < limit_cap:
        a, b = lo + 1, limit_cap
        if wrap(tokens, b)[0] >= k:
            break
        while a < b:
            mid = (a + b) // 2
            if wrap(tokens, mid)[0] < k:
                b = mid
            else:
                a = mid + 1
        out.append(a)
        lo, k = a, wrap(tokens, a)[0]
    return out


class Table:
    """一张表：cells = [(行, 列, 跨列, 跨行, (每行文字的断行单位宽度, ...)), ...]"""

    def __init__(self, ncols, nrows, cells, header, current=None, limit=738, ident=None, label=""):
        self.ncols, self.nrows, self.cells = ncols, nrows, cells
        self.header, self.current, self.limit = header, current, limit
        self.id, self.label = ident, label

    def evaluate(self, widths):
        """返回（行数，平滑项）。行数 = 各行最高格的折行数之和；另加每个孤字 ORPHAN 行的难看分。"""
        starts = [0]
        for w in widths:
            starts.append(starts[-1] + w)
        rows = [1.0] * self.nrows
        smooth = orphans = 0
        for r, c, cs, rs, us in self.cells:
            w = starts[min(c + cs, self.ncols)] - starts[c]
            cap = max((w - PAD_PX) // UNIT_PX, 1)
            n = orphan = 0
            for toks in us:
                k, last = wrap(toks, cap)
                n += k
                if k > 1 and last <= 6:
                    orphan += 1
            h = n / rs
            for rr in range(r, min(r + rs, self.nrows)):
                rows[rr] = max(rows[rr], h)
            smooth += n
            orphans += orphan
        return sum(rows) + ORPHAN * orphans, smooth

    def height_px(self, lines):
        return lines * LINE_PX + self.nrows * ROW_PAD_PX


def longest_token(us_lines):
    best = 0
    for ln in us_lines:
        u = units(ln)
        if u <= SHORT_CELL:
            best = max(best, u)
        for t in NO_BREAK.findall(ln):
            best = max(best, units(t))
    return best


def floors_of(t, texts):
    """每列下限：表头不折行、短格与【标记】/数字英文串不拆、最窄 MIN_COL。"""
    fl = [MIN_COL] * t.ncols
    for (r, c, cs, rs, _), lines in zip(t.cells, texts):
        if cs != 1:
            continue
        if r < t.header:
            need = max(units(ln) for ln in lines) * UNIT_PX + PAD_PX
        else:
            need = longest_token(lines) * UNIT_PX + PAD_PX
        fl[c] = max(fl[c], need)
    return [min(f, int(t.limit * 0.45)) for f in fl]


def naturals_of(t):
    nat = [MIN_COL] * t.ncols
    for r, c, cs, rs, us in t.cells:
        if cs == 1:
            nat[c] = max(nat[c], max(sum(toks) for toks in us) * UNIT_PX + PAD_PX)
    return nat


def fit_into(weights, floor, total):
    w = [max(f, total * x / sum(weights)) for f, x in zip(floor, weights)]
    over = sum(w) - total
    if over > 0:  # 下限挤占后按余量比例收回
        slack = [a - f for a, f in zip(w, floor)]
        if sum(slack) > 0:
            w = [a - over * s / sum(slack) for a, s in zip(w, slack)]
    w = [int(v) for v in w]
    w[w.index(max(w))] += total - sum(w)
    return w


def next_steps(t, widths, col):
    """给第 col 列加多少 px，能让经过它的某格少折一行（取最近 3 个断点）。"""
    starts = [0]
    for w in widths:
        starts.append(starts[-1] + w)
    adds = set()
    for r, c, cs, rs, us in t.cells:
        if not (c <= col < c + cs):
            continue
        w = starts[min(c + cs, t.ncols)] - starts[c]
        cap = max((w - PAD_PX) // UNIT_PX, 1)
        limit_cap = (t.limit - PAD_PX) // UNIT_PX
        for toks in us:
            for need_cap in wrap_steps(toks, cap, limit_cap):
                need = need_cap * UNIT_PX + PAD_PX
                if need > w:
                    adds.add(need - w)
    return sorted(adds)[:3]


def optimize(t, texts, ratio):
    """返回 (新列宽, 说明)。"""
    n = t.ncols
    floor = floors_of(t, texts)
    notes = []
    if sum(floor) > t.limit:
        notes.append(f"{n} 列塞不下（下限合计 {sum(floor)}px）：建议拆表或删列")
        if MIN_COL * n >= t.limit:
            return [MIN_COL] * n, notes
        floor = fit_into(floor, [MIN_COL] * n, t.limit)
        return floor, notes

    lam = LINE_PX / ratio
    # 1) 宽度 → 高度曲线
    w = floor[:]
    lines, sm = t.evaluate(w)
    path = [(w[:], lines)]
    while sum(w) < t.limit:
        room = t.limit - sum(w)
        base = lines + SMOOTH * sm
        best = None
        for c in range(n):
            for add in next_steps(t, w, c):
                if add > room:
                    break
                trial = w[:]
                trial[c] += add
                l2, s2 = t.evaluate(trial)
                v = l2 + SMOOTH * s2
                if v < base - 1e-9:
                    gain = (base - v) / add
                    if best is None or gain > best[0]:
                        best = (gain, c, add, l2, s2)
                    break
        if not best:
            break
        _, c, add, lines, sm = best
        w[c] += add
        path.append((w[:], lines))

    # 2) 曲线上取「高度 + 宽度 × 比价」最小的一点
    def cost(ws, ls):
        return t.height_px(ls) + lam * sum(ws)

    chosen, chosen_lines = min(path, key=lambda p: cost(*p))
    total = sum(chosen)

    # 3) 选定宽度上做列间挪宽度的微调（多个起点）
    def polish(ws):
        ws = ws[:]
        l, s = t.evaluate(ws)
        score = l + 0.01 * s
        moved = True
        while moved:
            moved = False
            for step in (64, 32, 16, 8, 4):
                for i in range(n):
                    for j in range(n):
                        if i == j or ws[j] - step < floor[j]:
                            continue
                        trial = ws[:]
                        trial[i] += step
                        trial[j] -= step
                        l2, s2 = t.evaluate(trial)
                        if l2 + 0.01 * s2 < score - 1e-9:
                            ws, score, moved = trial, l2 + 0.01 * s2, True
        return ws, score

    starts = [chosen, fit_into(naturals_of(t), floor, total)]
    if t.current and len(t.current) == n and all(t.current):
        starts.append(fit_into(t.current, floor, total))
    new, _ = min((polish(s) for s in starts), key=lambda p: p[1])

    # 现状已经不差就不动，避免重复运行来回抖
    if t.current and len(t.current) == n and all(t.current) and sum(t.current) <= t.limit:
        if cost(t.current, t.evaluate(t.current)[0]) <= cost(new, t.evaluate(new)[0]) + 1:
            new = t.current[:]

    data_rows = t.nrows - t.header
    if data_rows > LONG_ROWS:
        notes.append(f"{data_rows} 行偏长：建议按组拆开或挪附录")
    if data_rows <= 1:
        notes.append("只有 1 行数据：建议改成一句话")
    tallest = max_cell_lines(t, new)
    if tallest >= TALL_CELL:
        notes.append(f"有格子折到 {tallest} 行：长说明建议挪到表下正文")
    return new, notes


def max_cell_lines(t, widths):
    starts = [0]
    for w in widths:
        starts.append(starts[-1] + w)
    worst = 1
    for r, c, cs, rs, us in t.cells:
        w = starts[min(c + cs, t.ncols)] - starts[c]
        cap = max((w - PAD_PX) // UNIT_PX, 1)
        worst = max(worst, sum(wrap(toks, cap)[0] for toks in us))
    return worst


def report_line(k, t, new, notes):
    lb = t.evaluate(new)[0]
    after = f"宽 {sum(new)}px、高约 {t.height_px(lb):.0f}px（{lb:g} 行字）"
    if t.current and all(t.current):
        la = t.evaluate(t.current)[0]
        before = f"宽 {sum(t.current)}px、高约 {t.height_px(la):.0f}px（{la:g} 行字）"
        cols = f"列宽 {t.current} → {new}"
        head = f"{before} → {after}"
    else:
        cols = f"列宽 {new}"
        head = after
    flag = "" if not notes else "   ⚠ " + "；".join(notes)
    same = "（不变）" if t.current == new else ""
    return f"  表{k:>3} {t.label}（{t.nrows}×{t.ncols}）{same}\n        {head}   {cols}{flag}"


# ====================== lark-cli ======================

def lark(args, stdin=None):
    """调 lark-cli；飞书偶发 network/transport EOF，最多重试 3 次（设列宽幂等，重试安全）。"""
    res = {}
    for attempt in range(4):
        p = subprocess.run(["lark-cli", *args], input=stdin, capture_output=True, text=True)
        res = {"ok": False, "raw": (p.stdout + p.stderr)[-600:]}
        for out in (p.stdout, p.stderr):
            try:
                res = json.loads(out)
                break
            except json.JSONDecodeError:
                continue
        if res.get("ok") or '"network"' not in json.dumps(res, ensure_ascii=False) + p.stderr:
            return res
        time.sleep(3 * (attempt + 1))
    return res


def resolve_feishu(target, recursive):
    """把链接 / token 解析成 [(docx token, 标题)]。"""
    if not target.startswith("http"):
        return [(target, target)]
    info = lark(["drive", "+inspect", "--as", "user", "--url", target])
    if not info.get("ok"):
        print(f"✗ 解析不了 {target}：{json.dumps(info, ensure_ascii=False)[:300]}")
        return []
    d = info["data"]
    if d.get("type") == "folder":
        return list_folder(d["token"], recursive)
    if d.get("type") != "docx":
        print(f"· 跳过 {d.get('title', target)}：类型 {d.get('type')} 不是新版文档（docx）")
        return []
    return [(d["token"], d.get("title", d["token"]))]


def list_folder(folder, recursive):
    res = lark(["api", "GET", "/open-apis/drive/v1/files", "--as", "user", "--page-all",
                "--params", json.dumps({"folder_token": folder, "page_size": 200})])
    files = []
    for key in ("files",):
        files = res.get("data", {}).get(key) or []
    if not files and isinstance(res.get("data"), list):  # --page-all 可能返回分页数组
        for page in res["data"]:
            files += page.get("files", [])
    out = []
    for f in files:
        if f.get("type") == "docx":
            out.append((f["token"], f.get("name", f["token"])))
        elif f.get("type") == "folder" and recursive:
            out += list_folder(f["token"], recursive)
    return out


# ====================== 飞书文档 ======================

def xml_cell_lines(inner):
    has_img = "<img" in inner
    s = re.sub(r"<br\s*/?>", "\n", inner)
    s = re.sub(r"</(p|li|h\d|pre|checkbox|blockquote)>", "\n", s)
    s = html.unescape(re.sub(r"<[^>]+>", "", s))
    lines = [ln.strip() for ln in s.split("\n")]
    lines = [ln for ln in lines if ln] or [""]
    if has_img:
        lines.append("图" * 11)  # 图片按约 160px 宽占位
    return lines


def parse_xml_tables(xml, max_width):
    grid_cols = [(m.start(), m.end(), float(m.group(1)))
                 for m in re.finditer(r'<column[^>]*width-ratio="([\d.]+)"[^>]*>.*?</column>', xml, re.S)]
    tables = []
    for m in re.finditer(r"<table\b([^>]*)>(.*?)</table>", xml, re.S):
        tid = (re.search(r'id="([^"]+)"', m.group(1)) or [None, None])[1]
        body = m.group(2)
        current = []
        for attrs in re.findall(r"<col\b([^>]*)/?>", body):
            w = re.search(r'width="(\d+)"', attrs)
            sp = re.search(r'span="(\d+)"', attrs)
            current += [int(w.group(1)) if w else 0] * (int(sp.group(1)) if sp else 1)
        limit = max_width
        for a, b, ratio in grid_cols:
            if a <= m.start() < b:
                limit = int(max_width * ratio) - 16
        cells, texts, occupied = [], [], set()
        header = 0
        rows = re.findall(r"<tr[^>]*>(.*?)</tr>", body, re.S)
        for r, row in enumerate(rows):
            c = 0
            for tag, attrs, inner in re.findall(r"<(t[hd])([^>]*)>(.*?)</t[hd]>", row, re.S):
                while (r, c) in occupied:
                    c += 1
                cs = int((re.search(r'colspan="(\d+)"', attrs) or [0, 1])[1])
                rs = int((re.search(r'rowspan="(\d+)"', attrs) or [0, 1])[1])
                for rr in range(r, r + rs):
                    for cc in range(c, c + cs):
                        occupied.add((rr, cc))
                lines = xml_cell_lines(inner)
                cells.append((r, c, cs, rs, tuple(tokenize(ln) for ln in lines)))
                texts.append(lines)
                c += cs
            if tag_is_header(row):
                header = r + 1
        ncols = len(current) or max((c + cs for _, c, cs, _, _ in cells), default=1)
        label = " / ".join(t[0][:8] for (r, *_), t in zip(cells, texts) if r == 0)[:40]
        tables.append((Table(ncols, len(rows), cells, max(header, 1), current or None, limit, tid, label), texts))
    return tables


def tag_is_header(row):
    return "<th" in row and "<td" not in row


def run_feishu(token, title, args):
    res = lark(["docs", "+fetch", "--as", "user", "--doc", token, "--doc-format", "xml", "--detail", "with-ids"])
    content = res.get("data", {}).get("document", {}).get("content")
    if not isinstance(content, str):
        print(f"✗ 读不到《{title}》：{json.dumps(res, ensure_ascii=False)[:300]}")
        return
    m = re.search(r"<title[^>]*>(.*?)</title>", content, re.S)
    if m and title == token:
        title = html.unescape(re.sub(r"<[^>]+>", "", m.group(1))).strip() or token
    tables = parse_xml_tables(content, args.max_width)
    print(f"\n《{title}》 {len(tables)} 张表")
    plan = []
    for k, (t, texts) in enumerate(tables, 1):
        new, notes = optimize(t, texts, args.ratio)
        print(report_line(k, t, new, notes))
        if t.current != new:
            plan.append((t, new))
    print(f"  → 要改 {len(plan)} 张表" + ("" if args.apply else "（加 --apply 写入）"))
    if not args.apply or not plan:
        return

    # 每次批量调用里同一张表只能出现一次：按列序号分轮，每轮最多 100 条
    rounds = {}
    for t, new in plan:
        for i, w in enumerate(new):
            if not t.current or i >= len(t.current) or t.current[i] != w:
                rounds.setdefault(i, []).append({"block_id": t.id,
                                                 "update_table_property": {"column_width": w, "column_index": i}})
    failed = 0
    for i in sorted(rounds):
        reqs = rounds[i]
        for s in range(0, len(reqs), 100):
            r = lark(["api", "PATCH", f"/open-apis/docx/v1/documents/{token}/blocks/batch_update", "--as", "user",
                      "--params", '{"document_revision_id":-1}',
                      "--data", json.dumps({"requests": reqs[s:s + 100]})])
            if not r.get("ok"):
                failed += 1
                print(f"  ✗ 第 {i} 列那一轮写入失败：{json.dumps(r, ensure_ascii=False)[:300]}")
            time.sleep(0.4)
    content = None
    for _ in range(3):
        check = lark(["docs", "+fetch", "--as", "user", "--doc", token, "--doc-format", "xml", "--detail", "with-ids"])
        content = check.get("data", {}).get("document", {}).get("content")
        if isinstance(content, str):
            break
        time.sleep(3)
    if not isinstance(content, str):
        print(f"  已写入（批量调用失败 {failed} 次），但回读失败，请重跑一次不加 --apply 核对：要改 0 张即已落地")
        return
    got = {t.id: t.current for t, _ in parse_xml_tables(content, args.max_width)}
    off = [t.id for t, new in plan if got.get(t.id) != new]
    print(f"  已写入：批量调用失败 {failed} 次，回读与目标不符 {len(off)} 张" + (f"：{off}" if off else ""))


# ====================== Markdown ======================

SEP = re.compile(r"^\s*\|?\s*:?-{1,}:?\s*(\|\s*:?-{1,}:?\s*)*\|?\s*$")


def split_row(line):
    s = line.strip()
    if s.startswith("|"):
        s = s[1:]
    if s.endswith("|") and not s.endswith("\\|"):
        s = s[:-1]
    return [c.strip() for c in re.split(r"(?<!\\)\|", s)]


def md_plain_lines(cell):
    s = re.sub(r"<br\s*/?>", "\n", cell, flags=re.I)
    s = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", s)
    s = re.sub(r"(\*\*|__|~~|`)", "", s)
    s = re.sub(r"(?<!\w)[*_](?=\S)(.+?)(?<=\S)[*_](?!\w)", r"\1", s)
    s = re.sub(r"\\(.)", r"\1", s)
    s = html.unescape(re.sub(r"<[^>]+>", "", s))
    return [ln.strip() for ln in s.split("\n")] or [""]


def md_inline_to_xml(cell):
    codes = []

    def keep_code(m):
        codes.append(m.group(1))
        return f"\x00{len(codes) - 1}\x00"

    s = re.sub(r"`([^`]+)`", keep_code, cell)
    s = re.sub(r"<br\s*/?>", "\x01", s, flags=re.I)
    s = re.sub(r"\\([\\`*_{}\[\]()#+\-.!|<>~])", lambda m: f"\x02{ord(m.group(1))}\x02", s)
    s = html.escape(s, quote=False)
    s = re.sub(r"\[([^\]]+)\]\(([^)\s]+)\)", lambda m: f'<a href="{html.escape(m.group(2))}">{m.group(1)}</a>', s)
    s = re.sub(r"\*\*(.+?)\*\*|__(.+?)__", lambda m: f"<b>{m.group(1) or m.group(2)}</b>", s)
    s = re.sub(r"~~(.+?)~~", r"<del>\1</del>", s)
    s = re.sub(r"(?<![\w*])\*(?=\S)(.+?)(?<=\S)\*(?![\w*])", r"<em>\1</em>", s)
    s = s.replace("\x01", "<br/>")
    s = re.sub(r"\x02(\d+)\x02", lambda m: html.escape(chr(int(m.group(1))), quote=False), s)
    s = re.sub(r"\x00(\d+)\x00", lambda m: f"<code>{html.escape(codes[int(m.group(1))], quote=False)}</code>", s)
    return s


def find_md_tables(lines):
    """返回 [(起行, 止行(不含), 表头格, 对齐, 数据行)]；跳过代码块。"""
    out, i, fence = [], 0, None
    while i < len(lines):
        ln = lines[i]
        f = re.match(r"^\s*(```|~~~)", ln)
        if f:
            fence = None if fence == f.group(1) else (fence or f.group(1))
            i += 1
            continue
        if fence is None and "|" in ln and i + 1 < len(lines) and SEP.match(lines[i + 1]):
            head = split_row(ln)
            aligns = split_row(lines[i + 1])
            if len(aligns) == len(head):
                j = i + 2
                rows = []
                while j < len(lines) and "|" in lines[j] and lines[j].strip():
                    cells = split_row(lines[j])
                    rows.append((cells + [""] * len(head))[:len(head)])
                    j += 1
                out.append((i, j, head, aligns, rows))
                i = j
                continue
        i += 1
    return out


def md_table(head, rows, max_width, label):
    allrows = [head] + rows
    cells, texts = [], []
    for r, row in enumerate(allrows):
        for c, cell in enumerate(row):
            lines = md_plain_lines(cell)
            cells.append((r, c, 1, 1, tuple(tokenize(ln) for ln in lines)))
            texts.append(lines)
    return Table(len(head), len(allrows), cells, 1, None, max_width, None, label), texts


def render_xml_table(head, rows, widths):
    cols = "".join(f'<col width="{w}"/>' for w in widths)
    th = "".join(f"<th><p>{md_inline_to_xml(c)}</p></th>" for c in head)
    body = "".join("<tr>" + "".join(f"<td><p>{md_inline_to_xml(c)}</p></td>" for c in row) + "</tr>" for row in rows)
    return f"<table><colgroup>{cols}</colgroup><thead><tr>{th}</tr></thead><tbody>{body}</tbody></table>"


def mono(s):
    """等宽编辑器里的列数：只有全角 / 宽字符占 2 列。"""
    return sum(2 if unicodedata.east_asian_width(c) in ("W", "F") else 1 for c in s)


def render_pipe_table(head, aligns, rows):
    allrows = [head] + rows
    width = [max(3, max(mono(r[c]) for r in allrows)) for c in range(len(head))]

    def pad(s, w):
        return s + " " * (w - mono(s))

    def sep(a, w):
        left, right = a.startswith(":"), a.endswith(":")
        return (":" if left else "-") + "-" * (w - 2) + (":" if right else "-")

    out = ["| " + " | ".join(pad(c, w) for c, w in zip(head, width)) + " |",
           "| " + " | ".join(sep(a, w) for a, w in zip(aligns, width)) + " |"]
    out += ["| " + " | ".join(pad(c, w) for c, w in zip(r, width)) + " |" for r in rows]
    return out


def retune_xml_tables(text, args, first_no):
    """.md 里原本就有的表格标签（飞书 XML / HTML，含本脚本上次改写的）：只重算列宽。
    返回（新文本，表格标签数，要调的张数，报告行）。"""
    fences = [(m.start(), m.end()) for m in re.finditer(r"^(```|~~~).*?^\1", text, re.S | re.M)]
    pieces, last, n_xml, changed, lines = [], 0, 0, 0, []
    for m in re.finditer(r"<table\b[^>]*>.*?</table>", text, re.S):
        if any(a <= m.start() < b for a, b in fences):
            continue
        parsed = parse_xml_tables(m.group(0), args.max_width)
        if not parsed:
            continue
        t, texts = parsed[0]
        n_xml += 1
        new, notes = optimize(t, texts, args.ratio)
        if t.current == new:
            continue
        lines.append(report_line(first_no + n_xml, t, new, notes))
        changed += 1
        cols = "<colgroup>" + "".join(f'<col width="{w}"/>' for w in new) + "</colgroup>"
        tbl = m.group(0)
        if "<colgroup" in tbl:
            tbl = re.sub(r"<colgroup>.*?</colgroup>", cols, tbl, count=1, flags=re.S)
        else:
            tbl = re.sub(r"(<table\b[^>]*>)", r"\1" + cols, tbl, count=1)
        pieces += [text[last:m.start()], tbl]
        last = m.end()
    return "".join(pieces) + text[last:], n_xml, changed, lines


def run_md(path, args):
    p = Path(path)
    text = p.read_text(encoding="utf-8")
    n_pipe = len(find_md_tables(text.split("\n")))
    # 先处理原文里已有的表格标签，再把 | 表格改写，避免把刚改写出来的表再算一遍
    text, n_xml, changed, xml_report = retune_xml_tables(text, args, n_pipe)
    lines = text.split("\n")
    found = find_md_tables(lines)
    print(f"\n《{p.name}》 Markdown 表格 {len(found)} 张（输出格式：{args.md_format}）"
          + (f"，表格标签 {n_xml} 张" if n_xml else ""))
    replaced = {}
    for k, (a, b, head, aligns, rows) in enumerate(found, 1):
        label = " / ".join(md_plain_lines(h)[0][:8] for h in head)[:40]
        t, texts = md_table(head, rows, args.max_width, label)
        new, notes = optimize(t, texts, args.ratio)
        print(report_line(k, t, new, notes))
        if args.md_format == "pipe":
            replaced[a] = (b, render_pipe_table(head, aligns, rows))
        else:
            block = [render_xml_table(head, rows, new)]
            if a > 0 and lines[a - 1].strip():
                block.insert(0, "")
            if b < len(lines) and lines[b].strip():
                block.append("")
            replaced[a] = (b, block)
    for ln in xml_report:
        print(ln)
    if n_xml:
        print(f"  表格标签 {n_xml} 张，其中 {changed} 张列宽要调")
    out, i = [], 0
    while i < len(lines):
        if i in replaced:
            b, block = replaced[i]
            out += block
            i = b
        else:
            out.append(lines[i])
            i += 1
    result = "\n".join(out)

    if not args.apply or not (found or changed):
        if found or changed:
            print("  → 加 --apply 写入" + (f" {args.output}" if args.output else "（原地覆盖）"))
        return
    dest = Path(args.output) if args.output else p
    dest.write_text(result, encoding="utf-8")
    print(f"  已写入 {dest}")


# ====================== 入口 ======================

def main():
    ap = argparse.ArgumentParser(description="表格长度优化：飞书文档 / Markdown 表格在宽度与高度之间取最优比")
    ap.add_argument("targets", nargs="+", help="飞书文档 / 知识库 / 文件夹链接、docx token，或本地 .md 文件")
    ap.add_argument("--apply", action="store_true", help="写回；不加只出报告")
    ap.add_argument("--ratio", type=float, default=150, help="加宽多少 px 至少要省 1 行才加宽（默认 150）")
    ap.add_argument("--max-width", type=int, default=738, help="表格最宽（默认 738 = 飞书标准页宽正文满宽）")
    ap.add_argument("--recursive", action="store_true", help="文件夹连子文件夹一起处理")
    ap.add_argument("--md-format", choices=["feishu", "pipe"], default="feishu",
                    help="feishu = 改写成带列宽的表格标签（飞书导入 / MacDown 预览都认）；pipe = 保留 | 表格只对齐源码")
    ap.add_argument("-o", "--output", help="只处理一个 .md 时写到这个文件")
    args = ap.parse_args()

    md = [x for x in args.targets if Path(x).suffix.lower() in (".md", ".markdown") and Path(x).exists()]
    if args.output and len(md) != 1:
        sys.exit("-o 只能配一个 .md 文件")
    for target in args.targets:
        if target in md:
            run_md(target, args)
        else:
            for token, title in resolve_feishu(target, args.recursive):
                run_feishu(token, title, args)


if __name__ == "__main__":
    main()
