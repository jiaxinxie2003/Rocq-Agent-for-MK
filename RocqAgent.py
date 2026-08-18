import json
import re
import subprocess
import os
import threading
from datetime import datetime
from openai import OpenAI

# ========== 1. 创建本地客户端 ==========
client = OpenAI(
    api_key="xxxxx",           # 替换key
    base_url="https://api.deepseek.com"      
)


# ========== 2. 定义工具 ==========
COQ_OUTPUT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "coq_output")

def _safe_write_path(filename):
    """仅用于 create_text_file：强制将新建文件限制在 COQ_OUTPUT_DIR 内。"""
    if not filename.endswith(".v"):
        return None, f"文件名《{filename}》不是 .v 后缀，只允许创建 Coq 源文件（.v）。"
    basename = os.path.basename(filename)
    safe = os.path.join(COQ_OUTPUT_DIR, basename)
    os.makedirs(COQ_OUTPUT_DIR, exist_ok=True)
    return safe, None

def _safe_read_path(filename):
    """用于 read_coq_file / compile_coq：允许任意路径的 .v 文件，只做后缀校验。"""
    if not filename.endswith(".v"):
        return None, f"文件名《{filename}》不是 .v 后缀，只允许操作 Coq 源文件（.v）。"
    if not os.path.isabs(filename):
        return None, f"文件路径《{filename}》不是绝对路径，请提供完整的文件路径。"
    return filename, None


def _resolve_file_path(filename):
    """解析文件路径：绝对路径（含盘符）直接使用，纯文件名放到 COQ_OUTPUT_DIR。"""
    if not filename.endswith(".v"):
        return None, f"文件名《{filename}》不是 .v 后缀，只允许操作 Coq 源文件（.v）。"
    if os.path.isabs(filename):
        return filename, None
    basename = os.path.basename(filename)
    safe = os.path.join(COQ_OUTPUT_DIR, basename)
    os.makedirs(COQ_OUTPUT_DIR, exist_ok=True)
    return safe, None


# ========== Coq Session：持久化 coqtop 进程管理 ==========

def split_commands(content):
    commands = []
    n = len(content)
    i = 0
    in_string = False
    comment_depth = 0
    sent_start = 0
    at_sent_start = True   

    while i < n:
        c = content[i]

        # ---- 字符串字面量 ----
        if in_string:
            if c == '"' and content[i-1:i] != '\\':
                in_string = False
            i += 1
            continue

        # ---- 嵌套注释 (* ... *) ----
        if comment_depth > 0:
            if content[i:i+2] == '(*':
                comment_depth += 1
                i += 2
                continue
            if content[i:i+2] == '*)':
                comment_depth -= 1
                i += 2
                continue
            i += 1
            continue

        if content[i:i+2] == '(*':
            comment_depth += 1
            i += 2
            continue

        if c == '"':
            in_string = True
            at_sent_start = False
            i += 1
            continue

        # ---- 非空白字符表示已离开句首 ----
        if c not in ' \t\n\r':
            at_sent_start = False

        # ---- '.' 命令终止符：后面必须是空白或 EOF ----
        if c == '.':
            after = content[i+1] if i+1 < n else ''
            if after in ('', ' ', '\t', '\n', '\r'):
                text = content[sent_start:i+1].strip()
                if text:
                    commands.append(text)
                i += 1
                while i < n and content[i] in ' \t\n\r':
                    i += 1
                sent_start = i
                at_sent_start = True
                continue

        # ---- bullets / braces 检测：仅在句首 ----
        if at_sent_start and c in '-+*{}':
            if c in '{}':
                if sent_start < i:
                    before = content[sent_start:i].strip()
                    if before:
                        commands.append(before)
                commands.append(c)
                i += 1
                while i < n and content[i] in ' \t\n\r':
                    i += 1
                sent_start = i
                at_sent_start = True
                continue

            # bullets: -、+、* 及多字符变体（-- / ++ / ** / --- / +++ / ***）
            j = i
            bullet_char = content[i]
            while j < n and content[j] == bullet_char and (j - i) < 3:
                j += 1
            after_bullet = content[j] if j < n else ''
            if after_bullet in ('', ' ', '\t', '\n', '\r'):
                if sent_start < i:
                    before = content[sent_start:i].strip()
                    if before:
                        commands.append(before)
                commands.append(content[i:j])
                i = j
                while i < n and content[i] in ' \t\n\r':
                    i += 1
                sent_start = i
                at_sent_start = True
                continue

        i += 1

    remaining = content[sent_start:].strip()
    if remaining:
        commands.append(remaining)

    return commands


class CoqSession:
    """持久化 coqtop 会话，使用 subprocess.Popen 维持长期 coqtop 进程。"""

    def __init__(self, coqtop_path):
        self.coqtop_path = coqtop_path
        self.process = None
        self._stderr_thread = None

    def start(self):
        """启动 coqtop 进程。"""
        if self.process is not None:
            return
        self.process = subprocess.Popen(
            [self.coqtop_path, "-quiet"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            bufsize=1,
        )
        # 后台线程持续排空 stderr，防止管道阻塞
        self._start_stderr_drain()
        # 读取初始 prompt
        self.read_until_prompt(timeout=10)

    def stop(self):
        """关闭 coqtop 进程。"""
        if self.process is None:
            return
        try:
            self.process.stdin.close()
        except Exception:
            pass
        try:
            self.process.terminate()
            self.process.wait(timeout=5)
        except Exception:
            try:
                self.process.kill()
                self.process.wait(timeout=5)
            except Exception:
                pass
        self.process = None
        self._stderr_thread = None

    def restart(self):
        """关闭并重新启动 coqtop。"""
        self.stop()
        self.start()

    def send_command(self, cmd, timeout=30, read_output=True):
        if self.process is None:
            raise RuntimeError("CoqSession 未启动，请先调用 start()")
        if self.process.poll() is not None:
            raise RuntimeError(
                f"coqtop 进程已退出 (exit code {self.process.returncode})，请调用 restart()"
            )
        self.process.stdin.write(cmd.strip() + '\n')
        self.process.stdin.flush()
        if read_output:
            return self.read_until_prompt(timeout=timeout)
        return None

    def load_file(self, filename):
        with open(filename, 'r', encoding='utf-8') as f:
            content = f.read()
        commands = split_commands(content)
        for cmd in commands:
            self.send_command(cmd, read_output=False)
        # 批量加载完成后，读取一次输出使 coqtop 回到 stable prompt 状态
        self.read_until_prompt()

    def show_goal(self):
        raw = self.send_command('Show.')
        output = _extract_goal_output(raw)

        if not output:
            return "当前没有活动证明（No focused proof）。"
        if 'No focused proof' in output:
            return "当前没有活动证明（No focused proof）。"
        if 'Error:' in output:
            return (
                "无法获取证明状态（coqtop 报错）：\n"
                f"{output}\n\n"
                "请先使用 compile_coq 检查文件中的编译错误。"
            )
        return output

    def show_proof(self):
        """发送 Show Proof. 并返回当前证明项。"""
        raw = self.send_command('Show Proof.')
        return _extract_goal_output(raw)

    def read_until_prompt(self, timeout=30):
        """
        持续读取 stdout 直到 Coq prompt 出现，或超时/EOF。
        使用独立线程避免阻塞主流程。
        """
        output_lines = []
        done = threading.Event()
        read_error = []

        def reader():
            try:
                while not done.is_set():
                    if self.process is None or self.process.stdout is None:
                        break
                    line = self.process.stdout.readline()
                    if not line:          # EOF — 进程异常退出
                        read_error.append("coqtop 进程意外终止")
                        done.set()
                        break
                    output_lines.append(line)
                    s = line.strip()
                    # Coq prompt 格式：以 "<" 结尾的短行（兼容不同 Coq 版本）
                    if s.endswith('<'):
                        done.set()
                        break
            except Exception as e:
                read_error.append(str(e))
                done.set()

        t = threading.Thread(target=reader, daemon=True)
        t.start()
        t.join(timeout=timeout)

        if t.is_alive():
            done.set()
            t.join(timeout=2)

        if read_error:
            raise RuntimeError(read_error[0])

        return ''.join(output_lines)

    def _start_stderr_drain(self):
        """后台线程持续排空 stderr，防止管道满导致进程阻塞。"""

        def drain():
            try:
                while self.process and self.process.stderr:
                    line = self.process.stderr.readline()
                    if not line:
                        break
            except Exception:
                pass

        self._stderr_thread = threading.Thread(target=drain, daemon=True)
        self._stderr_thread.start()


# 全局会话状态：跟踪当前已加载的文件
_coq_session = None         
_coq_session_file = None     


def _invalidate_coq_session():
    """在文件被修改后调用，标记当前 session 为无效。"""
    global _coq_session, _coq_session_file
    if _coq_session is not None:
        _coq_session.stop()
        _coq_session = None
    _coq_session_file = None


def _extract_goal_output(raw_output):
    """从 coqtop 输出中移除末尾 prompt，返回干净的证明状态。"""
    if not raw_output:
        return raw_output
    output = raw_output.rstrip()
    for suffix in ('\n<', '\nCoq <', '\np <'):
        if output.endswith(suffix):
            output = output[:-len(suffix)]
    return output.strip()


# 用于创建文件并写入一些内容的函数工具
def create_text_file(filename, content):
    safe, err = _safe_write_path(filename)
    if err:
        return err
    _coqc_error_cache.pop(safe, None)  # 文件已修改，缓存失效
    with open(safe, 'w', encoding='utf-8') as f:
        f.write(content)
    _invalidate_coq_session()          # 文件已修改，Coq 会话必须重建
    return f"已成功创建文件《{safe}》（绝对路径）。如需编译，请使用 compile_coq 并传入此完整路径。"

# 替换文件中的指定内容（第二次及之后的修改使用此工具，而非重写整个文件）
def replace_in_file(filename, old_string, new_string):
    safe, err = _resolve_file_path(filename)
    if err:
        return err
    if not os.path.isfile(safe):
        return f"文件《{safe}》不存在，请检查路径是否正确。如需创建新文件请使用 create_text_file。"
    with open(safe, 'r', encoding='utf-8') as f:
        content = f.read()
    if old_string not in content:
        return f"替换失败！在文件《{safe}》中未找到要替换的内容。\n要替换的文本：\n{old_string[:500]}"
    new_content = content.replace(old_string, new_string, 1)
    _coqc_error_cache.pop(safe, None)  # 文件已修改，缓存失效
    with open(safe, 'w', encoding='utf-8') as f:
        f.write(new_content)
    _invalidate_coq_session()           # 文件已修改，Coq 会话必须重建
    return f"替换成功！已在文件《{safe}》中将指定内容替换为新内容。"

# 读取文件工具
def read_coq_file(filename):
    safe, err = _safe_read_path(filename)
    if err:
        return err
    if not os.path.isfile(safe):
        return f"文件《{safe}》不存在，请检查路径是否正确。"
    with open(safe, 'r', encoding='utf-8') as f:
        content = f.read()
    return f"文件《{safe}》的内容如下：\n{content}"

# coqc 错误缓存：compile_coq 失败后将错误信息缓存，get_coq_proof_state 直接复用，避免重复调用 coqc
_coqc_error_cache = {}  # {filepath: {"error": "...", "error_line": 42 | None}}

def _parse_coqc_error(error_output):
    """解析 coqc 错误输出，提取行号。"""
    match = re.search(r'line (\d+)', error_output)
    error_line = int(match.group(1)) if match else None
    return error_line

# Coq编译工具
def compile_coq(filename):
    coqc_path = r"D:\Coq\bin\coqc.exe"
    safe, err = _safe_read_path(filename)
    if err:
        return err
    if not os.path.isfile(safe):
        return f"文件《{safe}》不存在，请检查路径是否正确。"
    if not os.path.isfile(coqc_path):
        return f"coqc 编译器未找到，请检查 Coq 是否安装在 {coqc_path}。"

    # 文件被重新编译，清除旧缓存
    _coqc_error_cache.pop(safe, None)

    try:
        result = subprocess.run(
            [coqc_path, safe],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace"
        )
    except subprocess.TimeoutExpired:
        return f"编译超时！文件《{safe}》在 30 秒内未完成编译。"
    if result.returncode == 0:
        return f"编译成功！文件《{safe}》已通过 Coq 验证。"
    else:
        error_output = result.stderr.strip() or result.stdout.strip()
        # 缓存错误信息和行号，供 get_coq_proof_state 复用
        _coqc_error_cache[safe] = {
            "error": error_output,
            "error_line": _parse_coqc_error(error_output)
        }
        return f"编译失败！文件《{safe}》存在错误：\n{error_output}"


# 获取Coq证明状态的工具
# 使用持久化 CoqSession，不再每次重启 coqtop 重复执行整个文件
def get_coq_proof_state(filename):
    global _coq_session, _coq_session_file

    coqtop_path = r"D:\Coq\bin\coqtop.exe"
    coqc_path = r"D:\Coq\bin\coqc.exe"
    safe, err = _safe_read_path(filename)
    if err:
        return err
    if not os.path.isfile(safe):
        return f"文件《{safe}》不存在，请检查路径是否正确。"
    if not os.path.isfile(coqtop_path):
        return f"coqtop 未找到，请检查 Coq 是否安装在 {coqtop_path}。"

    try:
        with open(safe, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        return f"读取文件《{safe}》失败：{e}"

    # Step 1: 获取编译错误信息（优先从缓存读取 compile_coq 的结果）
    cached = _coqc_error_cache.get(safe)
    if cached:
        coqc_error = cached["error"]
        error_line = cached["error_line"]
    elif os.path.isfile(coqc_path):
        coqc_error = ""
        error_line = None
        try:
            coqc_result = subprocess.run(
                [coqc_path, safe],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=30
            )
            if coqc_result.returncode != 0:
                error_output = coqc_result.stderr.strip() or coqc_result.stdout.strip()
                coqc_error = error_output
                error_line = _parse_coqc_error(error_output)
        except subprocess.TimeoutExpired:
            pass
    else:
        coqc_error = ""
        error_line = None

    # Step 2: 确定是否需要重新建立会话（首次调用 / 文件变更 / session 已失效）
    need_reload = (_coq_session is None or _coq_session_file != safe)

    if need_reload:
        # 关闭旧会话
        if _coq_session is not None:
            _coq_session.stop()
            _coq_session = None
        _coq_session_file = None

        # 启动新会话
        _coq_session = CoqSession(coqtop_path)
        _coq_session.start()

        # 裁剪内容：如果存在编译错误，只加载报错行之前的命令
        if error_line is not None:
            prefix_text = '\n'.join(content.split('\n')[:error_line])
            cut = -1
            for sep in ('.\n', '. ', '.\t'):
                pos = prefix_text.rfind(sep)
                if pos > cut:
                    cut = pos
            if cut >= 0:
                load_content = prefix_text[:cut + 1]
            else:
                load_content = prefix_text
        else:
            load_content = content

        # 按 Vernac 命令逐条发送，加载期间不读取中间输出
        commands = split_commands(load_content)
        for cmd in commands:
            _coq_session.send_command(cmd, read_output=False)
        _coq_session.read_until_prompt()

        _coq_session_file = safe

    # Step 3: 仅发送 Show. 获取当前证明状态（不再重新执行整个文件）
    goal_output = _coq_session.show_goal()

    # Step 4: 组装返回结果
    parts = []
    if goal_output:
        parts.append(f"=== 当前证明状态 ===\n{goal_output}")
    if coqc_error:
        parts.append(f"=== coqc 编译错误 ===\n{coqc_error}")
    if not parts:
        return "coqtop 未返回任何输出，文件可能为空或格式不正确。"

    return "\n\n".join(parts)


# 对工具的具体描述
tools = [
    {
        "type": "function",  # 工具的类型(自定义函数工具的固定写法即为如此)
        "function": {
            "name": "create_text_file",   # 函数工具的名字
            "description": "创建一个新的 Coq .v 源文件。只需提供纯文件名（如 my_proof.v），文件会自动保存到 coq_output 目录下。",
            "parameters": {
                "type": "object",
                "properties": {
                    "filename": {"type": "string", "description": "要创建的 .v 文件名（纯文件名，不带路径，如 proof.v）"},
                    "content": {"type": "string", "description": "要写入的 Coq 代码内容"}
                },
                "required": ["filename", "content"]      # 想要使这个函数工具能够被调用运行，不可缺少的参数
            }
        }
    },
    {
        "type": "function",
        "function": {
            "name": "replace_in_file",
            "description": "替换 .v 文件中指定的文本片段。编译失败后应优先使用此工具做精准修改，而不是重写整个文件。可接受纯文件名（如 proof.v，自动保存到 coq_output 目录）或绝对路径（如 D:\\path\\to\\file.v，直接修改该文件）。修改用户指定的目标文件时必须使用绝对路径。old_string 必须与文件中的原文完全匹配（含缩进和换行），new_string 为替换后的内容。一次只替换一处匹配。",
            "parameters": {
                "type": "object",
                "properties": {
                    "filename": {"type": "string", "description": "要修改的 .v 文件名（纯文件名不带路径，或完整的绝对路径如 D:\\path\\to\\file.v）"},
                    "old_string": {"type": "string", "description": "文件中要被替换的原文（必须完全匹配，含缩进和换行）"},
                    "new_string": {"type": "string", "description": "替换后的新文本"}
                },
                "required": ["filename", "old_string", "new_string"]
            }
        }
    },
    {
        "type": "function",
        "function": {
            "name": "read_coq_file",
            "description": "读取任意路径下的 .v Coq 源文件内容。必须提供完整的绝对路径（如 D:\\Vscode\\py\\mk.v）。用于查看已有文件中的代码，了解当前定义或在此基础上进行修改。",
            "parameters": {
                "type": "object",
                "properties": {
                    "filename": {"type": "string", "description": "要读取的 .v 文件的绝对路径（如 D:\\Vscode\\py\\mk.v）"}
                },
                "required": ["filename"]
            }
        }
    },
    {
        "type": "function",
        "function": {
            "name": "compile_coq",
            "description": "使用 coqc 编译器编译指定的 .v Coq 源文件。必须提供完整的绝对路径（如 D:\\Vscode\\py\\my_agent_new\\coq_output\\proof.v）。成功时返回编译通过的信息，失败时返回具体错误信息以便修正。",
            "parameters": {
                "type": "object",
                "properties": {
                    "filename": {"type": "string", "description": "要编译的 .v 文件的绝对路径（如 D:\\Vscode\\py\\my_agent_new\\coq_output\\proof.v）"}
                },
                "required": ["filename"]
            }
        }
    },
    {
        "type": "function",
        "function": {
            "name": "get_coq_proof_state",
            "description": "获取 .v 文件中当前的 Coq 证明状态，包括已有的假设条件（hypotheses）和待证明的目标（goals）。必须提供完整的绝对路径。编译失败后，使用此工具查看出错位置的证明上下文，以便分析问题并调整证明策略。",
            "parameters": {
                "type": "object",
                "properties": {
                    "filename": {"type": "string", "description": "要查看证明状态的 .v 文件的绝对路径"}
                },
                "required": ["filename"]
            }
        }
    }
]

# 基础工具集（Fast）：仅创建、修改、编译 — 覆盖简单证明的完整流程
basic_tools = [t for t in tools if t["function"]["name"] in (
    "create_text_file", "replace_in_file", "compile_coq"
)]



# ========== 3. FSM 状态机：控制任务终止条件 ==========
# 只有编译成功才能结束任务；编译失败或未编译则强制继续
class AgentFSM:
    INIT = "INIT"                    # 任务初始状态
    EXECUTING = "EXECUTING"          # 正在执行中（文件已修改，编译结果已过期）
    COMPILE_SUCCESS = "COMPILE_SUCCESS"  # 最近一次编译成功
    COMPILE_FAIL = "COMPILE_FAIL"    # 最近一次编译失败

    def __init__(self):
        self.state = AgentFSM.INIT

    def on_file_modified(self):
        """文件被创建/修改后，之前的编译结果失效。"""
        self.state = AgentFSM.EXECUTING

    def on_compile_success(self):
        self.state = AgentFSM.COMPILE_SUCCESS

    def on_compile_fail(self):
        self.state = AgentFSM.COMPILE_FAIL

    @property
    def can_finish(self):
        """只有最近一次编译成功，任务才可以结束。"""
        return self.state == AgentFSM.COMPILE_SUCCESS

    @property
    def must_continue(self):
        """编译失败或从未编译过，LLM 声称完成时需强制继续。"""
        return self.state != AgentFSM.COMPILE_SUCCESS


# ========== 3a. 任务完成检查器：验证目标定理是否全部完成 ==========

class TaskCompletionChecker:
    """任务完成检查器：验证目标文件中指定定理是否全部完成证明。"""

    def __init__(self):
        self.target_file = None
        self.target_theorems = []
        self.start_theorem = None
        self.end_theorem = None

    def parse_task(self, user_message: str):
        """从用户消息中解析目标任务：目标文件 + 定理范围。"""
        # 1. 提取目标文件路径
        match = re.search(r'([A-Za-z]:\\[^\s]*\.v)', user_message)
        if match:
            self.target_file = match.group(1)

        if not self.target_file:
            return

        # 2. 提取定理范围：支持 到/至/和...之间/与...之间/从...到/to/between...and
        # 使用 [A-Za-z0-9_] 而非 \w，因为 Python 3 的 \w 会匹配中文字符
        range_patterns = [
            # --- 定理前缀 + 到/至 ---
            r'定理\s*([A-Za-z0-9_]+[\']?)\s*到\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            r'定理\s*([A-Za-z0-9_]+[\']?)\s*至\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            # --- 定理前缀 + 和/与（不含"之间"：支持"定理A和定理B的证明"等）---
            r'定理\s*([A-Za-z0-9_]+[\']?)\s*和\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            r'定理\s*([A-Za-z0-9_]+[\']?)\s*与\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            # --- 定理前缀 + 和/与...之间 ---
            r'定理\s*([A-Za-z0-9_]+[\']?)\s*和\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)\s*之间',
            r'定理\s*([A-Za-z0-9_]+[\']?)\s*与\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)\s*之间',
            # --- 无前缀 + 和/与（不含"之间"）---
            r'([A-Za-z0-9_]+[\']?)\s*和\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            r'([A-Za-z0-9_]+[\']?)\s*与\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            # --- 无前缀 + 到/至 + 之间 ---
            r'([A-Za-z0-9_]+[\']?)\s*到\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)\s*之间',
            r'([A-Za-z0-9_]+[\']?)\s*至\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)\s*之间',
            # --- 无前缀 + 和/与 + 之间 ---
            r'([A-Za-z0-9_]+[\']?)\s*和\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)\s*之间',
            r'([A-Za-z0-9_]+[\']?)\s*与\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)\s*之间',
            # --- 无前后缀 + 到/至 ---
            r'([A-Za-z0-9_]+[\']?)\s*到\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            r'([A-Za-z0-9_]+[\']?)\s*至\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            # --- 从...到 ---
            r'从\s*([A-Za-z0-9_]+[\']?)\s*到\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            # --- 英文 ---
            r'([A-Za-z0-9_]+[\']?)\s+to\s+([A-Za-z0-9_]+[\']?)',
            r'between\s+([A-Za-z0-9_]+[\']?)\s+and\s+([A-Za-z0-9_]+[\']?)',
        ]
        for pattern in range_patterns:
            m = re.search(pattern, user_message)
            if m:
                self.start_theorem = m.group(1)
                self.end_theorem = m.group(2)
                break

        # 3. 如果没有范围，检查是否是单个定理
        if not self.start_theorem:
            single_patterns = [
                r'定理\s*([A-Za-z0-9_]+[\']*)\s*(?:的证明|证明)',
                r'证明\s*定理\s*([A-Za-z0-9_]+[\']*)',
            ]
            for pattern in single_patterns:
                m = re.search(pattern, user_message)
                if m:
                    self.start_theorem = m.group(1)
                    self.end_theorem = m.group(1)
                    break

        # 4. 枚举范围内的所有定理
        if self.start_theorem and self.end_theorem:
            self._enumerate_theorems()
        elif self.target_file:
            # 检查用户是否明确要求全部定理（而非范围描述中附带"所有定理"字样）
            has_range_language = bool(
                re.search(r'[A-Za-z0-9_]+\s*[到至]\s*[A-Za-z0-9_]+', user_message) or
                re.search(r'[A-Za-z0-9_]+\s*[和与]\s*[A-Za-z0-9_]+\s*之间', user_message) or
                re.search(r'[A-Za-z0-9_]+\s+to\s+[A-Za-z0-9_]+', user_message) or
                re.search(r'从\s*[A-Za-z0-9_]+\s*到', user_message) or
                re.search(r'之间', user_message)
            )
            if (not has_range_language and
                re.search(r'所有(?:定理|theorem)|全部(?:定理|theorem)|all\s+(?:theorems|lemmas)',
                          user_message, re.IGNORECASE)):
                self._enumerate_all_theorems()

    def _enumerate_theorems(self):
        """在目标文件中定位 start/end 定理，提取范围内的所有定理名。"""
        all_theorems = self._find_all_theorems()
        if not all_theorems:
            return
        try:
            start_idx = all_theorems.index(self.start_theorem)
            end_idx = all_theorems.index(self.end_theorem)
        except ValueError:
            self.target_theorems = []
            return
        if start_idx <= end_idx:
            self.target_theorems = all_theorems[start_idx:end_idx + 1]
        else:
            self.target_theorems = all_theorems[end_idx:start_idx + 1]

    def _enumerate_all_theorems(self):
        """枚举目标文件中的所有定理。"""
        self.target_theorems = self._find_all_theorems()

    def _find_all_theorems(self):
        """在目标文件中查找所有定理/引理声明，返回名称列表。"""
        if not self.target_file:
            return []
        try:
            with open(self.target_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception:
            return []
        theorems = []
        for m in re.finditer(
            r'^\s*(?:Theorem|Lemma|Corollary|Proposition|Example|Remark|Fact)\s+([A-Za-z0-9_]+[\']?)',
            content, re.MULTILINE
        ):
            theorems.append(m.group(1))
        return theorems

    def count_completed(self):
        """返回目标定理中已完成证明（Proof. ... Qed.）的数量。"""
        if not self.target_file or not self.target_theorems:
            return 0
        try:
            with open(self.target_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception:
            return 0
        count = 0
        for thm_name in self.target_theorems:
            if self._check_theorem_proof(content, thm_name) == "complete":
                count += 1
        return count

    def check_completion(self):
        """
        检查目标文件中所有目标定理是否已完成证明。

        Returns:
            (all_done: bool, details: str)
        """
        if not self.target_file:
            return True, ""

        if not self.target_theorems:
            return True, ""

        try:
            with open(self.target_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return False, f"无法读取目标文件 {self.target_file}：{e}"

        incomplete = []
        admitted_theorems = []

        for thm_name in self.target_theorems:
            status = self._check_theorem_proof(content, thm_name)
            if status == "incomplete":
                incomplete.append(thm_name)
            elif status == "admitted":
                admitted_theorems.append(thm_name)

        compile_ok = self._compile_check()

        details_parts = []
        all_done = True

        completed = len(self.target_theorems) - len(incomplete) - len(admitted_theorems)
        details_parts.append(
            f"进度：{completed}/{len(self.target_theorems)} 个定理已完成。"
        )

        if incomplete:
            all_done = False
            details_parts.append(
                f"以下定理证明不完整（缺少 Proof. ... Qed.）：{', '.join(incomplete[:10])}"
            )

        if admitted_theorems:
            all_done = False
            details_parts.append(
                f"以下定理使用了 Admitted：{', '.join(admitted_theorems[:10])}"
            )

        if not compile_ok:
            all_done = False
            details_parts.append("目标文件编译未通过。")

        if all_done:
            details_parts.append(
                f"所有 {len(self.target_theorems)} 个目标定理均已完成证明且编译通过。"
            )

        return all_done, "\n".join(details_parts)

    def _check_theorem_proof(self, content, thm_name):
        """
        检查单个定理的证明状态。

        Returns: "complete" | "incomplete" | "admitted" | "not_found"
        """
        pattern = (
            rf'^\s*(?:Theorem|Lemma|Corollary|Proposition|Example|Remark|Fact)\s+'
            rf'{re.escape(thm_name)}\b'
        )
        m = re.search(pattern, content, re.MULTILINE)
        if not m:
            return "not_found"

        thm_start = m.start()
        after_thm = content[thm_start:]

        # 找到下一个定理声明作为边界
        next_thm = re.search(
            r'^\s*(?:Theorem|Lemma|Corollary|Proposition|Example|Remark|Fact)\s+[A-Za-z0-9_]+',
            after_thm[len(m.group()):],
            re.MULTILINE
        )

        if next_thm:
            thm_content = after_thm[:len(m.group()) + next_thm.start()]
        else:
            thm_content = after_thm

        if re.search(r'\bAdmitted\.', thm_content):
            return "admitted"

        if re.search(r'\bProof\.', thm_content) and re.search(r'\b(?:Qed|Defined)\.', thm_content):
            return "complete"

        return "incomplete"

    def _compile_check(self):
        """独立编译检查目标文件（不依赖 FSM 状态）。"""
        if not self.target_file or not os.path.isfile(self.target_file):
            return False
        coqc_path = r"D:\Coq\bin\coqc.exe"
        if not os.path.isfile(coqc_path):
            return False
        try:
            result = subprocess.run(
                [coqc_path, self.target_file],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=30
            )
            return result.returncode == 0
        except Exception:
            return False

    def has_target(self):
        """是否指定了目标任务（目标文件 + 目标定理范围）。"""
        return self.target_file is not None and len(self.target_theorems) > 0

    def format_context(self):
        """生成任务上下文描述，用于注入 Agent Prompt。"""
        if not self.has_target():
            return ""
        thm_list = ', '.join(self.target_theorems[:10])
        if len(self.target_theorems) > 10:
            thm_list += f' ... （共 {len(self.target_theorems)} 个）'
        return (
            f"## 任务目标\n"
            f"- 目标文件：{self.target_file}\n"
            f"- 目标定理（{len(self.target_theorems)} 个）：{thm_list}\n"
            f"- 所有定理必须完成 Proof. ... Qed. 且编译通过，任务才算完成。\n"
        )


# ========== 4. 新增：尝试历史、错误分类、相似度检测 ==========

def _similarity(text1, text2):
    """简单的编辑距离相似度（0~1），用于检测重复修改。"""
    if text1 == text2:
        return 1.0
    if not text1 or not text2:
        return 0.0
    # 去除空白后比较
    t1 = ''.join(text1.split())
    t2 = ''.join(text2.split())
    if t1 == t2:
        return 0.95  # 仅空白差异，视为高度重复
    if len(t1) < 5 or len(t2) < 5:
        return 0.0
    # Levenshtein 距离
    m, n = len(t1), len(t2)
    if m > n:
        t1, t2 = t2, t1
        m, n = n, m
    prev = list(range(n + 1))
    for i in range(1, m + 1):
        curr = [i] + [0] * n
        for j in range(1, n + 1):
            cost = 0 if t1[i - 1] == t2[j - 1] else 1
            curr[j] = min(prev[j] + 1, curr[j - 1] + 1, prev[j - 1] + cost)
        prev = curr
    distance = prev[n]
    max_len = max(m, n)
    return 1.0 - distance / max_len


class AttemptHistory:
    """记录每次修改尝试，支持重复检测和失败分析。"""

    def __init__(self, max_history=3):
        self.attempts = []  # [{round, edit, compile_error, goal, error_category, raw_response}]
        self.max_history = max_history

    def record(self, round_num, edit="", compile_error="", goal="", error_category="",
               raw_llm_response=""):
        if not compile_error:
            return  # 只记录失败尝试，编译成功不记录
        self.attempts.append({
            "round": round_num,
            "edit": edit,
            "compile_error": compile_error,
            "goal": goal,
            "error_category": error_category,
            "raw_response": raw_llm_response[:500] if raw_llm_response else ""
        })
        if len(self.attempts) > self.max_history:
            self.attempts = self.attempts[-self.max_history:]

    def get_recent_failures(self, n=3):
        """返回最近 n 次失败尝试（不含编译成功的）。"""
        failures = [a for a in self.attempts if a["compile_error"]]
        return failures[-n:]

    def get_last_error(self):
        for a in reversed(self.attempts):
            if a["compile_error"]:
                return a
        return None

    def get_last_goal(self):
        for a in reversed(self.attempts):
            if a["goal"]:
                return a["goal"]
        return None

    def is_duplicate(self, new_edit, threshold=0.92):
        """检查 new_edit 是否与最近尝试高度相似。"""
        recent_edits = [a["edit"] for a in self.attempts[-5:] if a["edit"]]
        for old_edit in recent_edits:
            if _similarity(old_edit, new_edit) >= threshold:
                return True
        return False

    def count_consecutive_same_error_category(self):
        """连续出现相同错误类型的次数。"""
        if len(self.attempts) < 2:
            return 1
        count = 1
        last_cat = self.attempts[-1]["error_category"]
        if not last_cat:
            return 1
        for a in reversed(self.attempts[:-1]):
            if a["error_category"] == last_cat:
                count += 1
            else:
                break
        return count

    def count_consecutive_identical_error(self):
        """连续出现完全相同 compile_error 的次数。"""
        if len(self.attempts) < 2:
            return 1
        count = 1
        last_err = self.attempts[-1]["compile_error"]
        if not last_err:
            return 1
        for a in reversed(self.attempts[:-1]):
            if a["compile_error"] == last_err:
                count += 1
            else:
                break
        return count

    def count_consecutive_similar_edits(self, threshold=0.92):
        """连续生成相似修改的次数。"""
        if len(self.attempts) < 2:
            return 1
        count = 1
        last_edit = self.attempts[-1]["edit"]
        if not last_edit:
            return 1
        edits = [a["edit"] for a in self.attempts[-8:] if a["edit"]]
        for old_edit in reversed(edits[:-1]):
            if _similarity(old_edit, last_edit) >= threshold:
                count += 1
            else:
                break
        return count

    def should_force_strategy_change(self):
        """连续3次同类错误 → 需要切换策略。"""
        return self.count_consecutive_same_error_category() >= 3

    def should_early_stop(self):
        """提前终止：相同错误≥5次 或 相似修改≥3次。"""
        if self.count_consecutive_identical_error() >= 5:
            return True, "连续 5 次出现完全相同的编译错误，已陷入重复修改循环。"
        if self.count_consecutive_similar_edits(threshold=0.90) >= 3:
            return True, "连续 3 次生成几乎相同的修改，已陷入重复修改循环。"
        return False, ""

    def format_recent_failures(self, n=3):
        """将最近失败尝试格式化为 Prompt 文本。"""
        failures = self.get_recent_failures(n)
        if not failures:
            return ""
        lines = [
            "\n=== 以下修改已尝试过且失败，请不要再次生成相同或近似的修改 ===\n"
        ]
        for i, a in enumerate(failures):
            error_cat = f"（{a['error_category']}）" if a['error_category'] else ""
            edit_text = a['edit']
            if len(edit_text) > 400:
                edit_text = edit_text[:400] + "\n...[截断]"
            error_text = a['compile_error']
            if len(error_text) > 600:
                error_text = error_text[:600] + "\n...[截断]"
            lines.append(
                f"Attempt {i + 1} (第 {a['round']} 轮):\n"
                f"  修改内容：\n{edit_text}\n"
                f"  错误类型：{error_cat}\n"
                f"  错误信息：\n{error_text}\n"
            )
        lines.append("=== 失败历史结束 ===\n")
        return "\n".join(lines)

    def format_strategy_hint(self):
        """当同一思路反复失败时，生成策略切换提示。"""
        last_cat = self.attempts[-1]["error_category"] if self.attempts else ""
        count = self.count_consecutive_same_error_category()

        if count < 3:
            return ""

        hints = {
            "Rewrite Failure": (
                "\n【策略提示】连续多次 Rewrite 失败。请放弃 rewrite，考虑以下策略：\n"
                "- destruct / induction（对关键变量做归纳）\n"
                "- inversion（反转假设中的等式）\n"
                "- apply（直接应用已有引理）\n"
                "- assert（引入中间引理）\n"
                "- remember（给复杂表达式命名）\n"
                "- generalize dependent（泛化依赖假设）\n"
            ),
            "Unification Error": (
                "\n【策略提示】连续多次 Unification 失败。请检查：\n"
                "- 是否混淆了不同但相似的变量名？\n"
                "- 类型参数是否传递完整？\n"
                "- 是否需要对某个变量做 unfold / simpl 展开？\n"
                "- 尝试使用 apply ... with (...) 明确指定参数\n"
            ),
            "Type Error": (
                "\n【策略提示】连续多次类型错误。请检查：\n"
                "- 函数/引理的参数类型是否匹配？\n"
                "- 是否需要调整归纳假设的表述？\n"
                "- 尝试使用 Check / About 理解目标类型\n"
            ),
            "Tactic Failure": (
                "\n【策略提示】连续多次策略执行失败。请：\n"
                "- 先用 get_coq_proof_state 查看当前 Goal 和 hypotheses\n"
                "- 确认策略的前提条件是否满足\n"
                "- 考虑从更高层次重新组织证明结构\n"
            ),
        }

        for key, hint in hints.items():
            if key in (last_cat or ""):
                return hint

        return (
            "\n【策略提示】连续多次尝试均以相同类型失败。\n"
            "请放弃当前证明思路，重新设计证明策略，而不是继续微调已有代码。\n"
        )


# ========== 4a. 编译错误分类 ==========

def classify_compile_error(error_text):
    """将 coqc 编译错误分类，返回 (类别, 简短描述)。"""
    if not error_text:
        return "Unknown Error", error_text

    error_lower = error_text.lower()

    categories = [
        ("Syntax Error", [
            r"syntax\s*error", r"illegal\s+character", r"unexpected\s+token",
            r"parse\s+error", r"ill[- ]?formed", r"expects",
            r"lexing:", r"illegal\s+begin",
        ]),
        ("Universe Error", [
            r"universe\s+inconsistency", r"universe\s+\w+\s+and\s+\w+\s+are\s+not",
            r"cannot\s+enforce", r"would\s+be\s+higher",
        ]),
        ("Cannot Find Reference", [
            r"cannot\s+find", r"unknown\s+identifier", r"not\s+found",
            r"reference\s+.*not", r"has\s+not\s+been\s+declared",
            r"unbound\s+reference",
        ]),
        ("Type Error", [
            r"type\s+error", r"has\s+type", r"is\s+not\s+a",
            r"incorrect\s+type", r"wrong\s+type", r"ill[- ]?typed",
            r"should\s+be\s+of\s+type", r"expected\s+type",
        ]),
        ("Unification Error", [
            r"unif", r"cannot\s+unify", r"unable\s+to\s+unify",
            r"cannot\s+be\s+applied", r"cannot\s+infer",
            r"different\s+instances", r"incompatible",
        ]),
        ("Rewrite Failure", [
            r"rewrite", r"found\s+no\s+subterm", r"no\s+subterm",
            r"does\s+not\s+match", r"setoid\s+rewrite",
        ]),
        ("Missing Identifier", [
            r"not\s+a\s+defined", r"undeclared", r"unbound",
            r"not\s+declared", r"unknown\s+variable",
        ]),
        ("Tactic Failure", [
            r"tactic\s+failure", r"no\s+more\s+subgoals",
            r"no\s+such\s+goal", r"cannot\s+apply",
            r"not\s+a\s+valid", r"does\s+not\s+apply",
            r"not\s+the\s+right", r"wrong\s+number\s+of",
            r"not\s+enough", r"too\s+many",
        ]),
        ("Incomplete Proof", [
            r"incomplete", r"attempt\s+to\s+save", r"still\s+have\s+subgoals",
            r"unsolved", r"remaining\s+subgoals", r"not\s+finished",
            r"admitted",
        ]),
    ]

    for category, regexes in categories:
        for regex in regexes:
            if re.search(regex, error_lower):
                # 提取错误的简短描述（第一行有效信息）
                lines = [l.strip() for l in error_text.split('\n') if l.strip()]
                short = lines[0] if lines else error_text[:200]
                if len(short) > 300:
                    short = short[:300] + "..."
                return category, short

    lines = [l.strip() for l in error_text.split('\n') if l.strip()]
    short = lines[0] if lines else error_text[:200]
    return "Unknown Error", short[:300]


# ========== 4b. 定理边界提取 ==========

def extract_theorem_context(content, error_line=None):
    """
    从文件中提取当前待证明定理及其上下文（前后各~25行）。
    返回用于构造 Prompt 的精简代码片段，不返回整个文件。
    """
    lines = content.split('\n')

    # 确定焦点行
    if error_line is not None and 1 <= error_line <= len(lines):
        focus = error_line - 1  # 转为0-index
    else:
        # 查找最后一个 Admitted 或 Proof. 之后的内容
        focus = None
        for i in range(len(lines) - 1, -1, -1):
            if re.match(r'^\s*(Admitted|Abort)\.', lines[i]):
                focus = i
                break
        if focus is None:
            # 查找最后一个 Proof.
            for i in range(len(lines) - 1, -1, -1):
                if re.match(r'^\s*Proof\.', lines[i]):
                    focus = i
                    break
        if focus is None:
            focus = len(lines) - 1

    # 向上查找当前 theorem/lemma 的声明
    theorem_start = None
    theorem_line_text = ""
    for i in range(focus, -1, -1):
        stripped = lines[i].strip()
        if re.match(
            r'^\s*(Theorem|Lemma|Corollary|Proposition|Example|Remark|Fact|Goal)\s+',
            stripped
        ):
            theorem_start = i
            theorem_line_text = stripped
            break

    if theorem_start is None:
        # 没找到 theorem，返回最后 60 行
        context_start = max(0, len(lines) - 60)
        return {
            "snippet": '\n'.join(lines[context_start:]),
            "theorem_line": "",
            "theorem_start": 0,
            "context_start": context_start,
            "context_end": len(lines),
            "focus_line": focus,
        }

    # 向前取 25 行作为上下文，向后取到 focus + 10 行
    context_start = max(0, theorem_start - 25)
    context_end = min(len(lines), max(focus + 10, theorem_start + 30))

    snippet = '\n'.join(lines[context_start:context_end])

    return {
        "snippet": snippet,
        "theorem_line": theorem_line_text,
        "theorem_start": theorem_start,
        "context_start": context_start,
        "context_end": context_end,
        "focus_line": focus,
    }


# ========== 4c. Planner 与 Executor Prompt 构建 ==========

# 存储最近一次 Planner 生成的证明计划，Executor 可复用
_plan_cache = {"plan": "", "theorem_line": "", "round": 0}

def build_planner_prompt(theorem_context, goal_text, user_goal):
    """构造 Planner 的 Prompt：分析 Goal，给出证明计划。"""
    return (
        "你是一位 Coq 定理证明策略专家。请分析以下证明目标并给出详细的证明计划。\n\n"
        f"## 待证明定理\n{theorem_context['theorem_line']}\n\n"
        f"## 当前 Goal\n{goal_text}\n\n"
        f"## 周围代码上下文\n```coq\n{theorem_context['snippet']}\n```\n\n"
        f"## 用户目标\n{user_goal}\n\n"
        "请输出证明计划（不要输出完整代码，只需策略步骤）：\n"
        "1. 核心思路（induction / destruct / rewrite / apply / assert / ...）\n"
        "2. 关键步骤序列（策略名称 + 作用简要说明）\n"
        "3. 可能的风险点和备选方案\n\n"
        "注意：只给出计划，不要写完整的 Coq 代码。"
    )


def build_executor_prompt(theorem_context, goal_text, compile_error, error_category,
                          attempt_history, filename="", mode="fast"):
    """构造 Executor 的 Prompt。Fast 模式仅含 theorem + error；Advanced 模式含完整上下文。"""
    parts = []

    if mode == "fast":
        # ---- Fast Mode: 最小 Prompt ----
        parts.append(
            "你是一个 Coq 证明执行者。使用 replace_in_file 修改证明脚本，"
            "然后用 compile_coq 验证。\n"
        )
        parts.append(
            "## 修改范围限制\n"
            "- 只能修改 Proof. 到 Qed. 之间的证明脚本\n"
            "- 禁止修改已通过编译的定义和引理\n"
            "- 使用 replace_in_file 做精准修改\n"
        )
        parts.append(f"## 待证明定理\n{theorem_context['theorem_line']}\n")
        if compile_error and error_category:
            parts.append(
                f"## 编译错误（{error_category}）\n```\n{compile_error}\n```\n"
            )
        parts.append("请修改证明并编译验证。")
        return "\n\n".join(parts)

    # ---- Advanced Mode: 完整上下文 ----
    parts.append(
        "你是一个 Coq 证明执行者。请根据证明计划、当前 Goal 和错误信息修改代码。\n"
    )
    parts.append(
        "## 修改范围限制\n"
        "- 只能修改当前定理内部的证明脚本（Proof. 到 Qed. 之间）\n"
        "- 禁止修改已证明通过的 theorem/lemma\n"
        "- 禁止修改 Definitions、Inductive、Fixpoint 等定义\n"
        "- 一次只修改一个 theorem 的证明\n"
    )
    parts.append(f"## 当前工作文件\n{filename}\n")
    parts.append(f"## 待证明定理\n{theorem_context['theorem_line']}\n")
    parts.append(
        f"## 定理上下文\n```coq\n{theorem_context['snippet']}\n```\n"
    )
    if goal_text:
        goal_short = goal_text[:800] + "\n...[截断]" if len(goal_text) > 800 else goal_text
        parts.append(f"## 当前证明状态\n```\n{goal_short}\n```\n")
    if compile_error and error_category:
        parts.append(
            f"## 编译错误（{error_category}）\n```\n{compile_error}\n```\n"
        )
    strategy_hint = attempt_history.format_strategy_hint()
    if strategy_hint:
        parts.append(strategy_hint)
    failure_text = attempt_history.format_recent_failures(n=3)
    if failure_text:
        parts.append(failure_text)
    if _plan_cache["plan"]:
        plan_short = _plan_cache["plan"]
        if len(plan_short) > 800:
            plan_short = plan_short[:800] + "\n...[截断]"
        parts.append(f"## Planner 证明计划\n{plan_short}\n")
    parts.append(
        "## 执行指令\n"
        "1. 使用 replace_in_file 修改证明脚本\n"
        "2. 使用 compile_coq 验证\n"
        "3. 如果编译失败，分析错误原因后尝试新方案\n"
        "4. 不要重复之前已失败的修改\n"
    )
    return "\n\n".join(parts)


# ========== 5. 规划阶段：代码分析 + 三种证明方案 ==========

def _extract_file_path(text: str):
    """从用户消息中提取 .v 文件的绝对路径。"""
    match = re.search(r'([A-Za-z]:\\[^\s]*\.v)', text)
    if match:
        return match.group(1)
    return None

def _read_file_safe(path: str):
    """安全读取文件，返回内容或 None。"""
    try:
        with open(path, 'r', encoding='utf-8') as f:
            return f.read()
    except Exception:
        return None

def _run_planner(theorem_context, goal_text, compile_error):
    """
    【按需 Planner】仅在进入 Advanced Mode 时调用。
    输入精简上下文（定理 + Goal + 错误），输出简短证明计划。
    """
    prompt = (
        "你是一位 Coq 证明策略专家。请分析以下证明目标并给出简短的证明计划。\n\n"
        f"## 待证明定理\n{theorem_context['theorem_line']}\n\n"
        f"## 当前错误\n{compile_error}\n\n"
        f"## 当前 Goal\n{goal_text}\n\n"
        f"## 上下文\n```coq\n{theorem_context['snippet']}\n```\n\n"
        "请输出简短的证明计划（3-5 步策略序列，不要完整代码）：\n"
        "1. 核心思路\n"
        "2. 关键策略步骤\n"
        "3. 可能的备选方案\n"
    )
    print("【Planner】正在分析证明策略...")
    response = client.chat.completions.create(
        model="deepseek-v4-flash",
        messages=[{"role": "user", "content": prompt}],
        reasoning_effort="high",
        extra_body={"thinking": {"type": "enabled"}},
    )
    plan = response.choices[0].message.content
    print(f"【Planner】计划：\n{plan}")
    return plan


# ========== 5. 对话压缩：控制上下文长度 ==========

def _find_safe_cut(messages, target_recent):
    """确保 recent 切片不从 tool 消息开始（tool 消息需要前面的 assistant 消息配对）。"""
    if len(messages) <= target_recent:
        return 0
    cut = len(messages) - target_recent
    # tool 消息不能独立存在，向前找到最近的 assistant/user/system 消息
    while cut > 0 and messages[cut]["role"] == "tool":
        cut -= 1
    return cut

def compress_messages(messages, max_messages=25, keep_recent=8):
    """压缩消息列表，控制上下文长度"""
    if len(messages) <= max_messages:
        return messages

    system_msg = messages[0] if messages[0]["role"] == "system" else None
    initial_user = messages[1] if len(messages) > 1 and messages[1]["role"] == "user" else None

    cut = _find_safe_cut(messages, keep_recent)
    middle = messages[(2 if system_msg else 1):cut]
    recent = messages[cut:]

    # 扫描中间消息，只提取关键信息
    latest_compile_error = None
    latest_proof_state = None
    compile_attempts = 0
    replace_attempts = 0
    filename = None

    for msg in middle:
        content = msg.get("content", "")
        if msg["role"] == "tool":
            if "已成功创建文件" in content:
                m = re.search(r'《(.+?)》', content)
                if m:
                    filename = m.group(1)
            elif "编译失败" in content:
                compile_attempts += 1
                latest_compile_error = content
            elif "编译成功" in content:
                compile_attempts += 1
            elif "替换成功" in content:
                replace_attempts += 1
            elif "证明状态" in content or "coqtop" in content:
                latest_proof_state = content

    # 同时对 recent 中的重复错误做去重：只保留最后一次编译失败和最后一次证明状态
    recent = _dedup_recent_tool_results(recent)

    # 构建压缩摘要，初始用户消息过长则截断
    summary_parts = ["[会话压缩 — 以下为之前交互的摘要]"]
    if filename:
        summary_parts.append(f"工作文件: {filename}")
    summary_parts.append(f"历史编译尝试: {compile_attempts} 次, 文件修改: {replace_attempts} 次")

    if latest_compile_error:
        err = latest_compile_error
        if len(err) > 600:
            err = err[:600] + "\n...[截断]"
        summary_parts.append(f"\n--- 最新编译错误 ---\n{err}")

    if latest_proof_state:
        state = latest_proof_state
        if len(state) > 600:
            state = state[:600] + "\n...[截断]"
        summary_parts.append(f"\n--- 最新证明状态 ---\n{state}")

    compressed = []
    if system_msg:
        compressed.append(system_msg)
    if initial_user:
        user_content = initial_user.get("content", "")
        if len(user_content) > 2000:
            # 截断过长的初始消息（通常含证明方案），保留首 tail 各一半
            half = 1000
            initial_user = dict(initial_user)
            initial_user["content"] = user_content[:half] + "\n\n...[中间内容已截断]...\n\n" + user_content[-half:]
        compressed.append(initial_user)
    compressed.append({"role": "user", "content": "\n".join(summary_parts)})
    compressed.extend(recent)

    print(f"【压缩】消息从 {len(messages)} 条压缩至 {len(compressed)} 条")
    return compressed


def _dedup_recent_tool_results(recent):
    last_compile_fail_idx = -1
    last_proof_state_idx = -1
    for i, msg in enumerate(recent):
        if msg["role"] != "tool":
            continue
        content = msg.get("content", "")
        if "编译失败" in content:
            last_compile_fail_idx = i
        elif "证明状态" in content or "coqtop" in content:
            last_proof_state_idx = i

    cleaned = []
    for i, msg in enumerate(recent):
        if msg["role"] == "tool":
            content = msg.get("content", "")
            if "编译失败" in content and i != last_compile_fail_idx:
                cleaned.append(dict(msg, content="[已省略旧的编译错误，最新错误见上下文摘要]"))
                continue
            if ("证明状态" in content or "coqtop" in content) and i != last_proof_state_idx:
                cleaned.append(dict(msg, content="[已省略旧的证明状态，最新状态见上下文摘要]"))
                continue
        cleaned.append(msg)
    return cleaned


# ========== 5b. Advanced Mode 多条件触发辅助函数 ==========

CONTEXT_TOKEN_THRESHOLD = 500000  # 上下文 token 阈值


def _estimate_token_count(messages):
    """估算消息列表的 token 数量。中文/Coq 混合文本按 ~2.5 字符/token 估算。"""
    total_chars = sum(len(str(m.get("content", ""))) for m in messages)
    return int(total_chars / 2.5)


def _get_trigger_reason(consecutive_failures, completed_count, estimated_tokens):
    """返回触发 Advanced Mode 的原因列表。"""
    reasons = []
    if consecutive_failures >= 10:
        reasons.append(f"连续编译失败 {consecutive_failures} 次")
    if completed_count > 0 and completed_count % 5 == 0:
        reasons.append(f"已完成 {completed_count} 个定理")
    if estimated_tokens > CONTEXT_TOKEN_THRESHOLD:
        reasons.append(
            f"上下文长度 {estimated_tokens} tokens 超过阈值 {CONTEXT_TOKEN_THRESHOLD}"
        )
    return reasons


def _build_task_scale_advanced_entry(completed_count, total_count, work_filename):
    """任务规模触发：已完成多个定理，压缩上下文并整理状态。"""
    parts = [
        "【系统通知】已进入 Advanced Mode（任务规模触发）。\n",
        f"当前已完成 {completed_count}/{total_count} 个定理。",
        "为避免上下文过长，已对历史对话进行压缩，同时保留关键证明状态。\n",
        "## 当前进度摘要",
    ]
    if work_filename:
        parts.append(f"- 工作文件：{work_filename}")
    parts.append(f"- 已完成定理数：{completed_count}")
    parts.append(f"- 剩余定理数：{total_count - completed_count}")
    parts.append(
        "\n请继续完成剩余定理的证明。使用 read_coq_file 查看当前文件状态，"
        "然后逐个完成剩余定理。"
    )
    return "\n".join(parts)


def _build_context_length_advanced_entry(estimated_tokens, threshold, work_filename):
    """上下文长度触发：上下文过长，需要压缩。"""
    parts = [
        "【系统通知】已进入 Advanced Mode（上下文长度触发）。\n",
        f"当前上下文约 {estimated_tokens} tokens，超过阈值 {threshold} tokens。",
        "已对历史对话进行压缩以控制上下文长度，同时保留关键证明状态。\n",
    ]
    if work_filename:
        parts.append(f"工作文件：{work_filename}")
    parts.append("\n请基于压缩后的上下文继续当前证明工作。")
    return "\n".join(parts)


def _apply_compression(messages, entry_msg):
    messages = compress_messages(messages, max_messages=20, keep_recent=6)
    messages.append({"role": "user", "content": entry_msg})
    new_tokens = _estimate_token_count(messages)
    print(f"【压缩】压缩后上下文约 {new_tokens} tokens")
    return messages, new_tokens


# ========== 6. 执行阶段：形式化证明 ==========

def _build_fast_continue_prompt(last_error, last_error_category):
    """Fast Mode 继续提示：仅含错误信息。"""
    parts = ["编译尚未通过，请修改代码后使用 compile_coq 验证。"]
    if last_error:
        parts.append(f"\n错误类型：{last_error_category or 'Unknown'}")
        parts.append(f"错误内容：\n{last_error}")
    parts.append("\n请使用 replace_in_file 修改证明，然后 compile_coq 编译。")
    return "\n\n".join(parts)


def _build_advanced_continue_prompt(attempt_history, last_error, last_error_category, last_goal):
    """Advanced Mode 继续提示：含 Goal + 失败历史 + 策略提示 + Planner 计划。"""
    parts = ["编译尚未通过，请修改代码后使用 compile_coq 验证。"]

    if last_error:
        parts.append(f"\n错误类型：{last_error_category or 'Unknown'}")
        parts.append(f"错误内容：\n{last_error}")

    if last_goal and "No focused proof" not in last_goal:
        goal_short = last_goal[:600] + "\n...[截断]" if len(last_goal) > 600 else last_goal
        parts.append(f"\n当前证明状态：\n{goal_short}")

    strategy_hint = attempt_history.format_strategy_hint()
    if strategy_hint:
        parts.append(strategy_hint)

    failure_text = attempt_history.format_recent_failures(n=3)
    if failure_text:
        parts.append(failure_text)

    if _plan_cache["plan"]:
        plan_short = _plan_cache["plan"]
        if len(plan_short) > 800:
            plan_short = plan_short[:800] + "\n...[截断]"
        parts.append(f"\nPlanner 证明计划：\n{plan_short}")

    parts.append("\n请使用 replace_in_file 修改证明，然后 compile_coq 编译。")
    return "\n\n".join(parts)


def _inject_executor_context(messages, attempt_history, work_filename, file_content_cache):

    if not work_filename:
        return messages

    # 获取文件内容
    if work_filename in file_content_cache:
        content = file_content_cache[work_filename]
    else:
        try:
            with open(work_filename, 'r', encoding='utf-8') as f:
                content = f.read()
            file_content_cache[work_filename] = content
        except Exception:
            return messages

    # 获取错误行号
    last_err = attempt_history.get_last_error()
    error_line = None
    if last_err and last_err["compile_error"]:
        match = re.search(r'line (\d+)', last_err["compile_error"])
        if match:
            error_line = int(match.group(1))

    # 提取定理上下文
    ctx = extract_theorem_context(content, error_line)

    # 获取当前 goal
    goal_text = attempt_history.get_last_goal() or ""

    # 获取最新错误
    last_error_text = ""
    last_error_cat = ""
    if last_err:
        last_error_text = last_err.get("compile_error", "")
        last_error_cat = last_err.get("error_category", "")

    executor_prompt = build_executor_prompt(
        theorem_context=ctx,
        goal_text=goal_text,
        compile_error=last_error_text,
        error_category=last_error_cat,
        attempt_history=attempt_history,
        filename=work_filename
    )

    # 追加到消息列表
    messages.append({
        "role": "user",
        "content": (
            "[上下文刷新] 以下是当前证明状态的摘要，请基于此继续工作：\n\n"
            f"{executor_prompt}"
        )
    })
    print(f"【上下文注入】已注入精简的 Executor 上下文（第 {len(messages)} 条消息）")
    return messages


def _build_advanced_mode_entry(attempt_history, last_error, last_error_category,
                               last_goal, work_filename):
    """构建进入 Advanced Mode 时的上下文注入消息。"""
    parts = [
        "【系统通知】已进入 Advanced Mode。以下为扩展上下文，请使用这些信息重新规划证明。\n"
    ]

    if last_error:
        parts.append(f"## 当前错误（{last_error_category or 'Unknown'}）\n```\n{last_error}\n```\n")

    if last_goal and "No focused proof" not in last_goal:
        goal_short = last_goal[:800] + "\n...[截断]" if len(last_goal) > 800 else last_goal
        parts.append(f"## 当前证明状态\n```\n{goal_short}\n```\n")

    strategy_hint = attempt_history.format_strategy_hint()
    if strategy_hint:
        parts.append(strategy_hint)

    failure_text = attempt_history.format_recent_failures(n=3)
    if failure_text:
        parts.append(failure_text)

    if _plan_cache["plan"]:
        plan_short = _plan_cache["plan"]
        if len(plan_short) > 800:
            plan_short = plan_short[:800] + "\n...[截断]"
        parts.append(f"## Planner 证明计划\n{plan_short}\n")

    if work_filename:
        parts.append(f"工作文件：{work_filename}")

    parts.append("请使用 replace_in_file 修改证明，然后 compile_coq 验证。不要重复之前的失败方案。")
    return "\n\n".join(parts)


# ========== 6b. 任务总结 Markdown 生成 ==========

def generate_task_summary(summary_data):
    """生成任务总结 Markdown 文件，保存到 RocqAgent_output。"""
    output_dir = r"D:\Vscode\py\RocqAgent_output"
    os.makedirs(output_dir, exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    summary_path = os.path.join(output_dir, f"task_summary_{timestamp}.md")

    start_time = summary_data.get("start_time", datetime.now())
    end_time = summary_data.get("end_time", datetime.now())
    duration = end_time - start_time

    target_file = summary_data.get("target_file", "N/A")
    target_theorems = summary_data.get("target_theorems", [])
    user_message = summary_data.get("user_message", "")
    final_status = summary_data.get("final_status", "UNKNOWN")
    compile_result = summary_data.get("compile_result", "UNKNOWN")
    total_iterations = summary_data.get("total_iterations", 0)
    comp_details = summary_data.get("completion_details", "")
    planner_called = summary_data.get("planner_called", False)
    work_filename = summary_data.get("work_filename", "")
    compile_errors = summary_data.get("compile_errors", [])
    early_stop = summary_data.get("early_stop_reason", None)
    max_iter_hit = summary_data.get("max_iterations_reached", False)

    # ---- 构建 Markdown ----
    lines = []
    lines.append("# Task Summary\n")

    lines.append("## 1. Basic Information")
    lines.append(f"- Task start time: {start_time.strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append(f"- Task end time: {end_time.strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append(f"- Duration: {duration}")
    lines.append(f"- User input: `{user_message}`\n")

    lines.append("## 2. Target Information")
    lines.append(f"- Target file: `{target_file}`")
    if target_theorems:
        lines.append(f"- Target theorems ({len(target_theorems)}): {', '.join(target_theorems)}")
    else:
        lines.append("- Target theorems: N/A")
    lines.append("- Completion requirement: All theorems must have Proof. ... Qed. and compile successfully.\n")

    lines.append("## 3. Execution Result")
    status_icon = {"SUCCESS": "SUCCESS", "INCOMPLETE": "INCOMPLETE", "FAILED": "FAILED"}.get(final_status, final_status)
    lines.append(f"- Final status: {status_icon}")
    lines.append(f"- Final compile result: {compile_result}")
    lines.append(f"- Total Agent iterations: {total_iterations}")
    if early_stop:
        lines.append(f"- Early stop reason: {early_stop}")
    if max_iter_hit:
        lines.append("- Warning: Reached maximum iterations limit.")
    lines.append("")

    lines.append("## 4. Proof Completion Status")
    if comp_details:
        lines.append(comp_details)
    else:
        lines.append("No completion check performed (no target specified).\n")

    lines.append("## 5. Execution Summary")
    if final_status == "SUCCESS":
        if target_theorems:
            lines.append(f"- Successfully completed {len(target_theorems)} target theorems in `{target_file}`.")
        else:
            lines.append("- Task completed successfully (compilation passed).")
    elif final_status == "INCOMPLETE":
        lines.append("- Task was not fully completed before exit.")
        if max_iter_hit:
            lines.append(f"- Reached maximum iterations ({total_iterations}).")
    elif final_status == "FAILED":
        lines.append("- Task failed to complete.")
        if early_stop:
            lines.append(f"- Failure reason: {early_stop}")

    if planner_called:
        lines.append("- Planner was invoked during execution.")
    if work_filename:
        lines.append(f"- Primary work file: `{work_filename}`")
    if compile_errors:
        unique_errors = list(dict.fromkeys(compile_errors))[-5:]
        lines.append(f"- Compile errors encountered: {len(compile_errors)} total")
        lines.append("- Last unique errors:")
        for err in unique_errors:
            err_short = err[:200].replace('\n', ' ')
            lines.append(f"  - {err_short}")

    lines.append("")

    md_content = "\n".join(lines)

    with open(summary_path, 'w', encoding='utf-8') as f:
        f.write(md_content)

    print(f"\n任务总结已保存至: {summary_path}")
    return summary_path


def agent_run(user_message: str):
    # -------- 任务计时 --------
    task_start_time = datetime.now()

    # -------- 任务退出追踪 --------
    final_status = None          # SUCCESS | INCOMPLETE | FAILED
    completion_details = ""      # TaskCompletionChecker 返回的详情
    early_stop_reason = None     # 提前终止原因

    # -------- Task Completion Checker --------
    task_checker = TaskCompletionChecker()
    task_checker.parse_task(user_message)
    if task_checker.has_target():
        print(f"【任务解析】目标文件：{task_checker.target_file}")
        thm_preview = ', '.join(task_checker.target_theorems[:5])
        if len(task_checker.target_theorems) > 5:
            thm_preview += '...'
        print(f"【任务解析】目标定理（{len(task_checker.target_theorems)} 个）：{thm_preview}")

    # -------- FSM 初始化 --------
    fsm = AgentFSM()

    # -------- 状态追踪 --------
    attempt_history = AttemptHistory(max_history=3)
    consecutive_failures = 0       # 连续编译失败次数
    in_advanced_mode = False       # 是否已进入 Advanced Mode
    planner_called = False         # Planner 是否已在本轮证明中调用过
    completed_theorem_count = 0    # 已完成定理计数
    _prev_completed_count = 0      # 上一轮完成的定理数（用于检测新完成）
    _advanced_triggered_by_scale = False  # 是否由任务规模触发
    _last_compression_tokens = 0    # 上次压缩后的 token 数（防止重复触发）
    _last_compression_round = 0     # 上次压缩时的迭代轮次
    _last_edit = ""
    _last_compile_error = ""
    _last_error_category = ""
    _last_goal = ""
    _work_filename = task_checker.target_file  # 优先使用用户指定的目标文件
    _raw_llm_response = ""
    file_content_cache = {}

    # -------- Fast Mode：最小化 System Prompt --------
    task_context = task_checker.format_context()
    system_prompt = (
        "你是一个 Coq 证明助手。\n\n"
        "## 工作流程\n"
        "1. 使用 read_coq_file 读取目标文件，了解现有代码和待证明定理\n"
        "2. 使用 replace_in_file 修改目标文件中的证明脚本（Proof. 到 Qed. 之间）\n"
        "3. 使用 compile_coq 编译验证\n"
        "4. 编译成功不代表任务完成！所有指定定理必须完成证明\n\n"
        + (task_context + "\n" if task_context else "") +
        "## 修改限制\n"
        "- 只能修改 Proof. 到 Qed. 之间的证明脚本\n"
        "- 禁止修改已通过编译的定义和引理\n"
        "- 使用 replace_in_file 做精准修改\n"
        "- 如果用户指定了目标文件，必须使用绝对路径修改该文件，不要创建新的 .v 文件\n\n"
        "## 任务完成标准\n"
        "- 目标文件中所有用户指定的定理都必须有完整的 Proof. ... Qed. 证明\n"
        "- 不允许留下 Admitted\n"
        "- 仅当所有定理证明完成且编译通过后，任务才算完成\n"
        "- 编译成功只是中间步骤，不是任务终点\n\n"
        "## 注意\n"
        "- 先编译再下结论，编译成功前不要声称完成\n"
        "- 如果连续失败，尝试不同的策略而不是微调\n"
        "- 不要通过创建新文件来绕过任务要求"
    )

    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": user_message}
    ]
    print("开始任务 [Fast Mode]")

    max_iterations = 200
    iteration = 0

    while iteration < max_iterations:
        iteration += 1
        mode_label = "Advanced" if in_advanced_mode else "Fast"
        print(f"--- 第 {iteration} 轮 [{mode_label} Mode] 连续失败={consecutive_failures} ---")

        # ======== 提前终止检测 ========
        should_stop, stop_reason = attempt_history.should_early_stop()
        if should_stop:
            print(f"\n{'='*60}")
            print(f"【提前终止】{stop_reason}")
            print("当前证明陷入重复修改。建议重新规划证明策略。")
            print(f"{'='*60}\n")
            messages.append({
                "role": "user",
                "content": (
                    f"【系统通知】{stop_reason}\n"
                    "当前证明陷入重复修改。建议重新规划证明策略。"
                )
            })
            final_status = "FAILED"
            early_stop_reason = stop_reason
            break

        # ======== 进入 Advanced Mode 检测（多条件触发）========
        estimated_tokens = _estimate_token_count(messages)
        # 上下文长度触发需满足：超过阈值 且 （首次压缩 或 比上次压缩后增长 30%）
        context_trigger = (
            estimated_tokens > CONTEXT_TOKEN_THRESHOLD
            and (_last_compression_tokens == 0
                 or estimated_tokens > _last_compression_tokens * 1.3)
        )
        if not in_advanced_mode and (
            consecutive_failures >= 10
            or (completed_theorem_count > 0 and completed_theorem_count % 5 == 0
                and completed_theorem_count > _prev_completed_count)
            or context_trigger
        ):
            in_advanced_mode = True
            failure_trigger = consecutive_failures >= 10
            scale_trigger = (
                completed_theorem_count > 0 and completed_theorem_count % 5 == 0
                and completed_theorem_count > _prev_completed_count
            )

            trigger_reasons = _get_trigger_reason(
                consecutive_failures, completed_theorem_count, estimated_tokens
            )
            print(
                "【模式切换】Fast → Advanced Mode"
                f"（触发原因：{'; '.join(trigger_reasons)}）"
            )

            # 获取 Proof State（所有触发类型都需要）
            if _work_filename:
                try:
                    goal_result = get_coq_proof_state(_work_filename)
                    if "No focused proof" not in goal_result:
                        _last_goal = goal_result
                    print("【Advanced】已获取 Proof State")
                except Exception as e:
                    print(f"【Advanced】获取 Proof State 失败：{e}")

            # ---- 失败触发：运行 Planner + 注入完整错误上下文 ----
            if failure_trigger:
                if not planner_called and _work_filename:
                    try:
                        content = _read_file_safe(_work_filename)
                        if content:
                            file_content_cache[_work_filename] = content
                            ctx = extract_theorem_context(content)
                            plan = _run_planner(
                                ctx, _last_goal or "", _last_compile_error
                            )
                            _plan_cache["plan"] = plan or ""
                            planner_called = True
                            print("【Advanced】Planner 已完成")
                    except Exception as e:
                        print(f"【Advanced】Planner 失败：{e}")

                advanced_ctx_prompt = _build_advanced_mode_entry(
                    attempt_history, _last_compile_error, _last_error_category,
                    _last_goal, _work_filename or ""
                )
                messages.append({"role": "user", "content": advanced_ctx_prompt})

            # ---- 任务规模 / 上下文长度触发：压缩上下文 ----
            else:
                if scale_trigger:
                    _advanced_triggered_by_scale = True
                    _prev_completed_count = completed_theorem_count
                    total = (
                        len(task_checker.target_theorems)
                        if task_checker.has_target() else 0
                    )
                    entry_msg = _build_task_scale_advanced_entry(
                        completed_theorem_count, total, _work_filename or ""
                    )
                else:
                    entry_msg = _build_context_length_advanced_entry(
                        estimated_tokens, CONTEXT_TOKEN_THRESHOLD,
                        _work_filename or ""
                    )
                # === 统一压缩入口：所有 compression 路径必须通过 _apply_compression ===
                messages, estimated_tokens = _apply_compression(messages, entry_msg)
                _last_compression_tokens = estimated_tokens
                _last_compression_round = iteration
                # 更新缓存中的文件内容
                if _work_filename:
                    content = _read_file_safe(_work_filename)
                    if content:
                        file_content_cache[_work_filename] = content

        # ======== 消息压缩（仅 Advanced Mode）========
        if in_advanced_mode and len(messages) > 25:
            messages = compress_messages(messages)

        # ======== LLM 调用 ========
        print("大模型(deepseek-v4-flash)思考中")
        response = client.chat.completions.create(
            model="deepseek-v4-flash",
            messages=messages,
            reasoning_effort="high",
            extra_body={"thinking": {"type": "enabled"}},
            tools=tools,
            tool_choice="auto"
        )

        msg = response.choices[0].message
        _raw_llm_response = msg.content or ""
        print(f"大模型的回复：{msg.content}")
        messages.append(msg.model_dump(exclude_none=True))

        # ======== 无工具调用：FSM + 任务完成检查 ========
        if not msg.tool_calls:
            if fsm.can_finish:
                # 编译通过，检查任务是否真正完成
                if task_checker.has_target():
                    all_done, details = task_checker.check_completion()
                    print(f"【任务检查】{details}")
                    if all_done:
                        print(f"【FSM】所有定理已完成且编译通过，任务完成。")
                        final_status = "SUCCESS"
                        completion_details = details
                        break
                    else:
                        print(f"【FSM】编译通过但定理未全部完成，强制继续。")
                        messages.append({
                            "role": "user",
                            "content": (
                                f"【系统通知】编译通过但任务未完成！\n{details}\n\n"
                                f"请继续证明剩余定理。必须使用绝对路径修改目标文件 "
                                f"{task_checker.target_file}，不要创建新的 .v 文件。"
                                f"使用 read_coq_file 查看目标文件中待证明的定理，"
                                f"然后使用 replace_in_file 完成证明。"
                            )
                        })
                        fsm.on_file_modified()  # 重置状态，强制继续
                        continue
                else:
                    print(f"【FSM】编译已验证通过，任务完成。")
                    final_status = "SUCCESS"
                    break
            else:
                print(f"【FSM】尚未成功编译，强制继续。")
                if in_advanced_mode:
                    continue_prompt = _build_advanced_continue_prompt(
                        attempt_history, _last_compile_error,
                        _last_error_category, _last_goal
                    )
                else:
                    continue_prompt = _build_fast_continue_prompt(
                        _last_compile_error, _last_error_category
                    )
                messages.append({"role": "user", "content": continue_prompt})
                continue

        # ======== 执行工具调用 ========
        for tool_call in msg.tool_calls:
            func_name = tool_call.function.name
            try:
                args = json.loads(tool_call.function.arguments)
            except json.JSONDecodeError as e:
                print(f"【JSON修复】tool_call 参数 JSON 解析失败：{e}")
                try:
                    from json_repair import repair_json
                    repaired_args = repair_json(tool_call.function.arguments)
                    args = json.loads(repaired_args)
                    print("【JSON修复】修复成功")
                except Exception as repair_err:
                    print(f"【JSON修复】修复失败：{repair_err}")
                    messages.append({
                        "role": "tool",
                        "tool_call_id": tool_call.id,
                        "content": (
                            f"工具调用参数 JSON 解析失败且无法修复。"
                            f"请重新生成合法的 JSON 参数。"
                        )
                    })
                    continue

            if func_name == "create_text_file":
                fsm.on_file_modified()
                _work_filename = os.path.join(COQ_OUTPUT_DIR, args["filename"])
                edit_content = args.get("content", "")

                if iteration > 2 and attempt_history.is_duplicate(edit_content):
                    print("【重复检测】创建内容与历史尝试高度相似，已被拒绝。")
                    messages.append({
                        "role": "tool",
                        "tool_call_id": tool_call.id,
                        "content": "【重复修改警告】此修改与之前已失败的尝试高度相似。请设计一个不同的证明方案。"
                    })
                    continue

                print("正在创建文件并写入内容...")
                result = create_text_file(args["filename"], edit_content)
                _last_edit = edit_content
                messages.append({"role": "tool", "tool_call_id": tool_call.id, "content": result})

            elif func_name == "replace_in_file":
                fsm.on_file_modified()
                filename = args["filename"]
                _work_filename = filename if os.path.isabs(filename) else os.path.join(COQ_OUTPUT_DIR, filename)

                old_str = args.get("old_string", "")
                new_str = args.get("new_string", "")
                _last_edit = f"replace:\n  old: {old_str[:400]}\n  new: {new_str[:400]}"

                if iteration > 2 and attempt_history.is_duplicate(_last_edit):
                    print("【重复检测】此修改与历史尝试高度相似，已被拒绝。")
                    messages.append({
                        "role": "tool",
                        "tool_call_id": tool_call.id,
                        "content": "【重复修改警告】此修改与之前已失败的尝试高度相似。请设计一个不同的证明方案。"
                    })
                    continue

                print("正在替换文件中的内容...")
                result = replace_in_file(args["filename"], old_str, new_str)
                messages.append({"role": "tool", "tool_call_id": tool_call.id, "content": result})

            elif func_name == "read_coq_file":
                print("正在读取 Coq 文件...")
                result = read_coq_file(args["filename"])
                safe_path = (
                    os.path.join(COQ_OUTPUT_DIR, args["filename"])
                    if not os.path.isabs(args["filename"])
                    else args["filename"]
                )
                if safe_path not in file_content_cache and os.path.isfile(safe_path):
                    try:
                        with open(safe_path, 'r', encoding='utf-8') as f:
                            file_content_cache[safe_path] = f.read()
                    except Exception:
                        pass
                messages.append({"role": "tool", "tool_call_id": tool_call.id, "content": result})

            elif func_name == "compile_coq":
                print("正在编译 Coq 文件...")
                result = compile_coq(args["filename"])
                messages.append({"role": "tool", "tool_call_id": tool_call.id, "content": result})

                if "编译成功" in result:
                    fsm.on_compile_success()
                    consecutive_failures = 0
                    # 更新已完成定理计数
                    if task_checker.has_target():
                        new_count = task_checker.count_completed()
                        if new_count > completed_theorem_count:
                            completed_theorem_count = new_count
                            total = len(task_checker.target_theorems)
                            print(
                                f"【进度】已完成 {completed_theorem_count}/{total} 个定理"
                            )
                    if in_advanced_mode:
                        in_advanced_mode = False
                        planner_called = False
                        _advanced_triggered_by_scale = False
                        print("【模式切换】Advanced → Fast Mode（编译成功）")
                    print(f"【FSM】编译成功")
                else:
                    fsm.on_compile_fail()
                    consecutive_failures += 1
                    print(f"【FSM】编译失败（连续 {consecutive_failures} 次）")

                    # 错误分类
                    error_category, error_short = classify_compile_error(result)
                    _last_compile_error = error_short
                    _last_error_category = error_category
                    print(f"【错误分类】{error_category}")

                    # 仅在 Advanced Mode 自动获取 Proof State
                    if in_advanced_mode and _work_filename:
                        try:
                            goal_result = get_coq_proof_state(_work_filename)
                            if "No focused proof" not in goal_result:
                                _last_goal = goal_result
                        except Exception:
                            pass

                    # 记录失败（仅失败尝试）
                    attempt_history.record(
                        round_num=iteration,
                        edit=_last_edit,
                        compile_error=error_short,
                        goal=_last_goal,
                        error_category=error_category,
                        raw_llm_response=_raw_llm_response
                    )

                    # Advanced Mode：连续同类错误 → 策略提示
                    if in_advanced_mode:
                        same_cat_count = attempt_history.count_consecutive_same_error_category()
                        if same_cat_count >= 3:
                            print("【策略警告】连续同类错误 ≥ 3 次")
                            strategy_hint = attempt_history.format_strategy_hint()
                            if strategy_hint:
                                messages.append({"role": "user", "content": strategy_hint})

            elif func_name == "get_coq_proof_state":
                print("正在获取 Coq 证明状态...")
                result = get_coq_proof_state(args["filename"])
                _last_goal = result
                messages.append({"role": "tool", "tool_call_id": tool_call.id, "content": result})

            else:
                messages.append({
                    "role": "tool",
                    "tool_call_id": tool_call.id,
                    "content": f"{func_name}是未知工具，请重新确认！"
                })
                break

    if iteration >= max_iterations and final_status is None:
        final_status = "INCOMPLETE"
        print(f"警告: 已达到最大迭代次数({max_iterations})，任务可能未完成。")

    # -------- 生成任务总结 Markdown --------
    if final_status is None:
        final_status = "UNKNOWN"

    task_end_time = datetime.now()

    # 最终编译结果
    if fsm.state == AgentFSM.COMPILE_SUCCESS:
        compile_result = "PASS"
    elif fsm.state == AgentFSM.COMPILE_FAIL:
        compile_result = "FAIL"
    else:
        compile_result = "UNKNOWN"

    summary_data = {
        "start_time": task_start_time,
        "end_time": task_end_time,
        "user_message": user_message,
        "target_file": task_checker.target_file or "N/A",
        "target_theorems": task_checker.target_theorems,
        "final_status": final_status,
        "compile_result": compile_result,
        "total_iterations": iteration,
        "completion_details": completion_details,
        "planner_called": planner_called,
        "work_filename": _work_filename or "",
        "compile_errors": [a["compile_error"] for a in attempt_history.attempts if a.get("compile_error")],
        "early_stop_reason": early_stop_reason,
        "max_iterations_reached": iteration >= max_iterations,
    }
    generate_task_summary(summary_data)

    # 清理 Coq 会话
    _invalidate_coq_session()



print("您好！欢迎来到Rocq编程智能体！")

while True:
    user_input = input("请输入指令:")
    if user_input == "":
        print("请勿输入空消息！")
    else:
        break

agent_run(user_input)
