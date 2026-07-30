import json
import re
import subprocess
import os
from datetime import datetime
from openai import OpenAI

# ========== 1. 创建一个本地客户端实例，把客户端指向 DeepSeek，用于与deepseek通信 ==========
client = OpenAI(
    api_key=" ",           # 替换成你自己的 key
    base_url="https://api.deepseek.com"       # 大模型公司的网址
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

# 用于创建文件并写入一些内容的函数工具
def create_text_file(filename, content):
    safe, err = _safe_write_path(filename)
    if err:
        return err
    with open(safe, 'w', encoding='utf-8') as f:
        f.write(content)
    return f"已成功创建文件《{safe}》（绝对路径）。如需编译，请使用 compile_coq 并传入此完整路径。"

# 替换文件中的指定内容（第二次及之后的修改使用此工具，而非重写整个文件）
def replace_in_file(filename, old_string, new_string):
    safe, err = _safe_write_path(filename)
    if err:
        return err
    if not os.path.isfile(safe):
        return f"文件《{safe}》不存在，请先用 create_text_file 创建文件。"
    with open(safe, 'r', encoding='utf-8') as f:
        content = f.read()
    if old_string not in content:
        return f"替换失败！在文件《{safe}》中未找到要替换的内容。\n要替换的文本：\n{old_string[:500]}"
    new_content = content.replace(old_string, new_string, 1)
    with open(safe, 'w', encoding='utf-8') as f:
        f.write(new_content)
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
        return f"编译失败！文件《{safe}》存在错误：\n{error_output}"

# 获取Coq证明状态的工具——用coqtop交互式获取当前条件和证明目标
def get_coq_proof_state(filename):
    coqtop_path = r"D:\Coq\bin\coqtop.exe"
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

    # 将文件内容通过 stdin 喂给 coqtop，-quiet 抑制启动信息
    try:
        result = subprocess.run(
            [coqtop_path, "-quiet"],
            input=content,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=30
        )
    except subprocess.TimeoutExpired:
        return "获取证明状态超时（30 秒）。文件可能包含死循环或不终止的策略。"

    output = result.stdout.strip()
    stderr_output = result.stderr.strip()

    # 合并输出，优先展示有用的部分
    parts = []
    if output:
        parts.append(f"=== coqtop 输出（含证明状态） ===\n{output}")
    if stderr_output:
        parts.append(f"=== 错误/警告 ===\n{stderr_output}")
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
            "description": "替换已创建的 .v 文件中指定的文本片段。编译失败后应优先使用此工具做精准修改，而不是重写整个文件。只需提供纯文件名（如 my_proof.v），文件必须在 coq_output 会话目录下。old_string 必须与文件中的原文完全匹配（含缩进和换行），new_string 为替换后的内容。一次只替换一处匹配。",
            "parameters": {
                "type": "object",
                "properties": {
                    "filename": {"type": "string", "description": "要修改的 .v 文件名（纯文件名，不带路径，如 proof.v）"},
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


# ========== 4. 规划阶段：代码分析 + 三种证明方案 ==========

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

def planning_phase(file_content: str, user_goal: str) -> str:
    """
    【阶段一：分析与规划】
    将文件内容交给 LLM，要求其：
    1. 分析已有代码（类型定义、已有引理、依赖关系）
    2. 提出三种不同的证明思路
    3. 选出可行性最高的方案并说明理由

    此阶段不使用工具，纯推理。
    """
    planning_prompt = (
        "你是一位 Coq 定理证明专家。下面是待证明定理所在的文件内容，以及用户的目标。\n\n"
        "请严格按以下结构输出：\n\n"
        "## 一、代码分析\n"
        "- 文件中定义了哪些类型、函数、引理？\n"
        "- 待证明的定理依赖了哪些定义？\n"
        "- 有哪些已证明的引理可以复用？\n\n"
        "## 二、证明方案一\n"
        "- 核心思路：\n"
        "- 关键步骤（用 Coq 策略描述）：\n"
        "- 优点：\n"
        "- 风险/难点：\n\n"
        "## 三、证明方案二\n"
        "- 核心思路：\n"
        "- 关键步骤：\n"
        "- 优点：\n"
        "- 风险/难点：\n\n"
        "## 四、证明方案三\n"
        "- 核心思路：\n"
        "- 关键步骤：\n"
        "- 优点：\n"
        "- 风险/难点：\n\n"
        "## 五、方案选择\n"
        "- 推荐方案：方案X\n"
        "- 选择理由：（从可行性、简洁性、与已有代码的兼容性等角度说明）\n\n"
        "注意：方案之间应有本质区别（如不同的归纳策略、不同的化简方向、是否使用额外引理等），而不是同一思路的微小变体。\n\n"
        f"=== 文件内容 ===\n{file_content}\n=== 文件结束 ===\n\n"
        f"用户目标：{user_goal}"
    )

    print("【阶段一】正在进行代码分析与证明规划...")
    response = client.chat.completions.create(
        model="deepseek-v4-pro",
        messages=[{"role": "user", "content": planning_prompt}],
        reasoning_effort="high",
        extra_body={"thinking": {"type": "enabled"}},
    )
    plan = response.choices[0].message.content
    print(f"【阶段一】规划完成。\n{plan}")
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
    """
    压缩消息列表，控制上下文长度：
    - 保留 system 消息和初始 user 消息（含证明方案）
    - 扫描中间消息，仅保留：最新编译错误、最新证明状态、关键统计
    - 保留最近 N 条消息以维持对话连贯性
    """
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
    """
    在 recent 消息中，只保留最新的 compile_coq 失败结果和最新的 get_coq_proof_state 结果。
    旧的同类结果替换为简短占位符。
    """
    # 找到最后一次 compile_coq 失败的位置
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


# ========== 6. 执行阶段：形式化证明 ==========

def agent_run(user_message: str):
    global COQ_OUTPUT_DIR
    session_dir = os.path.join(COQ_OUTPUT_DIR, datetime.now().strftime("session_%Y%m%d_%H%M%S"))
    os.makedirs(session_dir, exist_ok=True)
    COQ_OUTPUT_DIR = session_dir
    print(f"本次运行文件将保存至: {session_dir}")

    # -------- FSM 初始化 --------
    fsm = AgentFSM()

    # -------- 阶段一：分析与规划（代码控制，不在 system prompt 中）--------
    file_path = _extract_file_path(user_message)
    file_content = _read_file_safe(file_path) if file_path else None

    if file_content:
        plan = planning_phase(file_content, user_message)
        # 将分析方案保存为 markdown 文件
        plan_path = os.path.join(session_dir, "proof_plan.md")
        with open(plan_path, 'w', encoding='utf-8') as f:
            f.write(f"# 证明方案分析\n\n")
            f.write(f"> 原始目标：{user_message}\n\n")
            f.write(plan)
        print(f"【阶段一】分析报告已保存至: {plan_path}")
        user_message_with_plan = (
            f"{user_message}\n\n"
            f"=== 以下是经过专家分析的证明方案（已选定推荐方案） ===\n"
            f"{plan}\n"
            f"=== 方案分析结束 ===\n\n"
            f"请按照上述选定的推荐方案，完成形式化证明。"
        )
    else:
        print("【阶段一】未在消息中找到有效的 .v 文件路径，跳过规划阶段。")
        user_message_with_plan = user_message

    # -------- 阶段二：形式化证明（执行阶段）--------
    messages = [
        {"role": "system", "content": (
            "你是一个 Coq 编程助手，运行在自动化 Agent 环境中。\n\n"
            "## 核心工作流程\n\n"
            "你的任务是将 Admitted 的定理补全为完整证明。按以下步骤操作：\n\n"
            "1. 使用 read_coq_file 读取目标 .v 文件（如果尚未读取）\n"
            "2. 使用 create_text_file 创建完整的 .v 文件，将所有 Admitted 替换为实际证明\n"
            "3. 使用 compile_coq 编译，失败则根据错误修改后重试，直到成功\n\n"
            "## 工具使用规则\n"
            "- create_text_file：传入纯文件名（如 my_theorem.v），文件保存到会话目录。**仅在首次创建文件时使用。**\n"
            "- replace_in_file：编译失败后修改文件时使用，传入纯文件名、要替换的原文和新文本。**从第二次修改开始必须用此工具，不要再重写整个文件。**\n"
            "- read_coq_file：传入绝对路径读取已有 .v 文件\n"
            "- compile_coq：传入绝对路径编译 .v 文件\n"
            "- get_coq_proof_state：传入绝对路径，用 coqtop 获取文件的证明状态（假设条件 + 证明目标）\n\n"
            "## 编译失败后的处理流程（重要）\n"
            "1. 先用 get_coq_proof_state 查看出错位置的证明状态（当前有哪些假设条件？要证明什么目标？）\n"
            "2. 根据证明状态分析为什么当前策略不适用\n"
            "3. 用 replace_in_file 精准修改出错的部分，然后重新编译。**不要用 create_text_file 重写整个文件。**\n\n"
            "## 禁止事项\n"
            "- 禁止输出代码片段让用户手动复制\n"
            "- 禁止只补部分 Admitted 而忽略其他\n"
            "- 禁止编译通过前声称完成\n"
            "- 必须生成完整独立的 .v 文件\n"
            "- 首次创建后，禁止再使用 create_text_file 重写整个文件，必须用 replace_in_file 做增量修改"
        )},
        {"role": "user", "content": user_message_with_plan}
    ]
    print("开始任务")
    max_iterations = 500  # 安全限制，防止无限循环
    iteration = 0
    while iteration < max_iterations:       # 达到最大迭代次数或任务完成时退出循环
        iteration += 1
        print(f"--- 第 {iteration} 轮 ---")

        # 定期压缩消息列表，只保留最新编译错误和证明状态
        if len(messages) > 25:
            messages = compress_messages(messages)

        # 创建变量接收大模型返回的消息 此处的 client.chat.completions.create() 函数就是与大模型直接通信的核心代码
        # model 表示与哪个模型交互；messages 是发给模型的消息列表；tools是发给模型的工具列表；tool_choice是让大模型选择工具的方式，一般auto自动即可
        # 整个函数的返回结果就是大模型在这些参数(消息信息和提示词)下的回复
        print("大模型(deepseek-v4-pro)思考中")
        response = client.chat.completions.create(
            model="deepseek-v4-pro",      # 用 DeepSeek 的v4pro模型
            messages=messages,
            reasoning_effort="high",
            extra_body={"thinking":{"type":"enabled"}},
            tools=tools,
            tool_choice="auto"
        )

        # 大模型的回复不同于网络聊天窗口，依然是一个满足json格式的文本，里面包含有 自然语言回复和工具调用信息，即message片段
        print(f"\n\n\n大模型的response:{response}\n\n\n")

        # msg 用于获取大模型回复中的自然语言消息和工具调用信息  其中 response.choices[0].message.tool_calls 是工具列表，response.choices[0].message.content 是自然语言回复
        msg = response.choices[0].message

        # 先输出大模型的自然语言回复，给用户看
        print(f"大模型的回复：{msg.content}")
        # 把大模型的回复加入消息列表，作为历史消息记录（转为 dict 统一格式）
        messages.append(msg.model_dump(exclude_none=True))

        # 如果不含有工具字段，即没有tool_calls字段，也就没有调用工具
        # FSM 判断：只有编译成功才能结束任务，否则强制继续
        if not msg.tool_calls:
            if fsm.can_finish:
                print(f"【FSM】当前状态: {fsm.state} — 编译已验证通过，任务完成。")
                break
            else:
                print(f"【FSM】当前状态: {fsm.state} — 尚未成功编译，强制继续任务。")
                messages.append({
                    "role": "user",
                    "content": (
                        "你还未成功通过 compile_coq 编译验证。"
                        "请继续修改证明或创建文件，然后调用 compile_coq 直到编译成功。"
                        "只有 coqc 返回'编译成功'才算完成任务。"
                    )
                })
                continue

        # 若没有退出循环, 说明有工具要调用，开始按工具列表顺序依次调用工具
        for tool_call in msg.tool_calls:
            # 获取工具名称
            func_name = tool_call.function.name
            # 获取整体的参数字典，这里的json.loads将json文本中的相应内容解析成python字典
            args = json.loads(tool_call.function.arguments)

            # 如果工具是先前自定义的创建文件并写入内容的工具，则执行该功能，否则返回"未知工具"，告诉大模型工具用错了
            if func_name == "create_text_file":
                fsm.on_file_modified()   # 文件已修改，之前的编译结果失效
                print("正在创建文件并写入内容...")
                result = create_text_file(args["filename"], args["content"])

                # 把一次调用工具的信息加入到消息列表中作为历史消息
                messages.append({
                    "role": "tool",
                    "tool_call_id": tool_call.id,  # 工具的编号
                    "content": result              # 调用工具后给大模型的回复
                })

            elif func_name == "replace_in_file":
                fsm.on_file_modified()   # 文件已修改，之前的编译结果失效
                print("正在替换文件中的内容...")
                result = replace_in_file(args["filename"], args["old_string"], args["new_string"])
                messages.append({
                    "role": "tool",
                    "tool_call_id": tool_call.id,
                    "content": result
                })

            elif func_name == "read_coq_file":
                print("正在读取 Coq 文件...")
                result = read_coq_file(args["filename"])
                messages.append({
                    "role": "tool",
                    "tool_call_id": tool_call.id,
                    "content": result
                })

            elif func_name == "compile_coq":
                print("正在编译 Coq 文件...")
                result = compile_coq(args["filename"])
                messages.append({
                    "role": "tool",
                    "tool_call_id": tool_call.id,
                    "content": result
                })
                if "编译成功" in result:
                    fsm.on_compile_success()
                    print(f"【FSM】状态切换 → {fsm.state}")
                else:
                    fsm.on_compile_fail()
                    print(f"【FSM】状态切换 → {fsm.state}")

            elif func_name == "get_coq_proof_state":
                print("正在获取 Coq 证明状态...")
                result = get_coq_proof_state(args["filename"])
                messages.append({
                    "role": "tool",
                    "tool_call_id": tool_call.id,
                    "content": result
                })

            else:
                messages.append({
                    "role": "tool",
                    "tool_call_id": tool_call.id,  # 工具的编号
                    "content": f"{func_name}是未知工具，请重新确认！"              # 调用工具后给大模型的回复
                })
                break         # 一旦发现错误工具，跳出工具调用循环，即结束后续所有工具的调用

    if iteration >= max_iterations:
        print(f"警告: 已达到最大迭代次数({max_iterations})，任务可能未完成。请检查最终输出。")



print("您好！欢迎来到Coq编程智能体！我可以帮您创建 Coq 源文件并编译验证。请告诉我您想要证明的定理！")

while True:
    user_input = input("请输入指令:")
    if user_input == "":
        print("请勿输入空消息！")
    else:
        break

agent_run(user_input)
