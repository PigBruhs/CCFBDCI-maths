# python
from tqdm import tqdm
import requests

SILICONFLOW_API_URL = "https://api.siliconflow.cn/v1/chat/completions"
SILICONFLOW_MODEL = "deepseek-ai/DeepSeek-V3.1-Terminus"
# 连接超时 10s，读取超时 60s（可按需调整）
REQUEST_TIMEOUT = (10, 60)
token = 'sk-zvhwnuezxothhkbprbgjiuvrxpraxsjoonrhsbubghmfbblf'


def lean_master(nl_problem: str):
    """
    组包并请求 SiliconFlow，成功返回 (content, tokens, raw_json)。
    - 非 200：抛出 requests.HTTPError，异常上带 e.response，供上层解析状态码与消息。
    - 超时：保留 requests.ReadTimeout/ConnectTimeout 原异常。
    """
    prompt = (
        "你是一个擅长使用Lean（版本v4.21.0）格式的数学家。你将会收到若干数学问题的自然语言描述。"
        "你将会按照示例中的格式，将nl_problem中描述的问题转换成lean格式的命题陈述，"
        "并生成完整的、可执行的证明脚本。请严格按照示例进行输出。请按照要求填写注释。\n"
        "无需提供论述，仅输出header,formal_code与formal_statement!请勿使用markdown格式!"
        "输出格式：header:除题干、形式化证明核心逻辑（主定理）以外的环境代码、引理等。如Lean中的import、open、lemma、子定理部分."
        "formal_statement:形式化题干。question部分，即主定理的问题部分不含证明逻辑。如 Lean 中的主 theorem 到 := 部分"
        "formal_code:代码（全）。1.不能有转义问题；2.核心逻辑有注释；3.不能有作弊代码，必须是完整的数学形式化证明（如Lean的sorry、假设等）。"
        "示例输出："
        "header: import Mathlib.Data.Rat.Basic\nimport Mathlib.Tactic.NormNum\n\nnamespace CubeAverageVolume\n\n-- This namespace contains the formalization of the problem.\n-- The problem asks for the average volume of three cubes with edge lengths 4, 5, and 6.\n\n-- The volume of a cube with side length 's' is s³.\n-- The average is calculated as (4³ + 5³ + 6³) / 3.\n\n-- We use rational numbers (`ℚ`) to ensure precise division.\n\nend CubeAverageVolume\n\nopen CubeAverageVolume"
        "formal_statement: theorem main_theorem : (↑(4^3 : ℕ) + ↑(5^3 : ℕ) + ↑(6^3 : ℕ)) / (3 : ℚ) = (135 : ℚ) :="
        "formal_code: import Mathlib.Data.Rat.Basic\nimport Mathlib.Tactic.NormNum\n\nnamespace CubeAverageVolume\n\n-- This namespace contains the formalization of the problem.\n-- The problem asks for the average volume of three cubes with edge lengths 4, 5, and 6.\n\n-- The volume of a cube with side length 's' is s³.\n-- The average is calculated as (4³ + 5³ + 6³) / 3.\n\n-- We use rational numbers (`ℚ`) to ensure precise division.\n\nend CubeAverageVolume\n\nopen CubeAverageVolume\n\ntheorem main_theorem : (↑(4^3 : ℕ) + ↑(5^3 : ℕ) + ↑(6^3 : ℕ)) / (3 : ℚ) = (135 : ℚ) := by\n  -- Direct computation.\n  norm_num\n"
    )

    headers = {
        "Authorization": f"Bearer {token}",
        "Content-Type": "application/json",
    }
    payload = {
        "model": SILICONFLOW_MODEL,
        "messages": [
            {
                "role": "user",
                "content": prompt + "\n\n" + str(nl_problem),
            }
        ],
        "temperature": 0.65,
        "enable_thinking": False,
        "max_tokens": 16384,
    }

    try:
        resp = requests.post(
            SILICONFLOW_API_URL,
            json=payload,
            headers=headers,
            timeout=REQUEST_TIMEOUT,  # (connect_timeout, read_timeout)
        )
    except (requests.exceptions.ReadTimeout, requests.exceptions.ConnectTimeout) as e:
        # 读取或连接超时：直接抛出，供上层识别为超时并“停止以防继续消耗 tokens”
        raise
    except requests.exceptions.RequestException as e:
        # 其他 requests 级别错误（DNS、SSL 等）
        raise

    # 非 200：抛出 HTTPError，并保留 response（app.py 能读取 status/text/json）
    if resp.status_code != 200:
        # 构造更简洁的异常信息；详细体由上层读取 resp.text/resp.json
        msg = f"HTTP {resp.status_code} from SiliconFlow"
        raise requests.exceptions.HTTPError(msg, response=resp)

    # 200：解析结构
    try:
        data = resp.json()
    except Exception as e:
        # 返回非法 JSON，作为 HTTPError 抛给上层，附带 response
        raise requests.exceptions.HTTPError("Invalid JSON body", response=resp) from e

    try:
        content = data["choices"][0]["message"].get("content", "")
        tokens = data.get("usage", {}).get("total_tokens", 0)
    except Exception as e:
        tqdm.write(str(e))
        raise requests.exceptions.HTTPError("Unexpected response schema", response=resp) from e

    return content, tokens, data



if __name__ == "__main__":
    # 简单测试：请先设置环境变量 `SILICONFLOW_API_TOKEN`
    demo_problem = (
        "A sequence of integers $a_1, a_2, a_3,  \\ldots$ is chosen so that $a_n = a_{n - 1} - a_{n - 2}$ for each $n \\ge 3.$ What is the sum of the first $2001$ terms of this sequence if the sum of the first $1492$ terms is $1985, $ and the sum of the first $1985$ terms is $1492$?"
    )
    print(lean_master(demo_problem))
