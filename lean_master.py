import os
import requests

SILICONFLOW_API_URL = "https://api.siliconflow.cn/v1/chat/completions"
SILICONFLOW_MODEL = "Pro/deepseek-ai/DeepSeek-V3.1-Terminus"
REQUEST_TIMEOUT = 60  # seconds
token='sk-zvhwnuezxothhkbprbgjiuvrxpraxsjoonrhsbubghmfbblf'


def lean_master(nl_problem: str) -> str:
    """
    将 nl_problem 与预设 prompt 拼接，调用 SiliconFlow Chat Completions 生成结果并返回（不做任何清洗）。
    """

    prompt = (
        "你是一个擅长使用Lean（版本v4.21.0）格式的数学家。你将会收到若干数学问题的自然语言描述。"
        "你将会按照示例中的格式，将nl_problem中描述的问题转换成lean格式的命题陈述，"
        "并生成完整的、可执行的证明脚本。请严格按照示例进行输出。请按照要求填写注释。\n"
        "请注意：formal_code中不能有作弊代码，必须是完整的数学形式化证明（不能使用sorry,假设等）！！！"
        "请严格参考示例输出！！！不要使用markdown的格式符号！！！（如**header** 应为header）"
        "输出格式：header:除题干、形式化证明核心逻辑（主定理）以外的环境代码、引理等。如Lean中的import、open、lemma、子定理部分."
        "formal_statement:形式化题干。question部分，即主定理的问题部分不含证明逻辑。如 Lean 中的主 theorem 到 := 部分"
        "formal_code:代码（全）。"
        "格式要求："
        "1.不能有转义问题；"
        "2.核心逻辑有注释；"
        "3.不能有作弊代码，必须是完整的数学形式化证明（如Lean的sorry、假设等）。"
        "示例输入：nl_problem: Three cubes have edges of lengths 4,5 and 6 .\n\n"
        "The average (mean) of their volumes is\n(A) 120\n(B) 125\n(C) 1125\n(D) 261\n(E) 135\n\n"
        "![](https://cdn.mathpix.com/cropped/2024_04_20_ac36362783317e0251fdg-104.jpg?height=249&width=379&top_left_y=1220&top_left_x=1293) "
        "示例输出："    
        "header: import Mathlib.Data.Rat.Basic\nimport Mathlib.Tactic.NormNum\n\nnamespace CubeAverageVolume\n\n-- This namespace contains the formalization of the problem.\n-- The problem asks for the average volume of three cubes with edge lengths 4, 5, and 6.\n\n-- The volume of a cube with side length 's' is s³.\n-- The average is calculated as (4³ + 5³ + 6³) \/ 3.\n\n-- We use rational numbers (`ℚ`) to ensure precise division.\n\nend CubeAverageVolume\n\nopen CubeAverageVolume"
        "formal_statement: theorem main_theorem : (↑(4^3 : ℕ) + ↑(5^3 : ℕ) + ↑(6^3 : ℕ)) \/ (3 : ℚ) = (135 : ℚ) :="
        "formal_code: import Mathlib.Data.Rat.Basic\nimport Mathlib.Tactic.NormNum\n\nnamespace CubeAverageVolume\n\n-- This namespace contains the formalization of the problem.\n-- The problem asks for the average volume of three cubes with edge lengths 4, 5, and 6.\n\n-- The volume of a cube with side length 's' is s³.\n-- The average is calculated as (4³ + 5³ + 6³) \/ 3.\n\n-- We use rational numbers (`ℚ`) to ensure precise division.\n\nend CubeAverageVolume\n\nopen CubeAverageVolume\n\ntheorem main_theorem : (↑(4^3 : ℕ) + ↑(5^3 : ℕ) + ↑(6^3 : ℕ)) \/ (3 : ℚ) = (135 : ℚ) := by\n  -- The proof is a direct computation of the expression on the left-hand side.\n  -- We use the `norm_num` tactic, which is specialized for proving equalities\n  -- involving concrete numbers.\n  -- `norm_num` will evaluate the powers, the sum, and the division.\n  -- Calculation steps:\n  -- 1. Powers: 4^3 = 64, 5^3 = 125, 6^3 = 216.\n  -- 2. Sum: 64 + 125 + 216 = 405.\n  -- 3. Division: 405 \/ 3 = 135.\n  -- The tactic confirms that the left-hand side simplifies to 135, proving the theorem.\n  norm_num\n"
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
        "temperature": 0.4,
        "enable_thinking": False,
    }

    resp = requests.post(SILICONFLOW_API_URL, json=payload, headers=headers, timeout=REQUEST_TIMEOUT)
    if resp.status_code != 200:
        raise RuntimeError(f"SiliconFlow 调用失败: {resp.status_code} {resp.text}")

    data = resp.json()
    try:
        content = data["choices"][0]["message"].get("content", "")
    except Exception as e:
        raise RuntimeError(f"SiliconFlow 返回结构不符合预期: {e}; body={data}") from e

    return content


if __name__ == "__main__":
    # 简单测试：请先设置环境变量 `SILICONFLOW_API_TOKEN`
    demo_problem = (
        "Three cubes have edges of lengths 4,5 and 6 .\n\n"
        "The average (mean) of their volumes is\n(A) 120\n(B) 125\n(C) 1125\n(D) 261\n(E) 135\n\n"
        "![](https://cdn.mathpix.com/cropped/2024_04_20_ac36362783317e0251fdg-104.jpg?height=249&width=379&top_left_y=1220&top_left_x=1293)"
    )
    print(lean_master(demo_problem))
