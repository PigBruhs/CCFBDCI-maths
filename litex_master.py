import os
import requests

SILICONFLOW_API_URL = "https://api.siliconflow.cn/v1/chat/completions"
SILICONFLOW_MODEL = "Pro/deepseek-ai/DeepSeek-V3.1-Terminus"
REQUEST_TIMEOUT = 60  # seconds
token='sk-zvhwnuezxothhkbprbgjiuvrxpraxsjoonrhsbubghmfbblf'


def litex_master(nl_problem: str) -> str:
    """
    将 nl_problem 与预设 prompt 拼接，调用 SiliconFlow Chat Completions 生成结果并返回（不做任何清洗）。
    """

    prompt = (
        "你是一个擅长使用Litex（版本v0.1.11-beta）格式的数学家。你将会收到若干数学问题的自然语言描述。"
        "你将会按照示例中的格式，将nl_problem中描述的问题转换成litex格式的命题陈述，"
        "并生成完整的、可执行的证明脚本。请严格按照示例进行输出。请按照要求填写注释。\n"
        "请注意：formal_code中不能有作弊代码，必须是完整的数学形式化证明（不能使用know）！！！"
        "请严格参考示例输出！！！不要使用markdown的格式符号！！！（如**header** 应为header）"
        "输出格式：header:除题干、形式化证明核心逻辑（主定理）以外的环境代码、引理等。如Lean中的import、open、lemma、子定理部分；及Litex中的import、know、prop、fn部分。"
        "formal_statement:形式化题干。question部分，即主定理的问题部分不含证明逻辑。如 Lean 中的主 theorem 到 := 部分；及Litex中的claim到prove部分。"
        "formal_code:代码（全）。格式要求："
        "1.不能有转义问题；"
        "2.核心逻辑有注释；"
        "3.不能有作弊代码，必须是完整的数学形式化证明（如Lean的sorry、假设及Litex的know等）。"
        "示例输入：nl_problem: Three cubes have edges of lengths 4,5 and 6 .\n\n"
        "The average (mean) of their volumes is\n(A) 120\n(B) 125\n(C) 1125\n(D) 261\n(E) 135\n\n"
        "![](https://cdn.mathpix.com/cropped/2024_04_20_ac36362783317e0251fdg-104.jpg?height=249&width=379&top_left_y=1220&top_left_x=1293) "
        "示例输出：    formal_statement: forall e1, e2, e3, v1, v2, v3, partial_sum, total_sum, avg N_pos:\n"
        "        e1 = 4\n        e2 = 5\n        e3 = 6\n        v1 = e1 ^ 3\n        v2 = e2 ^ 3\n        v3 = e3 ^ 3\n"
        "        partial_sum = v1 + v2\n        total_sum = partial_sum + v3\n        avg = total_sum / 3\n        =>:\n"
        "            avg = 135, formal_code: claim:\n"
        "    forall e1, e2, e3, v1, v2, v3, partial_sum, total_sum, avg N_pos:\n"
        "        e1 = 4\n        e2 = 5\n        e3 = 6\n        v1 = e1 ^ 3\n        v2 = e2 ^ 3\n        v3 = e3 ^ 3\n"
        "        partial_sum = v1 + v2\n        total_sum = partial_sum + v3\n        avg = total_sum / 3\n        =>:\n"
        "            avg = 135\n    prove:\n"
        "        v1 = 4 ^ 3\n        v1 = 64\n\n        v2 = 5 ^ 3\n        v2 = 125\n\n        v3 = 6 ^ 3\n        v3 = 216\n\n"
        "        partial_sum = v1 + v2\n        partial_sum = 64 + 125\n        partial_sum = 189\n\n"
        "        total_sum = partial_sum + v3\n        total_sum = 189 + 216\n        total_sum = 405\n\n"
        "        avg = total_sum / 3\n        avg = 405 / 3\n        avg = 135"
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
    print(litex_master(demo_problem))
