# python
import argparse
import json
import sys
import time
import os
import socket
from typing import Any, Dict, Optional, Tuple
from tqdm import tqdm

from decoder_encoder import Jsonl_tackler
from lean_master import lean_master

# 尝试导入常见 HTTP/网络库，以识别其异常类型
try:
    import requests
    from requests import exceptions as req_exc
except Exception:
    requests = None
    class _Dummy:
        class Timeout(Exception): ...
        class ReadTimeout(Exception): ...
        class ConnectTimeout(Exception): ...
        class HTTPError(Exception): ...
    req_exc = _Dummy

try:
    import httpx
    from httpx import HTTPStatusError as _HTTPXStatusError  # noqa
    from httpx import ReadTimeout as _HTTPXReadTimeout      # noqa
    from httpx import ConnectTimeout as _HTTPXConnectTimeout  # noqa
except Exception:
    httpx = None
    class _HTTPXStatusError(Exception): ...
    class _HTTPXReadTimeout(Exception): ...
    class _HTTPXConnectTimeout(Exception): ...


def load_processed_ids(path: str) -> set:
    ids = set()
    if not os.path.exists(path):
        return ids
    try:
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                s = line.strip()
                if not s:
                    continue
                try:
                    obj = json.loads(s)
                except Exception:
                    continue
                for k in ("id", "rec_id"):
                    if k in obj:
                        ids.add(str(obj[k]))
                        break
    except Exception:
        pass
    return ids


def _extract_from_response(resp: Any) -> Tuple[Optional[int], Optional[str], Optional[Dict[str, Any]]]:
    status = getattr(resp, "status_code", None) or getattr(resp, "status", None)
    text = None
    data = None
    # 提取文本
    for attr in ("text", "content"):
        v = getattr(resp, attr, None)
        if isinstance(v, (bytes, bytearray)):
            try:
                text = v.decode("utf-8", errors="ignore")
            except Exception:
                text = None
            break
        if isinstance(v, str):
            text = v
            break
    # 提取 JSON
    if hasattr(resp, "json"):
        try:
            data = resp.json()
        except Exception:
            data = None
    return (int(status) if isinstance(status, int) else None), text, data


def _extract_status_and_payload(e: Exception) -> Tuple[Optional[int], str, Optional[str], Optional[Dict[str, Any]]]:
    status = None
    msg = str(e)
    resp_text = None
    resp_json = None

    # 直接属性
    for attr in ("status_code", "http_status", "status"):
        v = getattr(e, attr, None)
        if isinstance(v, int):
            status = v
            break

    # e.response
    resp = getattr(e, "response", None)
    if resp is not None:
        s, t, j = _extract_from_response(resp)
        status = status or s
        resp_text = t or resp_text
        resp_json = j or resp_json

    # httpx 兜底
    if resp is None and hasattr(e, "request") and hasattr(e, "response"):
        s, t, j = _extract_from_response(getattr(e, "response"))
        status = status or s
        resp_text = t or resp_text
        resp_json = j or resp_json

    return status, msg, resp_text, resp_json


def _is_timeout_error(e: Exception) -> bool:
    if isinstance(e, (TimeoutError, socket.timeout, _HTTPXReadTimeout, _HTTPXConnectTimeout, req_exc.ReadTimeout, req_exc.ConnectTimeout)):
        return True
    text = (str(e) or "").lower()
    if any(p in text for p in ("read timed out", "timed out", "timeout", "time out")):
        return True
    for sub in (getattr(e, "__cause__", None), getattr(e, "__context__", None)):
        if sub and _is_timeout_error(sub):
            return True
    return False


def _format_timeout_detail(e: Exception) -> str:
    lines = []
    cur = e
    seen = 0
    while cur and seen < 5:
        lines.append(f"{type(cur).__name__}: {str(cur)}")
        cur = getattr(cur, "__cause__", None) or getattr(cur, "__context__", None)
        seen += 1
    return " | ".join(lines)


def _classify_http_payload(status: Optional[int], resp_text: Optional[str], resp_json: Optional[Dict[str, Any]]) -> str:
    j = resp_json
    t = (resp_text or "").strip()

    def pick(d: Dict[str, Any], key: str, default: str = "") -> str:
        v = d.get(key)
        return v if isinstance(v, str) else default

    if status == 200 and isinstance(j, dict):
        content = ""
        usage = ""
        try:
            choices = j.get("choices") or []
            if choices and isinstance(choices, list):
                msg = (choices[0] or {}).get("message") or {}
                content = pick(msg, "content")
            u = j.get("usage") or {}
            if isinstance(u, dict):
                usage = f"prompt={u.get('prompt_tokens')}, completion={u.get('completion_tokens')}, total={u.get('total_tokens')}"
        except Exception:
            pass
        return f"[HTTP 200] 获取成功。content.length={len(content)}; usage=({usage})"

    if status == 400:
        if isinstance(j, dict):
            return f"[HTTP 400] code={j.get('code')}; message={pick(j, 'message')}; data={pick(j, 'data')}"
        return f"[HTTP 400] {t}"

    if status == 401:
        return f"[HTTP 401] {t or 'Invalid token'}"

    if status == 404:
        return f"[HTTP 404] {t or '404 page not found'}"

    if status == 429:
        if isinstance(j, dict):
            return f"[HTTP 429] message={pick(j, 'message')}; data={pick(j, 'data')}"
        return f"[HTTP 429] {t}"

    if status == 503:
        if isinstance(j, dict):
            return f"[HTTP 503] code={j.get('code')}; message={pick(j, 'message')}; data={pick(j, 'data')}"
        return f"[HTTP 503] {t}"

    if status == 504:
        return f"[HTTP 504] {t or 'Gateway Timeout'}"

    if status is not None:
        snippet = (t or "")[:512]
        return f"[HTTP {status}] {snippet}"
    return "未包含可识别的 HTTP 响应信息"


def main():
    parser = argparse.ArgumentParser(description="从 jsonl 读取题目，调用 LLM，写入结果（精细网络错误输出与超时保护）")
    parser.add_argument("-i", "--input", default="practice_data.jsonl", help="输入 jsonl 文件路径")
    parser.add_argument("-o", "--output", default="./output_jsonl/pdlean_fixed.jsonl", help="输出 jsonl 文件路径")
    parser.add_argument("--formal-type", default="Lean", help="formal_type 字段")
    parser.add_argument("--max", type=int, default=0, help="最多处理条数，0 表示全部")
    parser.add_argument("--retries", type=int, default=16, help="最大重试次数（默认 16 次）")
    parser.add_argument("--resume", action="store_true", default=True, help="启用断点续传")
    parser.add_argument("--header", default="", help="可选 header 字段")
    args = parser.parse_args()

    tackler = Jsonl_tackler(args.input)
    mapping = tackler.decode()  # {id: nl_problem}

    processed_ids = load_processed_ids(args.output) if args.resume else set()
    if args.resume and processed_ids:
        tqdm.write(f"[INFO] 断点续传：检测到已完成 {len(processed_ids)} 条，将跳过这些记录。")

    items = [(rid, prob) for rid, prob in mapping.items() if str(rid) not in processed_ids] if processed_ids else list(mapping.items())
    if args.max and args.max > 0:
        items = items[: args.max]

    ok = 0
    max_attempts = max(1, int(args.retries))
    header_arg = getattr(args, "header", "")
    total_token_usage = 0

    with tqdm(total=len(items), desc="Processing", unit="item") as pbar:
        for rec_id, nl_problem in items:
            gen_text = None
            tks = 0
            last_err: Optional[Exception] = None
            success_payload: Optional[Dict[str, Any]] = None

            for attempt in range(1, max_attempts + 1):
                try:
                    # lean_master 返回 (文本, token_usage, 原始 JSON)
                    gen_text, tks, raw_json = lean_master(nl_problem)
                    if gen_text is None or not str(gen_text).strip():
                        raise RuntimeError("LLM 返回空响应")
                    success_payload = raw_json
                    # 成功也按 200 打印摘要
                    summary_ok = _classify_http_payload(200, None, success_payload)
                    tqdm.write(f"[OK] id={rec_id} {summary_ok}")
                    break

                except Exception as e:
                    last_err = e
                    is_timeout = _is_timeout_error(e)
                    status, msg, resp_text, resp_json = _extract_status_and_payload(e)
                    err_type = type(e).__name__

                    # 统一输出错误信息
                    if is_timeout:
                        detail = _format_timeout_detail(e)
                        tqdm.write(
                            f"[TIMEOUT] id={rec_id} 第 {attempt}/{max_attempts} 次。读取阶段超时（read timed out/timeout）。\n"
                            f"status=N/A; server_message=无响应.\n"
                            f"error_type={err_type}; detail={detail}",
                            file=sys.stderr,
                        )
                    else:
                        summary = _classify_http_payload(status, resp_text, resp_json)
                        tqdm.write(
                            f"[WARN] id={rec_id} 生成失败，第 {attempt}/{max_attempts} 次："
                            f"status={status if status is not None else 'N/A'}; "
                            f"error_type={err_type}; error={msg}\n"
                            f"{summary}",
                            file=sys.stderr,
                        )

                    # 重试策略：
                    # - 超时：可重试
                    # - 429/503/504/其他 5xx：可重试
                    # - 400/401/404：不可重试
                    # - status 为 None（网络层错误）：可重试
                    retryable = False
                    if is_timeout:
                        retryable = True
                    elif status in (429, 503, 504) or (isinstance(status, int) and 500 <= status < 600):
                        retryable = True
                    elif status in (400, 401, 404):
                        retryable = False
                    elif status is None:
                        retryable = True

                    if attempt < max_attempts and retryable:
                        # 指数退避（上限 16s）；若有 Retry-After 则优先使用（上限 60s）
                        delay = min(2 ** (attempt - 1), 16)
                        try:
                            resp = getattr(e, "response", None)
                            if resp is not None:
                                ra = None
                                try:
                                    ra = resp.headers.get("Retry-After")
                                except Exception:
                                    ra = None
                                if ra:
                                    try:
                                        # 支持整数秒与浮点
                                        ra_seconds = max(1.0, float(ra))
                                        delay = int(min(ra_seconds, 60.0))
                                    except Exception:
                                        pass
                        except Exception:
                            pass
                        tqdm.write(f"[INFO] {delay}s 后重试（retryable={retryable}）...")
                        time.sleep(delay)
                    else:
                        # 达到最大次数或不可重试
                        break

            # 若仍无结果
            if gen_text is None or not str(gen_text).strip():
                status, msg, resp_text, resp_json = _extract_status_and_payload(last_err) if last_err else (None, "未知错误", None, None)
                summary = _classify_http_payload(status, resp_text, resp_json)
                tqdm.write(
                    f"[ERROR] id={rec_id} 连续 {max_attempts} 次未得到有效答复。\n"
                    f"status={status if status is not None else 'N/A'}; error={msg}\n{summary}",
                    file=sys.stderr,
                )
                pbar.update(1)
                continue

            # 成功写入
            gtxt = str(gen_text)
            total_token_usage += int(tks or 0)

            tqdm.write(f"=== Generated for ID {rec_id} ===")
            tqdm.write(gtxt)
            tqdm.write("\ntoken usage: " + str(tks or 0))
            tqdm.write("\ncurrent total token usages: " + str(total_token_usage))
            tqdm.write(f"=== End of ID {rec_id} ===\n")

            try:
                tackler.encode(
                    rec_id=rec_id,
                    formals_json=gtxt,
                    output_path=args.output,
                    formal_type=args.formal_type,
                    header=header_arg,
                )
                ok += 1
            except Exception as e:
                tqdm.write(f"[WARN] id={rec_id} 写入失败：{e}", file=sys.stderr)
            finally:
                pbar.update(1)

    print(f"完成 {ok}/{len(items)} 条记录，已写入 {args.output}")


if __name__ == "__main__":
    main()
