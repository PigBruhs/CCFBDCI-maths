import argparse
import json
import sys
import time
import re
from tqdm import tqdm
from decoder_encoder import Jsonl_tackler
from litex_master import litex_master
import time

def main():
    parser = argparse.ArgumentParser(description="从 jsonl 读取题目，生成 Litex 形式并写入新 jsonl（带重试逻辑）")
    parser.add_argument("-i", "--input", default="practice_data.jsonl", help="输入 jsonl 文件路径")
    parser.add_argument("-o", "--output", default=f"practice_data_formal_{time.time()}.jsonl", help="输出 jsonl 文件路径")
    parser.add_argument("--formal-type", default="Litex", help="formal_type 字段")
    parser.add_argument("--max", type=int, default=0, help="最多处理条数，0 表示全部")
    # 保持命令行兼容，但实际重试次数固定为 8 次
    parser.add_argument("--retries", type=int, default=8, help="生成失败时的重试次数（实际最多 8 次）")
    args = parser.parse_args()

    tackler = Jsonl_tackler(args.input)
    mapping = tackler.decode()  # {id: nl_problem}

    # 清空/创建输出文件
    open(args.output, "w", encoding="utf-8").close()

    items = list(mapping.items())
    if args.max and args.max > 0:
        items = items[: args.max]

    ok = 0
    max_attempts = 8
    header_arg = getattr(args, "header", "")

    with tqdm(total=len(items), desc="Processing", unit="item") as pbar:
        for rec_id, nl_problem in items:
            gen_text = None
            last_err = None

            for attempt in range(1, max_attempts + 1):
                try:
                    gen_text = litex_master(nl_problem)
                    if gen_text is None or not str(gen_text).strip():
                        raise RuntimeError("LLM 返回空响应")
                    break
                except Exception as e:
                    last_err = e
                    tqdm.write(f"[WARN] id={rec_id} 生成失败，第 {attempt}/{max_attempts} 次：{e}", file=sys.stderr)
                    if attempt < max_attempts:
                        time.sleep(min(2 ** (attempt - 1), 8))

            if gen_text is None or not str(gen_text).strip():
                tqdm.write(
                    f"[ERROR] id={rec_id} 连续 {max_attempts} 次未得到答复，程序已暂停。最后错误：{last_err}",
                    file=sys.stderr,
                )
                pbar.close()
                try:
                    input("按回车键退出程序（或手动终止以继续其他操作）...")
                except Exception:
                    pass
                sys.exit(1)

            gtxt = str(gen_text)
            if re.search(r"\bsorry\b", gtxt, flags=re.IGNORECASE) or any(re.match(r"^\s*know\b", ln, flags=re.IGNORECASE) for ln in gtxt.splitlines()):
                tqdm.write(f"[ERROR] id={rec_id} 生成内容包含禁止的作弊标识（如 'sorry' 或 行首 'know'），程序终止。", file=sys.stderr)
                pbar.close()
                sys.exit(1)

            tqdm.write(f"=== Generated for ID {rec_id} ===")
            tqdm.write(gtxt)
            tqdm.write(f"=== End of ID {rec_id} ===\n")

            try:
                # 关键改动：直接把 LLM 的“带标签整块文本”传给 encode
                tackler.encode(
                    rec_id=rec_id,
                    formals_json=gtxt,
                    output_path=args.output,
                    formal_type=args.formal_type,
                    header=header_arg,
                )
                ok += 1
            except Exception as e:
                serr = str(e)
                if "作弊" in serr or re.search(r"\bknow\b", serr, flags=re.IGNORECASE) or re.search(r"\bsorry\b", serr, flags=re.IGNORECASE):
                    tqdm.write(f"[ERROR] id={rec_id} 写入失败且检测到作弊标识，程序终止。错误：{e}", file=sys.stderr)
                    pbar.close()
                    sys.exit(1)
                tqdm.write(f"[WARN] id={rec_id} 写入失败：{e}", file=sys.stderr)
            finally:
                pbar.update(1)

    print(f"完成 {ok}/{len(items)} 条记录，已写入 {args.output}")


if __name__ == "__main__":
    main()