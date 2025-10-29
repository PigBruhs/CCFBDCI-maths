import argparse
import json
import sys
import time
from tqdm import tqdm
from decoder_encoder import Jsonl_tackler
from litex_master import litex_master


def main():
    parser = argparse.ArgumentParser(description="从 jsonl 读取题目，生成 Litex 形式并写入新 jsonl（带重试逻辑）")
    parser.add_argument("-i", "--input", default="practice_data.jsonl", help="输入 jsonl 文件路径")
    parser.add_argument("-o", "--output", default="practice_data_formal.jsonl", help="输出 jsonl 文件路径")
    parser.add_argument("--formal-type", default="Litex", help="formal_type 字段")
    parser.add_argument("--header", default="", help="header 字段")
    parser.add_argument("--max", type=int, default=0, help="最多处理条数，0 表示全部")
    parser.add_argument("--retries", type=int, default=8, help="生成失败时的重试次数")
    args = parser.parse_args()

    tackler = Jsonl_tackler(args.input)
    mapping = tackler.decode()  # {id: nl_problem}

    # 清空/创建输出文件
    open(args.output, "w", encoding="utf-8").close()

    items = list(mapping.items())
    if args.max and args.max > 0:
        items = items[: args.max]

    ok = 0
    with tqdm(total=len(items), desc="Processing", unit="item") as pbar:
        for rec_id, nl_problem in items:
            gen_text = None
            last_err = None

            # 生成阶段带重试
            for attempt in range(1, args.retries + 1):
                try:
                    gen_text = litex_master(nl_problem)
                    if gen_text is None or not str(gen_text).strip():
                        raise RuntimeError("LLM 返回空响应")
                    break
                except Exception as e:
                    last_err = e
                    tqdm.write(f"[WARN] id={rec_id} 生成失败，第 {attempt}/{args.retries} 次：{e}", file=sys.stderr)
                    if attempt < args.retries:
                        # 简单指数退避，最多等待 8 秒
                        time.sleep(min(2 ** (attempt - 1), 8))

            # 连续重试仍失败：输出错误信息并终止程序
            if gen_text is None or not str(gen_text).strip():
                tqdm.write(
                    f"[ERROR] id={rec_id} 连续 {args.retries} 次未得到答复，终止程序。最后错误：{last_err}",
                    file=sys.stderr,
                )
                pbar.close()
                sys.exit(1)

            # 输出生成内容供排查
            tqdm.write(f"=== Generated for ID {rec_id} ===")
            tqdm.write(gen_text)
            tqdm.write(f"=== End of ID {rec_id} ===\n")

            # 不做任何清洗/去除，直接原样写入两个字段
            try:
                formals = {
                    "formal_statement": gen_text,
                    "formal_code": gen_text,
                }
                formals_json = json.dumps(formals, ensure_ascii=False)

                tackler.encode(
                    rec_id=rec_id,
                    formals_json=formals_json,
                    output_path=args.output,
                    formal_type=args.formal_type,
                    header=args.header,
                )
                ok += 1
            except Exception as e:
                tqdm.write(f"[WARN] id={rec_id} 写入失败：{e}", file=sys.stderr)
            finally:
                pbar.update(1)

    print(f"完成 {ok}/{len(items)} 条记录，已写入 {args.output}")


if __name__ == "__main__":
    main()
