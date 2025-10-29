import argparse
import json
import sys
from tqdm import tqdm
from decoder_encoder import Jsonl_tackler
from litex_master import litex_master


def main():
    parser = argparse.ArgumentParser(description="从 jsonl 读取题目，生成 Litex 形式并写入新 jsonl（不处理字符串）")
    parser.add_argument("-i", "--input", default="practice_data.jsonl", help="输入 jsonl 文件路径")
    parser.add_argument("-o", "--output", default="practice_data_formal.jsonl", help="输出 jsonl 文件路径")
    parser.add_argument("--formal-type", default="Litex", help="formal_type 字段")
    parser.add_argument("--header", default="", help="header 字段")
    parser.add_argument("--max", type=int, default=0, help="最多处理条数，0 表示全部")
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
            try:
                gen_text = litex_master(nl_problem)

                # 输出生成内容供排查
                tqdm.write(f"=== Generated for ID {rec_id} ===")
                tqdm.write(gen_text)
                tqdm.write(f"=== End of ID {rec_id} ===\n")

                # 不做任何清洗/去除，直接原样写入两个字段
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
                tqdm.write(f"[WARN] id={rec_id} 处理失败: {e}", file=sys.stderr)
            finally:
                pbar.update(1)

    print(f"完成 {ok}/{len(items)} 条记录，已写入 {args.output}")


if __name__ == "__main__":
    main()
