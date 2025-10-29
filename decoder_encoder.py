import json
from typing import Dict, Any

class Jsonl_tackler:
    def __init__(self, input_path: str):
        self.input_path = input_path
        self.mapping: Dict[str, str] = {}

    def decode(self) -> Dict[str, str]:
        """
        读取输入 jsonl，填充并返回 {id: nl_problem} 映射
        """
        result: Dict[str, str] = {}
        with open(self.input_path, "r", encoding="utf-8") as f:
            for lineno, line in enumerate(f, start=1):
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except json.JSONDecodeError as e:
                    raise ValueError(f"第 {lineno} 行 JSON 解析失败: {e.msg}") from e
                if "id" not in obj or "nl_problem" not in obj:
                    raise KeyError(f"第 {lineno} 行缺少字段 'id' 或 'nl_problem'")
                result[str(obj["id"])] = str(obj["nl_problem"])
        self.mapping = result
        return result

    def encode(
        self,
        rec_id: str | int,
        formals_json: str,
        output_path: str,
        formal_type: str = "Litex",
        header: str = ""
    ) -> Dict[str, Any]:
        """
        将指定 id 的题面与传入的 formal_statement/formal_code 组合写入目标 jsonl。
        formals_json 需为包含 'formal_statement' 与 'formal_code' 的 JSON 字符串。
        """
        if not self.mapping:
            self.decode()

        rec_id_str = str(rec_id)
        if rec_id_str not in self.mapping:
            raise KeyError(f"未在输入文件中找到 id '{rec_id_str}' 对应的 nl_problem")

        try:
            payload = json.loads(formals_json)
        except json.JSONDecodeError as e:
            raise ValueError("formals_json 必须是 JSON 字符串") from e

        if "formal_statement" not in payload or "formal_code" not in payload:
            raise KeyError("formals_json 缺少字段 'formal_statement' 或 'formal_code'")

        record: Dict[str, Any] = {
            "id": rec_id_str,
            "nl_problem": self.mapping[rec_id_str],
            "formal_type": formal_type,
            "header": header,
            "formal_statement": payload["formal_statement"],
            "formal_code": payload["formal_code"],
        }

        with open(output_path, "a", encoding="utf-8") as out:
            out.write(json.dumps(record, ensure_ascii=False))
            out.write("\n")

        return record


if __name__ == "__main__":
    # 示例：从 `practice_data.jsonl` 解码，再把 107361 的 formal 写到 `practice_data_formal.jsonl`
    codec = Jsonl_tackler("practice_data.jsonl")
    codec.decode()

    formals = json.dumps({
        "formal_statement": "forall e1, e2, e3, v1, v2, v3, partial_sum, total_sum, avg N_pos:\n        e1 = 4\n        e2 = 5\n        e3 = 6\n        v1 = e1 ^ 3\n        v2 = e2 ^ 3\n        v3 = e3 ^ 3\n        partial_sum = v1 + v2\n        total_sum = partial_sum + v3\n        avg = total_sum / 3\n        =>:\n            avg = 135",
        "formal_code": "claim:\n    forall e1, e2, e3, v1, v2, v3, partial_sum, total_sum, avg N_pos:\n        e1 = 4\n        e2 = 5\n        e3 = 6\n        v1 = e1 ^ 3\n        v2 = e2 ^ 3\n        v3 = e3 ^ 3\n        partial_sum = v1 + v2\n        total_sum = partial_sum + v3\n        avg = total_sum / 3\n        =>:\n            avg = 135\n    prove:\n        v1 = 4 ^ 3\n        v1 = 64\n\n        v2 = 5 ^ 3\n        v2 = 125\n\n        v3 = 6 ^ 3\n        v3 = 216\n\n        partial_sum = v1 + v2\n        partial_sum = 64 + 125\n        partial_sum = 189\n\n        total_sum = partial_sum + v3\n        total_sum = 189 + 216\n        total_sum = 405\n\n        avg = total_sum / 3\n        avg = 405 / 3\n        avg = 135"
    }, ensure_ascii=False)

    codec.encode(rec_id="107361", formals_json=formals, output_path="practice_data_formal.jsonl")
