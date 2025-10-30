import json
import re
from typing import Dict, Any, Iterable, List, Tuple, Union


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

    @staticmethod
    def _normalize_formal_type(ft: str) -> str:
        if not isinstance(ft, str):
            raise ValueError("formal_type 必须是字符串")
        ft_norm = ft.strip().lower()
        if ft_norm == "lean":
            return "Lean"
        if ft_norm == "litex":
            return "Litex"
        raise ValueError("formal_type 仅可为 'Lean' 或 'Litex'")

    @staticmethod
    def _detect_cheating(formal_code: str) -> None:
        # 检测 Lean 的 `sorry`（不区分大小写）
        if re.search(r"\bsorry\b", formal_code, flags=re.IGNORECASE):
            raise ValueError("formal_code 包含禁止的作弊标识：'sorry'")

        # 检测 Litex 中以行首的 `know`（简单规则，按行检测）
        for ln in formal_code.splitlines():
            if re.match(r"^\s*know\b", ln, flags=re.IGNORECASE):
                raise ValueError("formal_code 包含禁止的 Litex-cheat：以行首的 'know'")

    @staticmethod
    def _extract_code_block(s: str) -> str:
        """
        尝试提取三重反引号内的第一段代码（若存在），否则返回原始字符串。
        """
        if not isinstance(s, str):
            return s
        m = re.search(r'```(?:[\w+-]*\n)?(.*?)```', s, flags=re.S)
        if m:
            return m.group(1)
        return s

    @staticmethod
    def _clean_content_block(s: str) -> str:
        """
        对提取到的内容做有限清洗：
        - 去除外围三重反引号（若未被 _extract_code_block 抽出）
        - 去除外围单/双反引号
        - 去除两端的成对 \*\* 或 \*
        - 去掉每行行首的列表标记 (\- 或 \*)
        - 保留内部换行与缩进
        """
        if not isinstance(s, str):
            return s
        text = s

        # 去除外围三重反引号（冗余情况）
        if text.strip().startswith("```") and text.strip().endswith("```"):
            inner = re.sub(r'^\s*```[\w+-]*\n?', '', text, count=1, flags=re.S)
            inner = re.sub(r'```\s*$', '', inner, count=1, flags=re.S)
            text = inner

        # 去除外围单/双反引号
        text = text.strip()
        if (text.startswith("`") and text.endswith("`")) or (text.startswith("``") and text.endswith("``")):
            text = text.strip("`")

        # 若整块被 **...** 或 *...* 包围，去除一层
        tstrip = text.strip()
        if (tstrip.startswith("**") and tstrip.endswith("**")) or (tstrip.startswith("*") and tstrip.endswith("*")):
            if tstrip.startswith("**") and tstrip.endswith("**"):
                text = tstrip[2:-2]
            elif tstrip.startswith("*") and tstrip.endswith("*"):
                text = tstrip[1:-1]

        # 对每行去掉常见列表前缀
        lines = text.splitlines()
        cleaned_lines = [re.sub(r'^\s*[-*]\s+', '', ln) for ln in lines]
        cleaned = "\n".join([ln.rstrip() for ln in cleaned_lines]).strip("\n")
        return cleaned

    @staticmethod
    def _parse_labeled_text(s: str) -> Dict[str, str]:
        """
        解析简单标注文本格式（容错 Markdown 包装）。
        支持标签：header、formal_statement、formal_code
        """
        if not isinstance(s, str):
            return {}

        s = Jsonl_tackler._extract_code_block(s)

        labels = ["header", "formal_statement", "formal_code"]
        buffers: Dict[str, List[str]] = {k: [] for k in labels}
        current: Union[None, str] = None
        lines = s.splitlines()

        # 更宽松的标签行匹配：允许标签被 `*` / `**` / `` ` `` / `~` 包裹
        label_re = re.compile(
            r'^\s*(?:[*`~_\-\s]*)(header|formal_statement|formal_code)(?:[*`~_\-\s]*)\s*:\s*',
            flags=re.IGNORECASE
        )

        for line in lines:
            m = label_re.match(line)
            if m:
                current = m.group(1).lower()
                rest = line[m.end():]
                buffers[current].append(rest)
            else:
                if current:
                    buffers[current].append(line)

        if any(buffers[k] for k in labels):
            result: Dict[str, str] = {}
            for k in labels:
                block = "\n".join(buffers[k]).rstrip("\n")
                cleaned = Jsonl_tackler._clean_content_block(block)
                result[k] = cleaned
            return result
        return {}

    @staticmethod
    def _has_labels(s: str) -> bool:
        if not isinstance(s, str):
            return False
        text = Jsonl_tackler._extract_code_block(s)
        return re.search(
            r'^\s*(?:[*`~_\-\s]*)(header|formal_statement|formal_code)(?:[*`~_\-\s]*)\s*:',
            text,
            flags=re.IGNORECASE | re.MULTILINE
        ) is not None

    @staticmethod
    def _normalize_payload(payload: Dict[str, Any], header_default: str) -> Dict[str, Any]:
        """
        若 payload 的 'formal_statement' 或 'formal_code' 内含“带标签的整块文本”，
        则按标签重组为 header/formal_statement/formal_code；并统一补齐 header。
        """
        stmt_text = payload.get("formal_statement", "")
        code_text = payload.get("formal_code", "")

        if isinstance(stmt_text, str) or isinstance(code_text, str):
            if Jsonl_tackler._has_labels(stmt_text) or Jsonl_tackler._has_labels(code_text):
                labeled = Jsonl_tackler._parse_labeled_text(stmt_text or code_text)
                if labeled:
                    payload = {
                        "header": labeled.get("header", payload.get("header", header_default)),
                        "formal_statement": labeled.get("formal_statement", payload.get("formal_statement", "")),
                        "formal_code": labeled.get("formal_code", payload.get("formal_code", "")),
                    }

        if "header" not in payload:
            payload["header"] = header_default
        return payload

    def encode(
            self,
            rec_id: Union[str, int],
            formals_json: Union[str, Dict[str, Any]],
            output_path: str,
            formal_type: str = "Litex",
            header: str = ""
    ) -> Dict[str, Any]:
        """
        仅支持“带标签的整块字符串”输入：
        header: ...
        formal_statement: ...
        formal_code: ...
        从字符串中解析三段内容并写入 jsonl。
        """
        # 确保题面映射已加载
        if not self.mapping:
            self.decode()

        rec_id_str = str(rec_id)
        if rec_id_str not in self.mapping:
            raise KeyError(f"未在输入文件中找到 id '{rec_id_str}' 对应的 nl_problem")

        # 仅支持字符串输入
        if not isinstance(formals_json, str):
            raise TypeError("encode 仅支持字符串输入（包含 header/formal_statement/formal_code 的整块文本）")

        # 若内容被三重反引号包裹，先抽出代码块
        raw_text = self._extract_code_block(formals_json)

        # 按关键词切分三个段落（大小写不敏感，按出现顺序截取到下一个标签或文本末尾）
        label_re = re.compile(r'^\s*(header|formal_statement|formal_code)\s*:\s*', flags=re.IGNORECASE | re.MULTILINE)
        matches = list(label_re.finditer(raw_text))
        print()
        if not matches:
            raise ValueError("未检测到任何标签。需要包含 header:、formal_statement:、formal_code: 三个段落")

        sections: Dict[str, str] = {}
        for i, m in enumerate(matches):
            label = m.group(1).lower()
            start = m.end()
            end = matches[i + 1].start() if i + 1 < len(matches) else len(raw_text)
            content = raw_text[start:end].strip()
            content = self._clean_content_block(content)
            sections[label] = content

        # 校验必须段落
        required = ["header", "formal_statement", "formal_code"]
        missing = [k for k in required if k not in sections or not isinstance(sections[k], str)]
        if missing:
            raise ValueError(f"缺少必要段落：{', '.join(missing)}")

        # 规范化 formal_type
        formal_type_norm = self._normalize_formal_type(formal_type)

        # 作弊检测（只检查 formal_code）
        self._detect_cheating(sections["formal_code"])

        # 组装记录并写入
        record: Dict[str, Any] = {
            "id": rec_id_str,
            "nl_problem": self.mapping[rec_id_str],
            "formal_type": formal_type_norm,
            "header": sections["header"],
            "formal_statement": sections["formal_statement"],
            "formal_code": sections["formal_code"],
        }

        with open(output_path, "a", encoding="utf-8") as out:
            out.write(json.dumps(record, ensure_ascii=False))
            out.write("\n")

        return record

    def encode_batch(
        self,
        items: Iterable[Tuple[Union[str, int], Union[str, Dict[str, Any]]]],
        output_path: str,
        formal_type: str = "Litex",
        header: str = ""
    ) -> List[Dict[str, Any]]:
        """
        批量写入，items 为可迭代的 (rec_id, formals_json)。
        使用 tqdm 显示进度条，返回写入的记录列表。
        """
        try:
            from tqdm import tqdm
        except Exception as e:
            raise RuntimeError("使用 encode_batch 需要安装 tqdm：pip install tqdm") from e

        written: List[Dict[str, Any]] = []
        for rec_id, formals_json in tqdm(items, desc="写入 formals"):
            rec = self.encode(rec_id=rec_id, formals_json=formals_json,
                              output_path=output_path, formal_type=formal_type, header=header)
            written.append(rec)
        return written

