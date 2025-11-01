import json
import re
from typing import Dict, Any, Iterable, List, Tuple, Union
import os


# python
class Jsonl_tackler:
    def __init__(self, input_path: str):
        self.input_path = input_path
        self.mapping: Dict[str, str] = {}

    def decode(self) -> Dict[str, str]:
        """
        读取输入 jsonl，填充并返回 {id: nl_problem} 映射（容错多种字段名）。
        """
        result: Dict[str, str] = {}
        with open(self.input_path, "r", encoding="utf-8") as f:
            for lineno, line in enumerate(f, start=1):
                s = line.strip()
                if not s:
                    continue
                try:
                    obj = json.loads(s)
                except Exception:
                    continue
                # 兼容多种字段名
                rid = obj.get("id") or obj.get("rec_id") or obj.get("question_id")
                nl = obj.get("nl_problem") or obj.get("question") or obj.get("problem") or obj.get("input") or obj.get("text")
                if rid is None or nl is None:
                    continue
                result[str(rid)] = str(nl)
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
                raise ValueError("formal_code 包含禁止的作弊标识：'know'")

    @staticmethod
    def _extract_code_block(s: str) -> str:
        """
        若整段被三重反引号围栏（含语言标签，如 ```lean）包裹，抽出第一段代码；否则返回原始字符串。
        """
        if not isinstance(s, str):
            return s
        m = re.search(r'```(?:[\w.+-]*\n)?(.*?)```', s, flags=re.S)
        if m:
            return m.group(1)
        return s

    @staticmethod
    def _strip_outer_md_fence(text: str) -> str:
        """
        去除一层最外侧三重反引号围栏（允许语言标记），仅当整块以围栏包裹时生效。
        """
        if not isinstance(text, str):
            return text
        t = text.strip()
        if t.startswith("```") and t.endswith("```"):
            # 去掉起始 ```lang\n 与结尾 ```
            inner = re.sub(r'^\s*```[\w.+-]*\n?', '', t, count=1, flags=re.S)
            inner = re.sub(r'```\s*$', '', inner, count=1, flags=re.S)
            return inner
        return text

    @staticmethod
    def _strip_all_outer_md_fences(text: str) -> str:
        """
        反复去除最外层围栏，直到不再是完整围栏包裹。
        """
        prev = None
        cur = text
        for _ in range(5):
            if prev == cur:
                break
            prev = cur
            cur = Jsonl_tackler._strip_outer_md_fence(cur)
        return cur

    @staticmethod
    def _clean_content_block(s: str) -> str:
        """
        对提取到的内容做有限清洗（面向 Markdown 输出）：
        - 去除外围三重反引号（含 ```lean 等语言标签，支持重复嵌套）
        - 去除外围单/双反引号
        - 去除外围成对 \*\* 或 \*
        - 去掉每行开头的引用符号 `>` 与常见列表标记（\- 或 \*）
        - 保留内部换行与缩进
        """
        if not isinstance(s, str):
            return s
        text = s

        # 去除所有最外层围栏（含 ```lean）
        text = Jsonl_tackler._strip_all_outer_md_fences(text)

        # 去除外围单/双反引号
        text = text.strip()
        if (text.startswith("``") and text.endswith("``")) or (text.startswith("`") and text.endswith("`")):
            text = text.strip("`")

        # 若整块被 **...** 或 *...* 包围，去除一层
        tstrip = text.strip()
        if len(tstrip) >= 4 and tstrip.startswith("**") and tstrip.endswith("**"):
            text = tstrip[2:-2].strip()
        else:
            if len(tstrip) >= 2 and tstrip.startswith("*") and tstrip.endswith("*"):
                text = tstrip[1:-1].strip()

        # 去掉每行的引用符号与列表前缀
        lines = text.splitlines()
        cleaned_lines = []
        for ln in lines:
            ln2 = re.sub(r'^\s*>+\s*', '', ln)              # 引用前缀
            ln2 = re.sub(r'^\s*[-*]\s+', '', ln2)           # 列表项
            cleaned_lines.append(ln2)
        cleaned = "\n".join([ln.rstrip() for ln in cleaned_lines]).strip("\n")
        return cleaned

    @staticmethod
    def _parse_labeled_text(s: str) -> Dict[str, str]:
        """
        解析“带标签的整块文本”（容错 Markdown 包装）。
        支持标签：header、formal_statement、formal_code
        - 允许标签被 \`*`、\`**`、\`_`、\`~`、破折号、空格等包裹
        - 允许标签行后同一行即有内容
        """
        if not isinstance(s, str):
            return {}

        # 若整块被代码围栏包裹（含 ```lean），先抽出内部
        s = Jsonl_tackler._extract_code_block(s)

        labels = ["header", "formal_statement", "formal_code"]
        buffers: Dict[str, List[str]] = {k: [] for k in labels}
        current: Union[None, str] = None
        lines = s.splitlines()

        # 更宽松的标签行匹配
        label_re = re.compile(
            r'^\s*(?:[*`~_\-\s]*)(header|formal_statement|formal_code)(?:[*`~_\-\s]*)\s*:\s*(.*)$',
            flags=re.IGNORECASE
        )

        for line in lines:
            m = label_re.match(line)
            if m:
                current = m.group(1).lower()
                rest = m.group(2) or ""
                if rest:
                    buffers[current].append(rest)
            else:
                if current:
                    buffers[current].append(line)

        # 输出前对各段执行 Markdown 清洗
        if any(buffers[k] for k in labels):
            result: Dict[str, str] = {}
            for k in labels:
                raw = "\n".join(buffers[k]).strip()
                result[k] = Jsonl_tackler._clean_content_block(raw)
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
            # 如果任一字段内部仍包含标签，则进行二次解析并覆盖
            src = stmt_text if Jsonl_tackler._has_labels(stmt_text) else code_text
            if isinstance(src, str) and Jsonl_tackler._has_labels(src):
                parsed = Jsonl_tackler._parse_labeled_text(src)
                if parsed:
                    payload.update(parsed)

        if "header" not in payload or not isinstance(payload.get("header"), str):
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
        接受“带标签的整块字符串”（支持 Markdown）：
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

        # 仅支持字符串输入（保持与现有调用一致）
        if not isinstance(formals_json, str):
            raise TypeError("encode 仅支持字符串输入（包含 header/formal_statement/formal_code 的整块文本）")

        # 先尝试宽松 Markdown 解析
        sections = self._parse_labeled_text(formals_json)

        # 若未解析到，退回到“按标签定位的简单切分”策略
        if not sections:
            raw_text = self._extract_code_block(formals_json)
            label_re = re.compile(r'^\s*(header|formal_statement|formal_code)\s*:\s*', flags=re.IGNORECASE | re.MULTILINE)
            matches = list(label_re.finditer(raw_text))
            if not matches:
                raise ValueError("未检测到任何标签。需要包含 header:、formal_statement:、formal_code: 三个段落")

            tmp: Dict[str, str] = {}
            for i, m in enumerate(matches):
                label = m.group(1).lower()
                start = m.end()
                end = matches[i + 1].start() if i + 1 < len(matches) else len(raw_text)
                content = raw_text[start:end].strip()
                tmp[label] = self._clean_content_block(content)
            sections = tmp

        # 校验必须段落
        required = ["header", "formal_statement", "formal_code"]
        missing = [k for k in required if k not in sections or not isinstance(sections[k], str)]
        if missing:
            raise ValueError(f"缺少必要段落：{', '.join(missing)}")

        # 进一步剥离 formal_code 内部可能存在的外层 ```lean 或通用 ``` 围栏
        code_clean = self._clean_content_block(sections["formal_code"])
        stmt_clean = self._clean_content_block(sections["formal_statement"])
        header_clean = self._clean_content_block(sections["header"])

        # 规范化 formal_type
        formal_type_norm = self._normalize_formal_type(formal_type)

        payload: Dict[str, Any] = {
            "id": rec_id_str,
            "nl_problem": self.mapping[rec_id_str],
            "formal_type": formal_type_norm,
            "header": header_clean if header_clean else (header or ""),
            "formal_statement": stmt_clean,
            "formal_code": code_clean,
        }

        # 若任一字段内部仍残留“带标签文本”，进行二次规范化
        payload = self._normalize_payload(payload, header_default=(header or ""))

        # 可选作弊检测（如需启用，取消注释）
        # self._detect_cheating(payload["formal_code"])

        # 追加写入 jsonl
        os.makedirs(os.path.dirname(output_path) or ".", exist_ok=True)
        with open(output_path, "a", encoding="utf-8") as f:
            f.write(json.dumps(payload, ensure_ascii=False) + "\n")

        return payload
