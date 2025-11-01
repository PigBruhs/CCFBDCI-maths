# python
import json
import os
import re
from typing import Optional, Union
from decoder_encoder import Jsonl_tackler

def convert_format_in_text(text: str, src_fmt: Optional[str], dst_fmt: str) -> str:
    """
    将文本中的代码围栏/标记从 src\_fmt 转为 dst\_fmt。
    - 示例：```litex -> ```lean；formal\_type: Litex -> formal\_type: Lean
    """
    if not isinstance(text, str) or not text:
        return text

    if src_fmt and src_fmt.lower() != dst_fmt.lower():
        # ``` litex / ```litex / ```\tLiTeX -> ```lean
        text = re.sub(
            r"(```[ \t]*)" + re.escape(src_fmt) + r"\b",
            r"\1" + dst_fmt,
            text,
            flags=re.IGNORECASE,
        )
        # formal_type: Litex / formal_type = Litex -> Lean
        text = re.sub(
            r"(?i)(formal_type\s*[:=]\s*)" + re.escape(src_fmt) + r"\b",
            r"\1" + dst_fmt.capitalize(),
            text,
        )

    # 统一目标大小写：代码围栏用小写语言名，formal_type 用首字母大写
    text = re.sub(r"```[ \t]*" + re.escape(dst_fmt) + r"\b", "```" + dst_fmt.lower(), text)
    return text

def input_answers(
    rec_id: Union[str, int],
    answer: str,
    output_path: str,
    target_formal_type: str = "Lean",
    header: str = "",
    source_format: Optional[str] = "Litex",
) -> bool:
    """
    直接接受字符串答案，将其转换为目标格式并写入 jsonl。
    - rec_id：该条记录的唯一标识
    - answer：原始答案字符串（可能为 Litex 等格式）
    - output_path：输出 jsonl 路径（自动创建目录并追加写入）
    - target_formal_type：写入的 formal_type（默认 Lean）
    - header：可选 header
    - source_format：源格式名，用于围栏/标记替换（默认 Litex）
    返回：是否写入成功
    """
    if not isinstance(answer, str) or not answer.strip():
        raise ValueError("answer 不能为空")

    # 转换为目标格式文本
    converted = convert_format_in_text(answer, src_fmt=source_format, dst_fmt=target_formal_type)

    # 确保输出目录存在
    out_dir = os.path.dirname(os.path.abspath(output_path))
    if out_dir and not os.path.exists(out_dir):
        os.makedirs(out_dir, exist_ok=True)

    # 优先使用项目内的 Jsonl_tackler 写入
    try:
        tackler = Jsonl_tackler("")  # encode 不依赖输入映射时，可给空路径
        tackler.encode(
            rec_id=rec_id,
            formals_json=converted,
            output_path=output_path,
            formal_type=target_formal_type,
            header=header,
        )
        return True
    except Exception:
        # 兜底：直接写入 jsonl
        record = {
            "rec_id": str(rec_id),
            "formal_type": target_formal_type,
            "formals_json": converted,
            "header": header,
        }
        try:
            with open(output_path, "a", encoding="utf-8") as f:
                f.write(json.dumps(record, ensure_ascii=False) + "\n")
            return True
        except Exception:
            return False


def convert_litex_to_lean_in_file(src_path: str, dst_path: Optional[str] = None) -> int:
    """
    将 jsonl 中的 formal_type 从 Litex 改为 Lean，并将代码块语言标记从 litex 改为 lean。
    - src_path：源 jsonl
    - dst_path：目标 jsonl；为空则原地覆盖
    返回：处理的行数
    """
    if not os.path.exists(src_path):
        raise FileNotFoundError(f"未找到文件: {src_path}")

    def _to_lean_text(text: str) -> str:
        if not isinstance(text, str) or not text:
            return text
        # ```litex -> ```lean（大小写不敏感）
        text = re.sub(r"```[ \t]*litex\b", "```lean", text, flags=re.IGNORECASE)
        # 兼容 fenced code 的行首语言标记形式 ``` Litex
        text = re.sub(r"^```[ \t]*litex\b", "```lean", text, flags=re.IGNORECASE | re.MULTILINE)
        return text

    tmp_path = dst_path or (src_path + ".tmp")
    total = 0

    with open(src_path, "r", encoding="utf-8") as fin, open(tmp_path, "w", encoding="utf-8") as fout:
        for line in fin:
            s = line.strip()
            if not s:
                fout.write(line)
                continue

            try:
                obj = json.loads(s)
                # formal_type -> Lean
                ft = obj.get("formal_type")
                if isinstance(ft, str) and ft.lower() == "litex":
                    obj["formal_type"] = "Lean"

                # 常见文本字段中的围栏语言标记替换
                for key in ("formals_json", "formal", "content", "answer", "body", "text"):
                    if key in obj and isinstance(obj[key], str):
                        obj[key] = _to_lean_text(obj[key])

                fout.write(json.dumps(obj, ensure_ascii=False) + "\n")
            except Exception:
                # 非 JSON 行做字符串替换兜底
                fout.write(_to_lean_text(line))
            total += 1

    if dst_path is None:
        os.replace(tmp_path, src_path)
    return total

if __name__ == "__main__":
    input_answers("MATH_geometry_5387",answer="header: \nimport Mathlib.Geometry.Euclidean.Basic\nimport Mathlib.Analysis.Inner_Product_Space.PiL2\nimport Mathlib.Tactic\n\nnamespace BalloonRopeOptimization\n\n-- This problem involves 3D geometry with points on a plane and a point above.\n-- We define coordinates: O at origin, A north (positive y), B west (negative x), \n-- C south (negative y), D east (positive x). H is directly above O (positive z).\n-- The distances between points on the ground are given, and rope lengths from H to A,B,C,D.\n\n-- Given: CD = 140m, HC = 150m, HD = 130m\n-- We need to find the maximum saving when replacing HC and HD with a single rope HP where P is on CD.\n\n-- Let's set up coordinate system:\n-- O = (0,0,0)\n-- A = (0,a,0) where a = OA > 0\n-- B = (-b,0,0) where b = OB > 0 \n-- C = (0,-c,0) where c = OC > 0\n-- D = (d,0,0) where d = OD > 0\n-- H = (0,0,h) where h = OH > 0\n\n-- From the problem: CD = 140m, so distance between C(0,-c,0) and D(d,0,0) is √(d² + c²) = 140\n-- Also: HC = 150m, so distance between H(0,0,h) and C(0,-c,0) is √(c² + h²) = 150\n-- And: HD = 130m, so distance between H(0,0,h) and D(d,0,0) is √(d² + h²) = 130\n\n-- We have three equations:\n-- (1) d² + c² = 140²\n-- (2) c² + h² = 150² \n-- (3) d² + h² = 130²\n\n-- Solving these gives us c, d, h.\n\n-- The saving is (HC + HD) - (HP + HD) but wait, we're replacing both HC and HD with HP?\n-- Actually reading carefully: "+"rope HC and rope HD are to be replaced by a single rope HP""\n-- So original total for these two ropes: HC + HD = 150 + 130 = 280\n-- New: HP (where P is on CD)\n-- Saving = (HC + HD) - HP = 280 - HP\n\n-- To maximize saving, we need to minimize HP.\n\n-- Since P is on line CD, we can parameterize P = C + t*(D - C) for t ∈ [0,1]\n-- P = (td, -c + t*c, 0) = (td, -c(1-t), 0) [Wait, careful: C=(0,-c,0), D=(d,0,0)]\n-- So P = (td, -c + t*c, 0) = (td, -c(1-t), 0)\n\n-- Then HP = distance between H(0,0,h) and P(td, -c(1-t), 0)\n-- HP² = (td)² + (-c(1-t))² + h² = t²d² + c²(1-t)² + h²\n\n-- We want to minimize HP, or equivalently HP².\n\n-- Let f(t) = t²d² + c²(1-t)² + h²\n-- f'(t) = 2td² - 2c²(1-t) = 2td² - 2c² + 2tc² = 2t(d² + c²) - 2c²\n-- Setting f'(t) = 0 gives: t(d² + c²) = c² ⇒ t = c²/(d² + c²)\n\n-- But d² + c² = 140² from equation (1)\n-- So optimal t = c²/140²\n\n-- Then minimal HP² = (c²/140²)² * d² + c²(1 - c²/140²)² + h²\n-- = (c⁴d²)/140⁴ + c²(140² - c²)²/140⁴ + h²\n-- = [c⁴d² + c²(140² - c²)²]/140⁴ + h²\n\n-- But we can find c², d², h² from the three equations.\n\n-- From (2) and (3): c² + h² = 150², d² + h² = 130²\n-- Subtracting: c² - d² = 150² - 130² = (150-130)(150+130) = 20*280 = 5600\n-- So c² = d² + 5600\n\n-- From (1): d² + (d² + 5600) = 140² ⇒ 2d² + 5600 = 19600 ⇒ 2d² = 14000 ⇒ d² = 7000\n-- Then c² = 7000 + 5600 = 12600\n-- Then h² = 150² - c² = 22500 - 12600 = 9900\n\n-- Now minimal HP² = [c⁴d² + c²(140² - c²)²]/140⁴ + h²\n-- = [12600² * 7000 + 12600 * (19600 - 12600)²] / 19600² + 9900\n-- = [12600² * 7000 + 12600 * 7000²] / 19600² + 9900\n-- = [7000 * 12600 * (12600 + 7000)] / 19600² + 9900\n-- = [7000 * 12600 * 19600] / 19600² + 9900\n-- = [7000 * 12600] / 19600 + 9900\n-- = [88200000] / 19600 + 9900\n-- = 4500 + 9900 = 14400\n\n-- So minimal HP = √14400 = 120\n\n-- Therefore maximum saving = 280 - 120 = 160\n\n-- Now we formalize this in Lean.\n\nend BalloonRopeOptimization\n\nopen BalloonRopeOptimization\n\nformal_statement:\ntheorem main_theorem : ∃ (saving : ℝ), saving = (150 : ℝ) + (130 : ℝ) - (120 : ℝ) ∧ saving = (160 : ℝ) :=\n\nformal_code:\nimport Mathlib.Geometry.Euclidean.Basic\nimport Mathlib.Analysis.Inner_Product_Space.PiL2\nimport Mathlib.Tactic\n\nnamespace BalloonRopeOptimization\n\n-- Coordinate system setup\nvariable (O A B C D H : EuclideanSpace ℝ (Fin 3))\nvariable (a b c d h : ℝ)\n\n-- Assumptions about positions\naxiom O_at_origin : O = (0 : EuclideanSpace ℝ (Fin 3))\naxiom A_north : A = (0, a, 0)\naxiom B_west : B = (-b, 0, 0) \naxiom C_south : C = (0, -c, 0)\naxiom D_east : D = (d, 0, 0)\naxiom H_above : H = (0, 0, h)\n\n-- Positive distances\naxiom a_pos : a > 0\naxiom b_pos : b > 0\naxiom c_pos : c > 0\naxiom d_pos : d > 0\naxiom h_pos : h > 0\n\n-- Given distances\naxiom CD_distance : dist C D = (140 : ℝ)\naxiom HC_distance : dist H C = (150 : ℝ)\naxiom HD_distance : dist H D = (130 : ℝ)\n\n-- The key equations derived from the distances\nlemma equation1 : d^2 + c^2 = 140^2 := by\n -- Distance CD = √((d-0)^2 + (0 - (-c))^2 + (0-0)^2) = √(d² + c²) = 140\n -- So d² + c² = 140²\n rw [show (140 : ℝ) = (140 : ℝ) by norm_num] at CD_distance\n have h1 : dist C D = Real.sqrt (d^2 + c^2) := by\n simp [A_north, B_west, C_south, D_east, H_above, dist_eq_norm, PiLp.norm_eq_sqrt_sq]\n ring\n rw [h1] at CD_distance\n have h2 : d^2 + c^2 ≥ 0 := by nlinarith [c_pos, d_pos]\n nlinarith [CD_distance, h2]\n\nlemma equation2 : c^2 + h^2 = 150^2 := by\n -- Distance HC = √((0-0)^2 + (0 - (-c))^2 + (h-0)^2) = √(c² + h²) = 150\n -- So c² + h² = 150²\n rw [show (150 : ℝ) = (150 : ℝ) by norm_num] at HC_distance\n have h1 : dist H C = Real.sqrt (c^2 + h^2) := by\n simp [A_north, B_west, C_south, D_east, H_above, dist_eq_norm, PiLp.norm_eq_sqrt_sq]\n ring\n rw [h1] at HC_distance\n have h2 : c^2 + h^2 ≥ 0 := by nlinarith [c_pos, h_pos]\n nlinarith [HC_distance, h2]\n\nlemma equation3 : d^2 + h^2 = 130^2 := by\n -- Distance HD = √((d-0)^2 + (0-0)^2 + (0-h)^2) = √(d² + h²) = 130\n -- So d² + h² = 130²\n rw [show (130 : ℝ) = (130 : ℝ) by norm_num] at HD_distance\n have h1 : dist H D = Real.sqrt (d^2 + h^2) := by\n simp [A_north, B_west, C_south, D_east, H_above, dist_eq_norm, PiLp.norm_eq_sqrt_sq]\n ring\n rw [h1] at HD_distance\n have h2 : d^2 + h^2 ≥ 0 := by nlinarith [d_pos, h_pos]\n nlinarith [HD_distance, h2]\n\n-- Solve for c², d², h²\nlemma c_sq_eq : c^2 = 12600 := by\n have h1 : c^2 - d^2 = 5600 := by\n have : c^2 + h^2 = 22500 := equation2\n have : d^2 + h^2 = 16900 := equation3\n nlinarith\n have : d^2 + c^2 = 19600 := equation1\n nlinarith\n\nlemma d_sq_eq : d^2 = 7000 := by\n have : d^2 + c^2 = 19600 := equation1\n rw [c_sq_eq] at this\n nlinarith\n\nlemma h_sq_eq : h^2 = 9900 := by\n rw [c_sq_eq] at equation2\n nlinarith [equation2]\n\n-- Parameterize point P on line CD\ndef P (t : ℝ) : EuclideanSpace ℝ (Fin 3) := C + t • (D - C)\n\n-- Distance HP as a function of t\ndef HP_sq (t : ℝ) : ℝ := dist H (P t) ^ 2\n\n-- Express HP_sq in terms of t, c, d, h\nlemma HP_sq_formula (t : ℝ) : HP_sq t = t^2 * d^2 + (1 - t)^2 * c^2 + h^2 := by\n dsimp [HP_sq, P]\n simp [A_north, B_west, C_south, D_east, H_above, dist_eq_norm, PiLp.norm_eq_sqrt_sq]\n ring\n\n-- Find optimal t that minimizes HP\nlemma optimal_t : (fun t : ℝ => HP_sq t) \n HasDerivAt (fun t => 2 * t * d^2 - 2 * (1 - t) * c^2) := by\n intro t\n have : HP_sq t = t^2 * d^2 + (1 - t)^2 * c^2 + h^2 := HP_sq_formula t\n have : deriv (HP_sq) t = 2 * t * d^2 - 2 * (1 - t) * c^2 := by\n dsimp [HP_sq]\n simp [A_north, B_west, C_south, D_east, H_above, dist_eq_norm, PiLp.norm_eq_sqrt_sq]\n ring\n exact this\n\nlemma derivative_zero_condition : 2 * t * d^2 - 2 * (1 - t) * c^2 = 0 ↔ t = c^2 / (d^2 + c^2) := by\n constructor\n · intro h\n have : t * d^2 = (1 - t) * c^2 := by linarith\n have : t * (d^2 + c^2) = c^2 := by linarith\n have : d^2 + c^2 = 19600 := equation1\n rw [this] at *\n field_simp [show (19600 : ℝ) ≠ 0 by norm_num] at *\n nlinarith\n · intro h\n have : d^2 + c^2 = 19600 := equation1\n rw [h, this]\n field_simp [show (19600 : ℝ) ≠ 0 by norm_num]\n nlinarith [c_sq_eq]\n\n-- Minimum HP occurs at t = c²/(d² + c²)\nlemma min_HP_at_t_opt : IsMinOn (fun t => HP_sq t) Set.univ (c^2 / (d^2 + c^2)) := by\n apply convex_univ.minimize_of_deriv_zero (fun t _ => ?_) (derivative_zero_condition ).2\n · exact optimal_t t\n · intro x hx\n have : deriv (HP_sq) x = 2 * x * d^2 - 2 * (1 - x) * c^2 := optimal_t x\n exact this\n\n-- Calculate minimal HP\nlemma min_HP_sq_eq : HP_sq (c^2 / (d^2 + c^2)) = 14400 := by\n rw [HP_sq_formula]\n rw [show d^2 + c^2 = (140 : ℝ)^2 by linarith [equation1]]\n rw [c_sq_eq, d_sq_eq, h_sq_eq]\n norm_num\n ring\n\nlemma min_HP_eq : dist H (P (c^2 / (d^2 + c^2))) = 120 := by\n have h1 : HP_sq (c^2 / (d^2 + c^2)) = 14400 := min_HP_sq_eq\n dsimp [HP_sq] at h1\n nlinarith [h1]\n\n-- Maximum saving\ntheorem main_theorem : ∃ (saving : ℝ), saving = (150 : ℝ) + (130 : ℝ) - (120 : ℝ) ∧ saving = (160 : ℝ) := by\n refine ⟨160, ?, rfl⟩\n norm_num\n\nend BalloonRopeOptimization",output_path="./output_jsonl/practice_data_lean_current.jsonl")