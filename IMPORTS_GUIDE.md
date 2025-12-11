# Mathlib 和 Aesop 导入指南

## 支持的导入

本地项目已配置 **Mathlib 4.10.0**，支持以下导入：

### ✅ 完整支持

```lean
-- 所有 Mathlib tactic（推荐）
import Mathlib.Tactic

-- Aesop 自动证明器
import Aesop

-- 基础库
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic

-- 常用 tactic
import Mathlib.Tactic.Omega      -- omega: 线性算术
import Mathlib.Tactic.Ring       -- ring: 环论
import Mathlib.Tactic.Linarith   -- linarith: 线性不等式
import Mathlib.Tactic.FieldSimp  -- field_simp: 域简化
import Mathlib.Tactic.NormNum    -- norm_num: 数值规范化
```

---

## 常用 Tactic 示例

### 1. Omega - 线性算术

```lean
import Mathlib.Tactic

theorem nat_positive (n : ℕ) (h : n > 0) : n ≥ 1 := by
  omega

theorem int_arithmetic (x y : ℤ) (h : x + y = 10) : y + x = 10 := by
  omega
```

### 2. Ring - 交换环

```lean
import Mathlib.Tactic

theorem add_comm (a b : ℕ) : a + b = b + a := by
  ring

theorem mul_comm (x y : ℤ) : x * y = y * x := by
  ring
```

### 3. Linarith - 线性不等式

```lean
import Mathlib.Tactic

theorem squeeze (x y z : ℝ) (h1 : x ≤ y) (h2 : y ≤ z) (h3 : z ≤ x) : x = y ∧ y = z := by
  constructor <;> linarith
```

### 4. Aesop - 自动证明

```lean
import Aesop

theorem modus_ponens (p q : Prop) (h1 : p) (h2 : p → q) : q := by
  aesop

theorem and_intro (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  aesop
```

### 5. Simp - 简化

```lean
import Mathlib.Tactic

theorem list_append_nil (l : List α) : l ++ [] = l := by
  simp

theorem zero_add (n : ℕ) : 0 + n = n := by
  simp
```

---

## 在动态证明服务中使用

### 示例 1: 使用 Omega

```python
client.prove(
    theorem_statement="(n : ℕ) (h : n > 0) : n ≥ 1",
    timeout=60,
)
# 期望证明: omega
```

### 示例 2: 使用 Ring

```python
client.prove(
    theorem_statement="(a b : ℤ) : a * b = b * a",
    timeout=60,
)
# 期望证明: ring
```

### 示例 3: 使用 Aesop

```python
client.prove(
    theorem_statement="""
    (p q : Prop) (h1 : p) (h2 : p → q) : q
    """,
    timeout=60,
)
# 期望证明: aesop
```

---

## 完整 Tactic 列表

通过 `import Mathlib.Tactic` 可以使用：

| Tactic | 用途 | 示例 |
|--------|------|------|
| `omega` | 线性算术 | `n > 0 → n ≥ 1` |
| `ring` | 环论等式 | `a + b = b + a` |
| `linarith` | 线性不等式 | `x ≤ y ∧ y ≤ x → x = y` |
| `field_simp` | 域简化 | `a / b * b = a` |
| `norm_num` | 数值计算 | `2 + 2 = 4` |
| `simp` | 简化 | `l ++ [] = l` |
| `aesop` | 自动证明 | 逻辑推理 |
| `decide` | 可判定命题 | `3 < 5` |
| `rfl` | 定义等价 | `x = x` |
| `exact` | 精确项 | 提供证明项 |
| `intro` | 引入假设 | `∀ x, P x` |
| `apply` | 应用定理 | 后向推理 |
| `constructor` | 构造 | `p ∧ q` |

---

## 依赖配置

当前 `lakefile.lean`:

```lean
import Lake
open Lake DSL

package workspace

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.10.0"

@[default_target]
lean_lib WorkspaceTheorems
```

**Mathlib 版本**: v4.10.0（与 Lean 4.10.0 匹配）  
**Aesop**: 包含在 Mathlib 中，无需额外配置

---

## 验证导入

运行测试：

```bash
cd local_lean_workspace
lake build WorkspaceTheorems.TestImports
```

如果构建成功，说明所有导入都正常工作！

---

## 常见问题

### Q: Import 找不到模块

确保已运行：
```bash
lake update  # 下载 Mathlib
lake build   # 构建依赖
```

### Q: Mathlib 太大，下载很慢

初次下载 Mathlib 需要时间（~10-30 分钟），请耐心等待。之后会缓存。

### Q: 想要更新 Mathlib 版本

编辑 `lakefile.lean`，修改版本号：
```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"
```

然后运行：
```bash
lake update
lake build
```

### Q: Aesop 不可用

Aesop 从 Mathlib 4.x 开始已集成，只需：
```lean
import Aesop
```

如果仍不可用，确保 Mathlib 已正确安装：
```bash
lake build Mathlib
```

---

## 总结

✅ **Mathlib**: 完全支持，包含所有标准库和 tactic  
✅ **Aesop**: 完全支持，集成在 Mathlib 中  
✅ **版本**: Mathlib 4.10.0 匹配 Lean 4.10.0  
✅ **导入**: 使用 `import Mathlib.Tactic` 获取所有常用 tactic

你可以在定理陈述中自由使用任何 Mathlib 的类型、函数和 tactic！
