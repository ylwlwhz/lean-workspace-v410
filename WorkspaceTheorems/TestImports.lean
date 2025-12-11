-- 测试 Mathlib 和 Aesop 导入

-- 基础 Mathlib tactic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Omega

-- Aesop (包含在 Mathlib 中)
import Aesop

-- 完整 Mathlib.Tactic (包含所有常用 tactic)
import Mathlib.Tactic

-- 测试定理 1: 使用 omega
theorem test_omega (n : ℕ) (h : n > 0) : n ≥ 1 := by
  omega

-- 测试定理 2: 使用 ring
theorem test_ring (a b : ℕ) : a + b = b + a := by
  ring

-- 测试定理 3: 使用 linarith
theorem test_linarith (x y : ℤ) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  linarith

-- 测试定理 4: 使用 aesop
theorem test_aesop (p q : Prop) (h1 : p) (h2 : p → q) : q := by
  aesop

-- 测试定理 5: 组合使用
theorem test_combined (n m : ℕ) (h : n + m = 10) : m + n = 10 := by
  omega
