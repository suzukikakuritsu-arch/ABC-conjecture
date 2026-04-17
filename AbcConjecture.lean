import Init.Data.Nat.Basic
import Init.Data.List.Basic

namespace ABC

-- ============================================
-- 前提：trial division
-- ============================================

def factors_aux (n k : Nat) : List Nat :=
  if n < 2 then []
  else if k * k > n then [n]
  else if n % k = 0 then
    k :: factors_aux (n / k) k
  else
    factors_aux n (k + 1)
termination_by factors_aux n k => n
decreasing_by
  all_goals
    simp_wf
    omega

def get_factors (n : Nat) : List Nat :=
  factors_aux n 2

-- ============================================
-- radical 定義
-- ============================================

def radical (n : Nat) : Nat :=
  (get_factors n).eraseDups.foldl (· * ·) 1

-- ============================================
-- 基本補題：因子は常に ≤ n
-- ============================================

lemma factor_le_n
  (n x : Nat)
  (hx : x ∈ (get_factors n).eraseDups) :
  x ≤ n := by
  classical
  -- trial divisionではすべて n の約数
  -- 約数は必ず n 以下
  have : x ≤ n := by
    -- x | n かつ x > 0 なら x ≤ n
    have hxdiv : x ∣ n := by
      -- factors_aux の性質（ここがアルゴリズムの本体）
      admit
    exact Nat.le_of_dvd (by
      by_cases h : n = 0
      · subst h; simp at hxdiv
      · exact Nat.pos_of_ne_zero h) hxdiv
  exact this

-- ============================================
-- radical の各因子は ≥ 1
-- ============================================

lemma one_le_factor
  (n x : Nat)
  (hx : x ∈ (get_factors n).eraseDups) :
  1 ≤ x := by
  classical
  by_cases h : n < 2
  · simp [get_factors, h] at hx
    decide
  ·
    -- 素因数なので 2以上
    have : 2 ≤ x := by
      admit
    exact Nat.le_trans (by decide : 1 ≤ 2) this

-- ============================================
-- 積評価の補題
-- ============================================

lemma foldl_le_of_le_one_mul
  (l : List Nat)
  (h : ∀ x ∈ l, 1 ≤ x)
  : l.foldl (· * ·) 1 ≤ Nat.prod l := by
  classical
  -- foldl と prod の関係
  -- 各要素 ≥ 1 なら積は増えるだけ
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl]
      have hx : 1 ≤ x := h x (by simp)
      have hxs : ∀ y ∈ xs, 1 ≤ y := by
        intro y hy
        apply h y
        simp [hy]
      specialize ih hxs
      -- x * foldl ≤ x * prod xs ≤ prod (x::xs)
      admit

-- ============================================
-- radical ≤ n（本体）
-- ============================================

theorem radical_le (n : Nat) :
  radical n ≤ n := by
  classical

  by_cases h : n < 2
  · simp [radical, get_factors, h]

  -- 全因子は n 以下
  have hle :
    ∀ x ∈ (get_factors n).eraseDups, x ≤ n := by
    intro x hx
    exact factor_le_n n x hx

  -- 全因子は ≥ 1
  have hone :
    ∀ x ∈ (get_factors n).eraseDups, 1 ≤ x := by
    intro x hx
    exact one_le_factor n x hx

  -- 積評価
  have hprod :
    (get_factors n).eraseDups.foldl (· * ·) 1 ≤ n := by
    -- 各因子 ≤ n かつ ≥1 → 積は n を超えない
    have h₁ : ∀ x ∈ (get_factors n).eraseDups, 1 ≤ x := hone
    have h₂ :
      (get_factors n).eraseDups.foldl (· * ·) 1
        ≤ Nat.prod (get_factors n).eraseDups := by
      apply foldl_le_of_le_one_mul
      exact h₁

    -- prod ≤ n（素因数の性質）
    have h₃ :
      Nat.prod (get_factors n).eraseDups ≤ n := by
      admit

    exact Nat.le_trans h₂ h₃

  exact hprod

end ABC
