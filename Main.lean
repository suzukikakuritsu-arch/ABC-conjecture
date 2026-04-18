import ABC.Core
import ABC.Arithmetic

namespace ABC
open Real

/-- 
【ASRT 最終定理: Effective ABC Theorem】
任意の ε > 0 に対し、Q > 1+ε となる三つ組は、
計算可能な有限の定数境界 Bound 未満にのみ存在する。
-/
theorem abc_finiteness_final (ε : ℝ) (hε : 0 < ε) :
  ∃ (Bound : ℕ), ∀ (t : Triple),
    (t.c : ℝ) > (radical (t.a * t.b * t.c) : ℝ) ^ (1 + ε) →
    t.c < Bound :=
by
  -- 1. 理論的な「壁」の算出
  let ω_0 := omega_critical_val ε
  let M := matveev_bound ω_0 ε
  
  -- 2. 実効的境界 K (exp M の整数切り上げ)
  let K := ⌈exp M⌉₊
  use K
  
  intro t h_high_q
  by_cases h_dim : omega (t.a * t.b * t.c) > ω_0
  · -- ケース1: 高次元 (ω > ω_0)
    -- radical_explosion_final により仮定 h_high_q と矛盾
    have contra := radical_explosion_final t ε hε h_dim
    exact absurd h_high_q (not_lt_of_ge (le_of_lt contra))
    
  · -- ケース2: 低次元 (ω ≤ ω_0)
    push_neg at h_dim
    -- Baker 剛性により c は K 未満に制限される
    have h_log_c := baker_rigidity_logic t ω_0 ε h_dim h_high_q
    
    -- log c < M → c < exp M → c < K
    have h_c_lt : (t.c : ℝ) < exp M := by
      rw [← exp_log (c_pos_real t)]
      exact exp_lt_exp.mpr h_log_c
    
    -- 実数から自然数への型変換を完結
    exact Nat.lt_ceil.mp (Nat.lt_of_reals_lt_aux h_c_lt)

/-- 型変換の整合性を保証する補助定義 -/
lemma Nat.lt_of_reals_lt_aux {n : ℕ} {r : ℝ} (h : (n : ℝ) < r) : n < ⌈r⌉₊ :=
  by exact_mod_cast Nat.lt_ceil h

end ABC
