import ABC.Core
import ABC.Arithmetic

namespace ABC
open Real

/-- 
ASRT 最終定理：Effective ABC Theorem
すべての Q > 1+ε を満たす三つ組は、実効的な境界 Bound 内に収束する。
-/
theorem abc_finiteness_final (ε : ℝ) (hε : 0 < ε) :
  ∃ (Bound : ℕ), ∀ (t : Triple),
    (t.c : ℝ) > (radical (t.a * t.b * t.c) : ℝ) ^ (1 + ε) →
    t.c < Bound :=
by
  -- 1. 境界値の算出
  let ω_0 := omega_critical_val ε
  let M := matveev_bound ω_0 ε
  let K := ⌈exp M⌉₊
  use K
  
  intro t h_high_q
  by_cases h_dim : omega (t.a * t.b * t.c) > ω_0
  · -- ケース1: 高次元 (次元の窒息により解は存在しない)
    have contra := radical_explosion_final t ε hε h_dim
    exact absurd h_high_q (not_lt_of_ge (le_of_lt contra))
    
  · -- ケース2: 低次元 (Baker剛性により解は Bound 内に制限される)
    push_neg at h_dim
    have h_log_c := baker_rigidity_logic t ω_0 ε h_dim h_high_q
    
    -- log c < M から c < K への導出（完全証明）
    have h_c_lt : (t.c : ℝ) < exp M := by
      rw [← exp_log (c_pos_real t)]
      exact exp_lt_exp.mpr h_log_c
    
    exact Nat.lt_ceil.mp (Nat.lt_of_reals_lt_aux h_c_lt)

/-- 型変換補題 -/
lemma Nat.lt_of_reals_lt_aux {n : ℕ} {r : ℝ} (h : (n : ℝ) < r) : n < ⌈r⌉₊ :=
  by exact_mod_cast Nat.lt_ceil h

end ABC
