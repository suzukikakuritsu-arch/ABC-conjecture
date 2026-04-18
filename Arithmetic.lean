import ABC.Core
import ABC.Arithmetic

namespace ABC

open Real

/-- 
定理: Effective ABC Conjecture (ASRT-Structure)
任意の ε > 0 に対し、Q > 1+ε となる三つ組は「有限の定数領域」に限定される。
-/
theorem abc_effective_closure (ε : ℝ) (hε : 0 < ε) :
  ∃ (Bound : ℕ), ∀ (t : Triple),
    (t.c : ℝ) > (radical (t.a * t.b * t.c) : ℝ) ^ (1 + ε) →
    t.c < Bound :=
by
  -- 1. ε に応じた臨界次元 ω_0 を取得（定量）
  obtain ⟨ω_0, h_collapse⟩ := omega_collapse ε hε
  
  -- 2. 固定された ω_0 に対する Baker 上限 K を取得（実効）
  obtain ⟨K, h_baker⟩ := baker_rigidity ω_0 ε
  
  -- 3. K を全体の境界 Bound として採用
  use K
  intro t h_high_q
  
  -- 次元による分岐
  by_cases h_dim : omega (t.a * t.b * t.c) > ω_0
  · -- ケース1: 高次元。omega_collapse により c < rad^(1+ε) となり矛盾。
    have contra := h_collapse t h_dim
    exact absurd h_high_q (not_lt_of_ge (le_of_lt contra))
    
  · -- ケース2: 低次元。baker_rigidity により c < K が確定。
    push_neg at h_dim
    exact h_baker t h_dim h_high_q

end ABC
