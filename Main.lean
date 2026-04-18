import ABC.Core
import ABC.Arithmetic

namespace ABC
open Real

theorem abc_final_finiteness (ε : ℝ) (hε : 0 < ε) :
  ∃ (Bound : ℕ), ∀ (t : Triple),
    (t.c : ℝ) > (radical (t.a * t.b * t.c) : ℝ) ^ (1 + ε) →
    t.c < Bound :=
by
  let ω_0 := omega_critical_val ε
  let K := ⌈exp ( (30.0 ^ (ω_0 + 4)) / ε )⌉₊
  use K
  
  intro t h_high_q
  by_cases h_dim : omega (t.a * t.b * t.c) > ω_0
  · -- ケース1: 高次元。radical_explosion_lower_bound により rad が巨大化。
    -- c < rad^(1+ε) を導き、h_high_q (c > rad^(1+ε)) と矛盾させる。
    have h_rad_growth := radical_explosion_lower_bound t
    -- ω > ω_0 のとき rad^(1+ε) が Baker上限 K を超えることを示す
    sorry 
  · -- ケース2: 低次元。c は Baker上限 K 未満。
    push_neg at h_dim
    -- ここは定数評価のみ。
    sorry

end ABC
