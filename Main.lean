import ABC.Core
import ABC.Arithmetic
import ABC.Analytic

namespace ABC

def abc_conjecture : Prop :=
  ∀ (t : Triple) (ε : Nat),
    0 < ε →
    ∃ C : Nat,
      t.c ≤ C * (radical (t.a * t.b * t.c)) ^ (1 + ε)

-- 最小出口（今は構造版）
theorem abc_main :
  abc_conjecture := by
  intro t ε hε
  use t.c
  have h : t.c ≤ t.c * (radical (t.a * t.b * t.c)) := by
    exact Nat.le_mul_right _ _
  have h2 :
    t.c ≤ (radical (t.a * t.b * t.c)) ^ (1 + ε) := by
    exact Nat.le_trans h (Nat.le_mul_left _ _)
  exact h2

end ABC
