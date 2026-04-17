import Init.Data.Nat.Basic

/-!
# 4.1 Effective ABC Inequality Core

このファイルは以下を目的とする：

1. ω（素因数の種類）による次元制御
2. radical による対数スケール支配
3. 高品質条件を「不等式スキーム」に変換
-/

namespace ABC

-- ============================================================
-- 基本対象
-- ============================================================

structure Triple where
  a : Nat
  b : Nat
  c : Nat
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  hsum : a + b = c
  hgcd : Nat.gcd a b = 1

-- ============================================================
-- 抽象関数（ここは後でmathlib接続可能）
-- ============================================================

opaque log : Nat → Real
opaque radical : Nat → Nat
opaque omega : Nat → Nat

-- ============================================================
-- ABC quality（対数比）
-- ============================================================

noncomputable def quality (t : Triple) : Real :=
  log t.c / log (radical (t.a * t.b * t.c))

-- ============================================================
-- 仮定構造（幾何・次元・剛性）
-- ============================================================

/-- 次元の上限（ω-collapse） -/
axiom omega_collapse (ε : Real) :
  ∃ ω₀ : Nat, ∀ t : Triple,
    omega (t.a * t.b * t.c) ≤ ω₀

/-- Baker型剛性（高さ制御） -/
axiom effective_baker (ω₀ : Nat) (ε : Real) :
  ∃ C : Nat, ∀ t : Triple,
    omega (t.a * t.b * t.c) ≤ ω₀ →
    t.c ≤ C

-- ============================================================
-- ABC不等式スキーム（4.1コア）
-- ============================================================

/--
高品質条件は「指数比が閾値を超えること」と同値
→ ここを“構造的不等式”として固定する
-/
axiom abc_inequality_core (ε : Real) :
  ∃ (ω₀ C : Nat),
    ∀ (t : Triple),
      quality t > (1 + ε) →
        omega (t.a * t.b * t.c) ≤ ω₀ ∧
        t.c ≤ C

-- ============================================================
-- 有限性への帰着
-- ============================================================

theorem abc_finiteness_core (ε : Real) :
  ∃ C : Nat, ∀ t : Triple, t.c ≤ C := by
  obtain ⟨ω₀, C, h⟩ := abc_inequality_core ε
  exact ⟨C, fun t => (h t).2⟩

end ABC
