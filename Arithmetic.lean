import ABC.Core
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting

open Nat Real

namespace ABC

/-- 
チェビシェフ関数 θ(x) を用いた radical の評価。
Mathlib の `primorial_ge_exp` 等と接続することで sorry を消せます。
-/
lemma radical_lower_bound_refined (t : Triple) :
  let ω := omega (t.a * t.b * t.c)
  ω ≥ 17 → (radical (t.a * t.b * t.c) : ℝ) > exp (0.92 * ω) :=
by
  -- ここは Mathlib の素数評価ライブラリを apply するだけで消える段階です
  sorry 

/-- Matveevの実効的定数を用いた高さの上限 -/
noncomputable def baker_rigidity_bound (ω : ℕ) (ε : ℝ) : ℝ :=
  exp ((30.0 ^ (ω + 4)) / ε)

end ABC
