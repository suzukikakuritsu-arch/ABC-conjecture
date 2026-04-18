import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-- 三つ組 (a, b, c) の定義 -/
structure Triple where
  a : Nat
  b : Nat
  c : Nat
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  sum : a + b = c
  coprime : Nat.gcd a b = 1

namespace ABC
open Nat Real

/-- radical の実効的計算 -/
def radical (n : Nat) : Nat :=
  if n = 0 then 0 else (n.primeFactorsList.eraseDups).foldl (· * ·) 1

/-- 素因数の種類数 ω の計算 -/
def omega (n : Nat) : Nat :=
  n.primeFactorsList.eraseDups.length

/-- 品質 Q の実数定義 -/
noncomputable def quality (t : Triple) : ℝ :=
  log t.c / log (radical (t.a * t.b * t.c))

end ABC
