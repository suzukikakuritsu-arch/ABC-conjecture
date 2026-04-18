import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-- 三つ組 (a, b, c) の定義と基本性質 -/
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

/-- 根基 (radical) の定義 -/
def radical (n : Nat) : Nat :=
  if n = 0 then 0 
  else (n.primeFactorsList.eraseDups).foldl (· * ·) 1

/-- 次元の定義（素因数の種類数） -/
def omega (n : Nat) : Nat :=
  (n.primeFactorsList.eraseDups).length

/-- 実数解析への橋渡し補題 -/
lemma c_pos_real (t : Triple) : 0 < (t.c : ℝ) := cast_pos.mpr t.pos_c

end ABC
