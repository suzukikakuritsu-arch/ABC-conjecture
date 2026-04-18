import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

/-- 根基 (radical) の決定論的計算 -/
def radical (n : Nat) : Nat :=
  if n = 0 then 0 else (n.primeFactorsList.eraseDups).foldl (· * ·) 1

/-- 次元の定義 -/
def omega (n : Nat) : Nat :=
  n.primeFactorsList.eraseDups.length

/-- 三つ組の高さ（エネルギー）の評価関数 -/
noncomputable def log_c (t : Triple) : ℝ := log (t.c : ℝ)

end ABC
