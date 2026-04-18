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

def radical (n : Nat) : Nat :=
  if n = 0 then 0 
  else (n.primeFactorsList.eraseDups).foldl (· * ·) 1

def omega (n : Nat) : Nat :=
  (n.primeFactorsList.eraseDups).length

lemma c_pos_real (t : Triple) : 0 < (t.c : ℝ) := cast_pos.mpr t.pos_c

end ABC
