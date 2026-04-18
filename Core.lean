import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.GCD.Basic

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

/-- radical（根基）の定義 -/
noncomputable def radical (n : Nat) : Nat :=
  if n = 0 then 0 else (n.primeFactorsList.eraseDups).foldl (· * ·) 1

/-- ω（素因子の種類数）の定義 -/
def omega (n : Nat) : Nat :=
  n.primeFactorsList.eraseDups.length

end ABC
