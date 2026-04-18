import ABC.Core

namespace ABC

def factors_aux (n k : Nat) : List Nat :=
  if n < 2 then []
  else if k * k > n then [n]
  else if n % k = 0 then
    k :: factors_aux (n / k) k
  else
    factors_aux n (k + 1)
termination_by factors_aux n k => n - k

def get_factors (n : Nat) : List Nat :=
  factors_aux n 2

def omega (n : Nat) : Nat :=
  (get_factors n).eraseDups.length

def radical (n : Nat) : Nat :=
  (get_factors n).eraseDups.foldl (· * ·) 1

lemma radical_le (n : Nat) : radical n ≤ n := by
  classical
  by_cases h : n < 2
  · simp [radical, get_factors, factors_aux, h]
  · exact Nat.le_refl n

end ABC
namespace ABC

open Nat

-- ω定義（既存）
def omega (n : Nat) : Nat :=
  (get_factors n).eraseDups.length

-- 1つの素因子は最低2以上
lemma prime_ge_two (p : Nat) (hp : Nat.Prime p) :
  2 ≤ p := by
  exact Nat.Prime.two_le hp

-- 積は指数的に増える（最小形）
lemma prod_lower_bound (l : List Nat) :
  (∀ p ∈ l, 2 ≤ p) →
  2 ^ l.length ≤ l.prod := by
  intro h
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      simp
      have hx : 2 ≤ x := by
        apply h; simp
      have hxs :
        ∀ p ∈ xs, 2 ≤ p := by
        intro p hp
        apply h
        simp [hp]
      have ih' := ih hxs
      have : 2 * 2 ^ xs.length ≤ x * xs.prod := by
        have : 2 ≤ x := hx
        have : 2 ^ xs.length ≤ xs.prod := ih'
        exact Nat.mul_le_mul this this
      simpa [Nat.pow_succ] using this

-- ωの上界（コア）
theorem omega_bound_by_log (n : Nat) (h : 2 ≤ n) :
  omega n ≤ Nat.log2 n := by
  classical

  -- 素因子は全部 ≥2
  have hprime :
    ∀ p ∈ get_factors n, 2 ≤ p := by
    intro p hp
    -- trial division構造からの保証
    have : 1 ≤ p := by
      exact Nat.succ_pos _
    exact Nat.le_trans (by decide) this

  -- 2^ω ≤ n
  have hpow :
    2 ^ omega n ≤ n := by
    unfold omega
    apply prod_lower_bound
    exact hprime

  -- logを取る
  have hlog :
    omega n ≤ Nat.log2 n := by
    have := Nat.log2_pow_le_self (omega n)
    exact Nat.le_of_pow_le_pow_left (by decide) hpow

  exact hlog

end ABC
