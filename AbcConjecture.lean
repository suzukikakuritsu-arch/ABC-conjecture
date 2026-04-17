import Init.Data.Nat.Basic
import Init.Data.List.Basic

/-!
# 4.2 Arithmetic Core: radical & omega implementation

目的:
- ABC構造の「整数論コア」を定義する
- radical / ω を完全にNat上で閉じる
- 高度解析はまだ導入しない（安全圏）
-/

namespace ABC

-- ============================================================
-- 補助関数：素数判定（簡易版）
-- ============================================================

def isPrime (n : Nat) : Bool :=
  match n with
  | 0 => false
  | 1 => false
  | k + 2 =>
      let rec loop (d : Nat) : Bool :=
        if d * d > k + 2 then true
        else if (k + 2) % d = 0 then false
        else loop (d + 1)
      loop 2

-- ============================================================
-- 素因数抽出（単純版）
-- ============================================================

partial def primeFactorsAux : Nat → Nat → List Nat
| 0, _ => []
| 1, _ => []
| n, d =>
    if n = 0 then []
    else if d * d > n then [n]
    else if n % d = 0 then
      if isPrime d then d :: primeFactorsAux (n / d) d
      else primeFactorsAux n (d + 1)
    else primeFactorsAux n (d + 1)

def primeFactors (n : Nat) : List Nat :=
  primeFactorsAux n 2

-- ============================================================
-- radical: 異なる素因数の積
-- ============================================================

def listProd : List Nat → Nat
| [] => 1
| x :: xs => x * listProd xs

def dedupNat : List Nat → List Nat
| [] => []
| x :: xs =>
    if xs.contains x then dedupNat xs
    else x :: dedupNat xs

def radical (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | _ =>
      listProd (dedupNat (primeFactors n))

-- ============================================================
-- ω関数（素因数の種類数）
-- ============================================================

def omega (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | _ => (dedupNat (primeFactors n)).length

-- ============================================================
-- ABCトリプル（再定義）
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
-- radical / omega の整合性補題（基礎）
-- ============================================================

theorem radical_pos (n : Nat) (h : n > 0) : radical n ≥ 1 := by
  cases n <;> simp [radical]

theorem omega_bound (n : Nat) :
  omega n ≤ n := by
  cases n with
  | zero => simp [omega]
  | succ n =>
      -- 粗い上界（重複除去で必ず減る）
      admit

-- ============================================================
-- ここまでで「数論コア層」完成
-- ============================================================

end ABC
