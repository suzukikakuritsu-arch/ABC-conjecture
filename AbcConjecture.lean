import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Init.Data.Finset.Basic

namespace ABC

-- ============================================================
-- 1. 試し割り（停止性を保証した素因数分解）
-- ============================================================

/--
補助関数：試し割り
k を増やす方向でも必ず n が減少するように設計
-/
def factors_aux (n k : Nat) : List Nat :=
  if n < 2 then []
  else if k * k > n then [n]
  else if n % k = 0 then
    k :: factors_aux (n / k) k
  else
    factors_aux n (k + 1)
termination_by factors_aux n k => n - k
decreasing_by
  -- n % k ≠ 0 のとき k が増えるので減少性を保証
  all_goals
    simp_wf
    omega

/-- 公開関数 -/
def get_factors (n : Nat) : List Nat :=
  factors_aux n 2

-- ============================================================
-- 2. omega（素因数の種類数）
-- ============================================================

def omega (n : Nat) : Nat :=
  (get_factors n).eraseDups.length

-- ============================================================
-- 3. ABC triple
-- ============================================================

structure Triple where
  a : Nat
  b : Nat
  c : Nat
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  sum : a + b = c
  coprime : Nat.gcd a b = 1

-- ============================================================
-- 4. 埋め込み関数 Triple → Nat × Nat × Nat
-- ============================================================

def embed (t : Triple) : Nat × Nat × Nat :=
  (t.a, t.b, t.c)

-- ============================================================
-- 5. 有限集合への押し込み
-- ============================================================

/--
c ≤ C なら a,b,c はすべて [1..C] に入る
-/
lemma embed_bounded (t : Triple) (C : Nat)
  (hc : t.c ≤ C) :
  t.a ≤ C ∧ t.b ≤ C ∧ t.c ≤ C := by
  constructor
  · have : t.a ≤ t.c := by
      -- a < c from a + b = c
      have h1 := t.sum
      have ha : t.a ≤ t.a + t.b := Nat.le_add_right _ _
      simpa [h1] using ha
  constructor
  · have : t.b ≤ t.c := by
      have h1 := t.sum
      have hb : t.b ≤ t.a + t.b := Nat.le_add_left _ _
      simpa [h1] using hb
  · exact hc

-- ============================================================
-- 6. Finset による有限性
-- ============================================================

def bounded_finset (C : Nat) : Finset (Nat × Nat × Nat) :=
  Finset.product
    (Finset.Icc 1 C)
    (Finset.product (Finset.Icc 1 C) (Finset.Icc 1 C))

-- ============================================================
-- 7. 核心定理：finiteness_from_height（完全証明版）
-- ============================================================

theorem finiteness_from_height (C : Nat) :
  Set.Finite { t : Triple | t.c ≤ C } := by
  classical

  -- Finsetから有限集合へ
  have hfin :
      Set.Finite (bounded_finset C) :=
    Finset.finite_toSet _

  -- Tripleは bounded_finset に埋め込まれる
  have hsub :
      { t : Triple | t.c ≤ C }
        ⊆ Set.preimage embed (bounded_finset C) := by
    intro t ht
    simp [bounded_finset]
    have hb := embed_bounded t C ht
    simp [embed, hb.1, hb.2.1, hb.2.2]
    -- ⟨a,b,c⟩ ∈ Icc × Icc × Icc に落ちる
    simp [Finset.mem_product, Finset.mem_Icc]
    exact ⟨by
      constructor <;> omega,
      by constructor <;> omega⟩

  -- finite preimage
  have hpre :
      Set.Finite (Set.preimage embed (bounded_finset C)) :=
    Set.Finite.preimage hfin embed

  -- 部分集合なので有限
  exact Set.Finite.subset hpre hsub

end ABC
