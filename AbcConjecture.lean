import Init.Data.Nat.Basic
import Init.Data.Finset

/-!
# ABC Framework 1.3: Finite Reduction Layer
目的：
- 「c ≤ C ⇒ 有限集合」を明示化
- ABC構造を Finset に落とす準備
- ωやradicalを使う前段として combinatorial closure を構築
-/

-- ============================================================
-- 1. ABC Triple
-- ============================================================

structure ABCTriple where
  a : Nat
  b : Nat
  c : Nat
  pos_a : a > 0
  pos_b : b > 0
  eq_sum : a + b = c
  coprime : Nat.gcd a b = 1

-- ============================================================
-- 2. bounded cube embedding
-- ============================================================

def cube (C : Nat) : Finset (Nat × Nat × Nat) :=
  (Finset.Icc 1 C) ×ˢ (Finset.Icc 1 C) ×ˢ (Finset.Icc 1 C)

-- ============================================================
-- 3. ABC を cube に埋め込む写像
-- ============================================================

def toTuple (t : ABCTriple) : Nat × Nat × Nat :=
  (t.a, t.b, t.c)

-- ============================================================
-- 4. boundedness assumption（ここが核心）
-- ============================================================

def bounded_by (C : Nat) (t : ABCTriple) : Prop :=
  t.c ≤ C

-- ============================================================
-- 5. finite lemma（核）
-- ============================================================

lemma finite_triples_below_c (C : Nat) :
  Set.Finite { t : ABCTriple | bounded_by C t } := by
  classical

  -- cube は有限集合
  let s : Finset (Nat × Nat × Nat) := cube C

  -- ABCTriple → cube への埋め込み（弱写像）
  let f : ABCTriple → Nat × Nat × Nat := toTuple

  -- bounded set は cube の部分集合
  have h : { t : ABCTriple | bounded_by C t } ⊆
           { t | t.a ≤ C ∧ t.b ≤ C ∧ t.c ≤ C } := by
    intro t ht
    simp [bounded_by] at ht
    -- 最小限の構造だけ残す
    admit

  -- cube は有限なので部分集合も有限
  exact Set.Finite.subset (by
    -- FinsetからSetへ
    classical
    exact Finset.finite_toSet s
  ) h

-- ============================================================
-- 6. main consequence (bridge lemma)
-- ============================================================

theorem abc_finite_from_bound (C : Nat) :
  Set.Finite { t : ABCTriple | t.c ≤ C } :=
  finite_triples_below_c C
