import Init.Data.Nat.Basic
import Init.Data.List.Basic

namespace ABC

-- ============================================================
-- 1. Trial Division（停止性付き素因数分解）
-- ============================================================

def factors_aux : Nat → Nat → List Nat
| n, k =>
  if n < 2 then []
  else if k * k > n then [n]
  else if n % k = 0 then
    k :: factors_aux (n / k) k
  else
    factors_aux n (k + 1)

termination_by factors_aux n k => n - k

def get_factors (n : Nat) : List Nat :=
  factors_aux n 2

-- ============================================================
-- 2. radical / omega
-- ============================================================

def dedup (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x :: xs =>
    if xs.contains x then dedup xs else x :: dedup xs

def radical (n : Nat) : Nat :=
  (dedup (get_factors n)).foldl (fun a b => a * b) 1

def omega (n : Nat) : Nat :=
  (dedup (get_factors n)).length

-- ============================================================
-- 3. ABC Triple
-- ============================================================

structure Triple where
  a : Nat
  b : Nat
  c : Nat
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  sum : a + b = c

-- ============================================================
-- 4. 埋め込み関数 (Triple → ℕ × ℕ × ℕ)
-- ============================================================

def embed (t : Triple) : Nat × Nat × Nat :=
  (t.a, t.b, t.c)

-- ============================================================
-- 5. Finset補助
-- ============================================================

def range (C : Nat) : Finset Nat :=
  Finset.Icc 1 C

-- ============================================================
-- 6. 有限性補題（核）
-- ============================================================

lemma finiteness_from_height (C : Nat) :
  Set.Finite { t : Triple | t.c ≤ C } := by
  classical

  let S := range C
  let F := S ×ˢ S ×ˢ S

  have hF : Set.Finite (F : Set (Nat × Nat × Nat)) := by
    exact Finset.finite_toSet F

  -- Tripleは(a,b,c)に埋め込める
  have inj :
    ∀ t : Triple,
      t.c ≤ C →
      embed t ∈ (F : Set (Nat × Nat × Nat)) := by
    intro t htc
    simp [embed, F, S, range]
    -- a,b,c ≤ C に帰着（最小構造なので明示的に仮定）
    have ha : t.a ∈ range C := by
      have : t.a ≤ t.c := by
        have : 0 < t.b := t.pos_b
        have : t.a ≤ t.a + t.b := Nat.le_add_right _ _
        simpa [t.sum] using this
      exact Finset.mem_Icc.mpr ⟨by simp, this.trans htc⟩

    have hb : t.b ∈ range C := by
      have : t.b ≤ t.c := by
        have : 0 < t.a := t.pos_a
        have : t.b ≤ t.a + t.b := Nat.le_add_left _ _
        simpa [t.sum] using this
      exact Finset.mem_Icc.mpr ⟨by simp, this.trans htc⟩

    have hc : t.c ∈ range C := by
      exact Finset.mem_Icc.mpr ⟨by simp, htc⟩

    simp [range] at ha hb hc
    exact ⟨ha, ⟨hb, hc⟩⟩

  -- ここが核心：有限集合への写像
  have subset :
    { t : Triple | t.c ≤ C } ⊆ Set.map embed F := by
    intro t ht
    simp at ht
    exact ⟨t, by
      constructor
      · exact inj t ht
      · simp [F, range]⟩

  exact Set.Finite.subset hF subset

end ABC
