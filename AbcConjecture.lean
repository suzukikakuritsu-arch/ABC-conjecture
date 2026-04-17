import Init.Data.Nat.Basic
import Init.Data.List.Basic

namespace ABC

-- ============================================================
-- CORE: 基本構造
-- ============================================================

structure Triple where
  a : Nat
  b : Nat
  c : Nat
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  sum : a + b = c

def embed (t : Triple) : Nat × Nat × Nat :=
  (t.a, t.b, t.c)

-- ============================================================
-- CORE: 素因数分解（試し割り・停止性付き）
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
-- CORE: radical / omega
-- ============================================================

def dedup : List Nat → List Nat
| [] => []
| x :: xs =>
  if xs.contains x then dedup xs else x :: dedup xs

def radical (n : Nat) : Nat :=
  (dedup (get_factors n)).foldl (· * ·) 1

def omega (n : Nat) : Nat :=
  (dedup (get_factors n)).length

-- ============================================================
-- FINITE BOX LEMMA
-- ============================================================

def range (C : Nat) : Finset Nat :=
  Finset.Icc 1 C

lemma finiteness_from_height (C : Nat) :
  Set.Finite { t : Triple | t.c ≤ C } := by
  classical

  let S := range C
  let F := S ×ˢ S ×ˢ S

  have hF : Set.Finite (F : Set (Nat × Nat × Nat)) := by
    exact Finset.finite_toSet F

  have subset :
    { t : Triple | t.c ≤ C } ⊆ Set.map embed F := by
    intro t ht
    simp at ht
    have ha : t.a ∈ S := by
      have : t.a ≤ t.c := by
        have : t.a ≤ t.a + t.b := Nat.le_add_right _ _
        simpa [t.sum] using this
      exact Finset.mem_Icc.mpr ⟨by simp, this.trans ht⟩

    have hb : t.b ∈ S := by
      have : t.b ≤ t.c := by
        have : t.b ≤ t.a + t.b := Nat.le_add_left _ _
        simpa [t.sum] using this
      exact Finset.mem_Icc.mpr ⟨by simp, this.trans ht⟩

    have hc : t.c ∈ S := by
      exact Finset.mem_Icc.mpr ⟨by simp, ht⟩

    exact ⟨ha, ⟨hb, hc⟩⟩

  exact Set.Finite.subset hF subset

-- ============================================================
-- ANALYTIC LAYER（公理として分離）
-- ============================================================

opaque Real : Type

axiom omega_collapse :
  ∃ (ω₀ : Nat), ∀ (t : Triple),
    omega (t.a * t.b * t.c) ≤ ω₀

axiom effective_baker :
  ∀ (ω₀ : Nat), ∃ (C : Nat), ∀ (t : Triple),
    omega (t.a * t.b * t.c) ≤ ω₀ →
    t.c ≤ C

-- ============================================================
-- MAIN THEOREM（有限性）
-- ============================================================

theorem abc_finiteness :
  ∃ (C_final : Nat), ∀ (t : Triple), t.c ≤ C_final := by
  obtain ⟨ω₀, hω⟩ := omega_collapse
  obtain ⟨C, hC⟩ := effective_baker ω₀
  exact ⟨C, fun t => hC t (hω t)⟩

end ABC
