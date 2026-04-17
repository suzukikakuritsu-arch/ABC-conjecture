import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Nat
open Real
open BigOperators

-- ============================================================
-- 1. ABC Triple
-- ============================================================

structure ABCTriple where
  a : ℕ
  b : ℕ
  c : ℕ
  pos_a : 0 < a
  pos_b : 0 < b
  eq_sum : a + b = c
  coprime : Nat.gcd a b = 1

-- ============================================================
-- 2. Radical
-- ============================================================

noncomputable def radical (n : ℕ) : ℕ :=
if n = 0 then 0 else (Nat.factorization n).support.prod

-- ============================================================
-- 3. Quality
-- ============================================================

noncomputable def quality (t : ABCTriple) : ℝ :=
  Real.log (t.c : ℝ) / Real.log (radical (t.a * t.b * t.c) : ℝ)

-- ============================================================
-- 4. omega
-- ============================================================

noncomputable def omega (n : ℕ) : ℕ :=
  (Nat.factorization n).support.card

-- ============================================================
-- 5. AXIOM: Effective Baker rigidity
-- ============================================================

axiom effective_baker :
  ∀ (ω₀ : ℕ) (ε : ℝ),
    ∃ (Cε : ℕ), ∀ (t : ABCTriple),
      omega (t.a * t.b * t.c) ≤ ω₀ →
      quality t > 1 + ε →
      t.c ≤ Cε

-- ============================================================
-- 6. LEMMA: finite set under bounded c
-- ============================================================

lemma bounded_triple_embedding (C : ℕ) :
  { t : ABCTriple | t.c ≤ C } ⊆ (↑(Finset.Icc 1 C ×ˢ Finset.Icc 1 C ×ˢ Finset.Icc 1 C) : Set (ℕ × ℕ × ℕ)) := by
  intro t ht
  simp at *
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · constructor; exact t.pos_a; linarith [t.pos_a, t.pos_b, t.eq_sum, ht]
  · constructor; exact t.pos_b; linarith [t.pos_a, t.pos_b, t.eq_sum, ht]
  · constructor; linarith [t.pos_a, t.pos_b, t.eq_sum]; exact ht

lemma finite_triples_below_c (C : ℕ) :
  Set.Finite { t : ABCTriple | t.c ≤ C } := by
  apply Set.Finite.subset (Finset.finite_toSet _)
  exact bounded_triple_embedding C

-- ============================================================
-- 7. ω-collapse
-- ============================================================

theorem omega_collapse (ε : ℝ) (hε : 0 < ε) :
  ∃ (ω₀ : ℕ), ∀ (t : ABCTriple),
    quality t > 1 + ε → omega (t.a * t.b * t.c) ≤ ω₀ := by
  sorry

-- ============================================================
-- 8. MAIN THEOREM
-- ============================================================

theorem abc_finiteness (ε : ℝ) (hε : 0 < ε) :
  Set.Finite { t : ABCTriple | quality t > 1 + ε } := by
  classical
  obtain ⟨ω₀, hω⟩ := omega_collapse ε hε
  obtain ⟨Cε, hC⟩ := effective_baker ω₀ ε
  have hsubset : { t : ABCTriple | quality t > 1 + ε } ⊆ { t : ABCTriple | t.c ≤ Cε } := by
    intro t ht
    exact hC t (hω t ht) ht
  exact Set.Finite.subset (finite_triples_below_c Cε) hsubset
