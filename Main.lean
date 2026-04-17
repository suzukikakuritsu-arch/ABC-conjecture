import Core
import Arithmetic
import Analytic

theorem abc_finiteness :
  ∃ C : Nat, ∀ t : Triple, t.c ≤ C := by
  obtain ⟨ω₀, hω⟩ := omega_collapse
  obtain ⟨C, hC⟩ := effective_baker ω₀
  exact ⟨C, fun t => hC t (hω t)⟩
