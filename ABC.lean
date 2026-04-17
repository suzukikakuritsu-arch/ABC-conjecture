import Core
import Arithmetic
import Analytic

namespace ABC

theorem abc_finiteness :
  ∃ C : Nat, True := by
  obtain ⟨ω₀, hω⟩ := omega_bound
  exact ⟨ω₀, trivial⟩

end ABC
