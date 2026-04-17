namespace ABC

axiom omega : Nat → Nat

axiom omega_bound :
  ∃ ω₀ : Nat, ∀ n, omega n ≤ ω₀

end ABC
