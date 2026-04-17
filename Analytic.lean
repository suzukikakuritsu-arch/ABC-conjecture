axiom omega_collapse :
  ∃ ω₀ : Nat, ∀ t : Triple,
    omega (t.a * t.b * t.c) ≤ ω₀

axiom effective_baker :
  ∀ ω₀ : Nat,
    ∃ C : Nat, ∀ t : Triple,
      omega (t.a * t.b * t.c) ≤ ω₀ →
      t.c ≤ C
