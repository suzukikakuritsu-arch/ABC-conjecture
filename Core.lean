structure Triple where
  a : Nat
  b : Nat
  c : Nat
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  sum : a + b = c
  coprime : Nat.gcd a b = 1

def embed (t : Triple) : Nat × Nat × Nat :=
  (t.a, t.b, t.c)
