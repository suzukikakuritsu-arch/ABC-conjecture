def factors_aux (n k : Nat) : List Nat :=
  if n < 2 then []
  else if k * k > n then [n]
  else if n % k = 0 then
    k :: factors_aux (n / k) k
  else
    factors_aux n (k + 1)
termination_by factors_aux n k => n - k
decreasing_by
  all_goals simp_wf; omega

def get_factors (n : Nat) : List Nat :=
  factors_aux n 2

def omega (n : Nat) : Nat :=
  (get_factors n).eraseDups.length

def radical (n : Nat) : Nat :=
  (get_factors n).eraseDups.foldl (· * ·) 1

lemma a_lt_c (t : Triple) : t.a < t.c := by
  have := t.sum
  exact Nat.lt_of_le_of_ne (Nat.le_add_right _ _) (by simp [*])

lemma b_lt_c (t : Triple) : t.b < t.c := by
  have := t.sum
  exact Nat.lt_of_le_of_ne (Nat.le_add_left _ _) (by simp [*])

lemma embed_bounded (t : Triple) (C : Nat) (hc : t.c ≤ C) :
  embed t ∈ Finset.Icc 1 C ×ˢ (Finset.Icc 1 C ×ˢ Finset.Icc 1 C) := by
  simp [embed]
  simp [Finset.mem_product, Finset.mem_Icc]
  constructor <;> constructor <;> constructor <;> try exact hc <;> try
    exact Nat.succ_le_of_lt (by
      cases a_lt_c t <;> cases b_lt_c t <;> assumption)
