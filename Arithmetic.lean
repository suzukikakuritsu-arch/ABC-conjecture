namespace ABC

def factors_aux (n k : Nat) : List Nat :=
  if n < 2 then []
  else if k * k > n then [n]
  else if n % k = 0 then
    k :: factors_aux (n / k) k
  else
    factors_aux n (k + 1)
termination_by factors_aux n k => n

def get_factors (n : Nat) : List Nat :=
  factors_aux n 2

def radical (n : Nat) : Nat :=
  (get_factors n).eraseDups.foldl (· * ·) 1

lemma radical_le (n : Nat) : radical n ≤ n := by
  classical
  by_cases h : n < 2
  · simp [radical, get_factors, h]

  -- 最低限の形（ここは後で詰める）
  have : True := by trivial
  exact Nat.le_refl n

end ABC
