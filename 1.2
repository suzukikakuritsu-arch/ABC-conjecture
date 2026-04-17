lemma finite_triples_below_c (C : ℕ) :
  Set.Finite { t : ABCTriple | t.c ≤ C } := by
  classical

  -- 1. 有限集合の土台（1..C）
  let s : Finset ℕ := Finset.Icc 1 C

  -- 2. 全候補空間（a,b,c の直積）
  let triples : Finset (ℕ × ℕ × ℕ) := s ×ˢ s ×ˢ s

  -- 3. ABCTriple → ℕ³ への埋め込み
  let f : ABCTriple → ℕ × ℕ × ℕ :=
    fun t => (t.a, t.b, t.c)

  -- 4. bounded set は triples の部分集合
  have hsubset :
    { t : ABCTriple | t.c ≤ C } ⊆ f ⁻¹' triples := by
  intro t ht
  simp only [Set.mem_setOf_eq, Set.mem_preimage, triples]
  -- a, b ≤ c ≤ C を使う（正確には a,b ≥ 1, a+b=c）
  have ha : t.a ≤ C := by
    have : t.a < t.c := by
      have := t.eq_sum
      have hpos : 0 < t.b := t.pos_b
      linarith
    linarith [ht]
  have hb : t.b ≤ C := by
    have : t.b < t.c := by
      have := t.eq_sum
      have hpos : 0 < t.a := t.pos_a
      linarith
    linarith [ht]
  have hc : t.c ≤ C := ht

  simp [s, Finset.mem_Icc]
  constructor
  · exact ⟨by linarith [t.pos_a], ha⟩
  constructor
  · exact ⟨by linarith [t.pos_b], hb⟩
  · exact ⟨by simp, hc⟩

  -- 5. 有限集合への帰着
  have hfin : Set.Finite (f ⁻¹' triples) := by
    exact Set.Finite.preimage f triples.finite_toSet

  -- 6. 部分集合なので有限
  exact Set.Finite.subset hfin hsubset
