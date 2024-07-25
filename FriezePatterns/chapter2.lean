import FriezePatterns.chapter1

-- Chapter 2: Frieze patterns (i.e. "positive" field-valued patterns)
-- Section 1: Infinite frieze patterns

class inftyFrieze (f : ℕ × ℕ → ℚ) extends pattern ℚ f where
  positive : ∀ m, ∀ i, f (i,m) > 0

-- An infinite frieze is nowhere zero
lemma friezeNonZero (f : ℕ×ℕ → ℚ) [inftyFrieze f] (i : ℕ) (m : ℕ): f (i,m) ≠ 0 := by
  apply LT.lt.ne'
  exact inftyFrieze.positive m i


-- Section 2: bounded frieze patterns
class frieze_n (f : ℕ × ℕ → ℚ) (n : ℕ) : Prop where
  topBordOnes : ∀ m, f (0,m) =1
  diamond : ∀ m, ∀ i,  f (i+1,m) * f (i+1,m+1) -1= f (i+2,m)*f (i,m+1)
  positive_n : ∀ m, ∀ i, i ≤ n ∧ f (i,m) > 0
  botBordOnes_n : ∀ m, f (n, m) = 1
