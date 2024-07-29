import FriezePatterns.Chapter1.section1

-- Chapter 1: Background on frieze patterns
-- Section 2: Frieze patterns (i.e. "positive" field-valued patterns)
-- Infinite frieze patterns

class inftyFrieze (F : Type*) [LinearOrderedField F] (f : ℕ × ℕ → F) extends nzPattern F f where
positive : ∀ i, ∀ m, f (i,m) > 0

-- An infinite frieze is nowhere zero
lemma friezeNonZero (F : Type*) [LinearOrderedField F]  (f : ℕ×ℕ → F) [inftyFrieze F f] (i : ℕ) (m : ℕ): f (i,m) ≠ 0 := by
  exact nzPattern.non_zero i m


-- Bounded frieze patterns
class frieze_n (f : ℕ × ℕ → ℚ) (n : ℕ) : Prop where
  topBordOnes : ∀ m, f (0,m) =1
  diamond : ∀ m, ∀ i,  f (i+1,m) * f (i+1,m+1) -1= f (i+2,m)*f (i,m+1)
  positive_n : ∀ m, ∀ i, i ≤ n ∧ f (i,m) > 0
  botBordOnes_n : ∀ m, f (n, m) = 1
