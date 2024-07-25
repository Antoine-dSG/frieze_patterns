import FriezePatterns.chapter1
import FriezePatterns.chapter2
-- Chapter 3: Arithmetic frieze patterns (i.e. "positive integral" field-valued patterns)
-- Section 1: Infinite arithmetic frieze patterns

-- Section 2: bounded arithmetic frieze patterns


-- We now need to define arithmetic frieze patterns
class arithFrieze_n (f : ℕ × ℕ → ℚ) (n : ℕ) extends frieze_n f n where
  integral : ∀ m, ∀ i, (f (i,m)).den = 1

-- If a frieze is arithmetic, there exists a unique map f : ℕ × ℕ → ℤ such that the two are equal
-- We need to define friezes over arbitrary fields first...
-- lemma diagTestCriteria (f : ℕ×ℕ → ℚ) (n : ℕ) [arithFrieze_n f n] (i : ℕ) (h: i ≤ n) : ∀m, f (i+1,m) ∣ (f (i,m) + f)
