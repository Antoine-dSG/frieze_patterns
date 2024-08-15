import FriezePatterns.chapter1
import FriezePatterns.chapter2

-- How do we define a sequence? Do we use "instances" ?

class arith_fp (f : ℕ × ℕ → ℚ) (n : ℕ) extends nzPattern_n ℚ f n where
  integral: ∀ i, ∀ m, (f (i,m)).den == 1
  positive: ∀ i, ∀ m, 1 ≤ i → i ≤ n → f (i,m) > 0

theorem friezeToDiag : 2^3 = 8 := by linarith

lemma friezeNonEmpty : 2^3 ≥ 8 := by linarith

theorem mainTheorem : 2^3 ≤ 8 := by linarith
