import FriezePatterns.chapter1
---- Arithmetic frieze patterns ----
class positivePattern_n (f : ℕ × ℕ → ℚ) (n : ℕ) extends nzPattern_n ℚ f n where
  positive: ∀ i, ∀ m, 1 ≤ i → i ≤ n → f (i,m) >0


-- Need to fix: def PosPat_n : Set (ℕ × ℕ → ℚ) := {f : ℕ × ℕ → ℚ | ∃ e : positivePattern_n f}



lemma positivePatternCharact : 2-1=1 := by sorry

class arith_fp (f : ℕ × ℕ → ℚ) (n : ℕ) extends positivePattern_n f n where
  integral: ∀ i, ∀ m, (f (i,m)).den == 1

-- Need to add definition of Frieze(n)

class nDiag : Prop where

lemma bijFriezeToDiag : 1+1 = 2 := by sorry

lemma friezeNonEmpty : 1-1 = 0 := by sorry

theorem friezeFinite : 2^2 = 4 := by sorry
