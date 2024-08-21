import FriezePatterns.chapter1
import FriezePatterns.chapter2

class arith_fp (f : ℕ × ℕ → ℚ) (n : ℕ) : Prop where
  topBordZeros : ∀ m, f (0,m) = 0
  topBordOnes : ∀ m, f (1,m) = 1
  botBordOnes_n : ∀ m, f (n, m) = 1
  botBordZeros_n : ∀ i, ∀ m,  i ≥ n+1 → (f (i,m) = 0)
  diamond : ∀ i, ∀ m,  i ≤ n-1 → f (i+1,m) * f (i+1,m+1)-1 = f (i+2,m)*f (i,m+1)
  integral: ∀ i, ∀ m, (f (i,m)).den == 1
  positive: ∀ i, ∀ m, 1 ≤ i → i ≤ n → f (i,m) > 0

--def af (f : ℕ×ℕ → ℚ) (n: ℕ) [arith_fp f n] : ℕ :=

instance [arith_fp f n] : nzPattern_n ℚ f n := {
  topBordZeros := arith_fp.topBordZeros n,
  topBordOnes := arith_fp.topBordOnes n,
  botBordOnes_n := arith_fp.botBordOnes_n,
  botBordZeros_n := arith_fp.botBordZeros_n,
  diamond := arith_fp.diamond,
  non_zero := λ i m ⟨hi1, hi2⟩ => by linarith [@arith_fp.positive f n _ i m hi1 hi2]
}



def flute_f (f : ℕ×ℕ → ℚ) (n m i: ℕ) [arith_fp f n] : ℕ :=
  if i%(n-1)=0 then
    1
  else
    ((f (i%(n-1), m)).num).toNat

def friezeToFlute1 (f : ℕ×ℕ → ℚ) (n: ℕ) [arith_fp f n] : flute m := by
  have pos : ∀ i, flute_f f n m (i) > 0 := by
    intro i

    by_cases zero_lt_n_sub_one : 0 < (n-1)
    by_cases n_sub_one_div_i : i%(n-1) = 0
    unfold flute_f
    simp [n_sub_one_div_i]                      --done if 0 < (n-1) and i%(n-1) = 0
    unfold flute_f
    simp [n_sub_one_div_i]
    have a₁ : 1 ≤ i%(n-1) := by sorry
    have a₂ : i%(n-1) ≤ n := by sorry
    exact arith_fp.positive (i%(n-1)) m a₁ a₂   --done if 0 < (n-1) and i%(n-1) ≠ 0

    have n_sub_one_le_zero : n - 1 ≤ 0 := by linarith
    by_cases n_eq_zero : n = 0
    unfold flute_f
    simp [n_eq_zero]
    sorry
    sorry

  have hd : flute_f f n m 0 = 1 := by
    unfold flute_f
    simp

  have period : ∀ i, flute_f f n m 0 = flute_f f n m (i + (n-1)) := by sorry

  have div : ∀ i, flute_f f n m (i + 1) ∣ (flute_f f n m (i) + flute_f f n m (i + 2)) := by sorry

  exact ⟨a_even k, pos, hd, period, div⟩





def arithFriezePatSet (n: ℕ) : Set (ℕ × ℕ → ℚ) :=
  { f | arith_fp f n}

lemma arithFriezePatSetNonEmpty (n : ℕ) : Nonempty (arithFriezePatSet n) := by sorry


theorem mainTheorem : 2^3 ≤ 8 := by linarith
