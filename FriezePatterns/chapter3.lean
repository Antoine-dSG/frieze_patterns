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



def flute_f (f : ℕ×ℕ → ℚ) (n m: ℕ) [arith_fp f n] (i:ℕ) : ℕ :=        -- alternative definition only good when n ≥ 2, as otherwise i%0 = i for all i
  if i%(n-1)=0 then
    1
  else
    ((f (i%(n-1), m)).num).toNat

/--/
def flute_f' (f : ℕ×ℕ → ℚ) (n m: ℕ) [arith_fp f n] (i:ℕ) : ℕ :=        --definition only good when n ≥ 2, as otherwise i%0 = i for all i
  if i ≥ n then
    flute_f n m (i - (n-1))
  else
    ((f (i, m)).num).toNat
-/



def friezeToFlute1 (f : ℕ×ℕ → ℚ) (n m: ℕ) (hn : 2 ≤ n) [arith_fp f n] : flute n := by
  have pos : ∀ i, flute_f f n m (i) > 0 := by
    intro i

    have zero_lt_n_sub_one : 0 < n - 1 :=
        calc 0 < 1 := by simp
            _≤ 2 - 1 := by simp
            _≤  n - 1 := Nat.sub_le_sub_right hn 1

    by_cases n_sub_one_div_i : i%(n-1) = 0
    unfold flute_f
    simp [n_sub_one_div_i]                      --finish if 1 < (n-1) and i%(n-1) = 0
    unfold flute_f
    simp [n_sub_one_div_i]
    have a₁ : 1 ≤ i%(n-1) := by omega
    have a₂ : i%(n-1) ≤ n :=
        calc i%(n-1) ≤ (n - 1) := Nat.le_of_lt (Nat.mod_lt i zero_lt_n_sub_one)
            _≤ n := by simp

    exact arith_fp.positive (i%(n-1)) m a₁ a₂   --finish if 1 < (n-1) and i%(n-1) ≠ 0

  have hd : flute_f f n m 0 = 1 := by
    simp [flute_f]

  have period : ∀ i, flute_f f n m i = flute_f f n m (i + (n-1)) := by
    intro i

    by_cases n_sub_one_div_i : i%(n-1) = 0
    unfold flute_f
    simp [n_sub_one_div_i]                      --finish if i%(n-1) = 0
    unfold flute_f
    simp [n_sub_one_div_i]                      --finish if i%(n-1) ≠ 0

  have div : ∀ i, flute_f f n m (i + 1) ∣ (flute_f f n m (i) + flute_f f n m (i + 2)) := by sorry

  exact ⟨flute_f f n m, pos, hd, period, div⟩





def arithFriezePatSet (n: ℕ) : Set (ℕ × ℕ → ℚ) :=
  { f | arith_fp f n}

lemma arithFriezePatSetNonEmpty (n : ℕ) : Nonempty (arithFriezePatSet n) := by sorry


theorem mainTheorem : 2^3 ≤ 8 := by linarith
