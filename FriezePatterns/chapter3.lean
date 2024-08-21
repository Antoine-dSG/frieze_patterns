import FriezePatterns.chapter1
import FriezePatterns.chapter2

class arith_fp (f : ℕ × ℕ → ℚ) (n : ℕ) : Prop where
  topBordZeros : ∀ m, f (0,m) = 0
  topBordOnes : ∀ m, f (1,m) =1
  botBordOnes_n : ∀ m, f (n, m) = 1
  botBordZeros_n : ∀ i, ∀ m,  i ≥ n+1 → (f (i,m) = 0)
  diamond : ∀ i, ∀ m,  i ≤ n-1 → f (i+1,m) * f (i+1,m+1)-1 = f (i+2,m)*f (i,m+1)
  integral: ∀ i, ∀ m, (f (i,m)).den == 1
  positive: ∀ i, ∀ m, 1 ≤ i → i ≤ n → f (i,m) > 0

instance [arith_fp f n] : nzPattern_n ℚ f n := {
  topBordZeros := arith_fp.topBordZeros n,
  topBordOnes := arith_fp.topBordOnes n,
  botBordOnes_n := arith_fp.botBordOnes_n,
  botBordZeros_n := arith_fp.botBordZeros_n,
  diamond := arith_fp.diamond,
  non_zero := λ i m ⟨hi1, hi2⟩ => by linarith [@arith_fp.positive f n _ i m hi1 hi2]
}
theorem friezeToDiag : 2^3 = 8 := by linarith
/-
def cFriezePatSet (n: ℕ) : Inhabited (Set (ℕ × ℕ → ℚ)) := by
  let A : Set (ℕ × ℕ → ℚ) := {arith_fp.f n| arith_fp n}
  exact ⟨A⟩
-/
def arithFriezePatSet (n: ℕ) : Set (ℕ × ℕ → ℚ) :=
  { f | arith_fp f n}

-- The following two definitions turn a flute to a frieze.
def f {n : ℕ} (g : flute n): ℕ × ℕ → ℚ :=
  λ ⟨i, m⟩ =>
    if i = 0 then 0
    else if i ≥ n+1 then 0
    else if m = 0 then g.a (i-1)
    else (f g (i+1,m-1) * f g (i-1, m) + 1) / f g (i,m-1)
    termination_by x => (x.2, x.1)


def fluteToFrieze {n : ℕ} (g : flute n) (h: n ≠ 0): arith_fp (f g) n := by sorry

-- Now we can use the nonemptyness of Flute n to prove the nonemptyness of arithFriezePatSet n.
lemma arithFriezePatSetNonEmpty {n : ℕ} (h : n ≠ 0) : Nonempty (arithFriezePatSet n) := by
  rcases csteFlute n with ⟨a⟩
  exact ⟨f a, fluteToFrieze a h⟩


lemma arithFrPatImageFinite (n : ℕ) (f : ℕ × ℕ → ℚ) [arith_fp f n] : Finite (Set.range f) := by
  exact imageFinite ℚ f n

variable (s : Set (ℕ × ℕ)) -- using this definition apparently we can apply Set.Finite.exists_maximal_wrt', with the tradeoff of more complicated definitions.
lemma unFDefined (n : ℕ) (f : ℕ × ℕ → ℚ) [arith_fp f n] : ∃ a ∈ s, ∀ a' ∈ s, f a ≤ f a' → f a = f a' := by
  refine Set.Finite.exists_maximal_wrt' f s ?h ?hs
  have h : (f '' s).Finite := by sorry
  exact h
  have hs : s.Nonempty := by sorry
  exact hs


  --Set.Finite.exists_maximal_wrt' f V h₂ h₁

-- Step 1: define u_n(f) = max (f (i,m), i ∈ ℕ , m ∈ ℕ )

theorem mainTheorem : 2^3 ≤ 8 := by linarith
