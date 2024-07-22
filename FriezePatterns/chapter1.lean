import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
-- open Nat
-- Second attempt at defining frieze patterns. This time we use the
-- finite sets Fin and we consider rational valued patterns

-- The above attempt has not worked, because inductions on Fin n are a real problem
-- Here is a third attempt at a working definition

-- Acroynms for the comments:
-- CfF: Convenient for Formalisation

class pattern (f : ℕ × ℤ → ℚ) : Prop where
  bordZeros: ∀m, f (0,m) = 0
  bordOnes : ∀ m, f (1,m) =1
  diamond : ∀ m, ∀ i,  f (i+1,m) * f (i+1,m+1) =1 + f (i+2,m)*f (i,m+1)

class inftyFrieze (f : ℕ × ℤ → ℚ) extends pattern f where
  positive : ∀ m, ∀ i, f (i+1,m) > 0
  non_zero : ∀ m, ∀ i, f (i+1,m) ≠ 0 -- Obviously follows from inftyFrieze.positive, but CfF

lemma continuantInftyFrieze (f : ℕ × ℤ → ℚ) [inftyFrieze f] (i : ℕ) : ∀ m, f (i+2,m) = f (2,m+i) * f (i+1, m) - f (i,m) := by
  induction i with
  | zero =>
  simp
  intro m
  have h₀ : f (0,m) = 0 := by exact pattern.bordZeros m
  have h₁ : f (1,m) = 1 := by exact pattern.bordOnes m
  rw [h₀, h₁]
  simp
  | succ n ih =>
    intro m
    have h₂ : f (n + 2, m) = f (2, m + n) * f (n + 1, m) - f (n, m) := by exact ih m
    have h₃ : f (n+2 ,m) * f (n+2, m+1) = 1 + f (n+3 , m) * f (n+1, m+1) := by exact pattern.diamond m (n + 1)
    have h₄ : f (n+2, m+1) = f (2, m + 1 + n) * f (n + 1, m+1) - f (n, m+1) := by exact ih (m+1)
    rw [h₄] at h₃
    simp [h₃]
    rw [sub_eq_add_neg] at h₃
    rw [left_distrib] at h₃
    have h₅ : 1 = f (n+1, m) * f (n+1, m+1) - f (n+2,m) * f (n,m+1) := by sorry
    rw [h₅] at h₃
    rw [mul_neg] at h₃
    rw [sub_eq_add_neg] at h₃
    rw [add_comm (f (n + 1, m) * f (n + 1, m + 1) + -(f (n + 2, m) * f (n, m + 1)))] at h₃
    -- The following hypothesis by sorry is because I gave up with the rewrites
    have h : f (n + 2, m) * (f (2, m + 1 + n) * f (n + 1, m + 1)) - (f (n + 1, m) * f (n + 1, m + 1)) = f (n + 3, m) * f (n + 1, m + 1) := by sorry
    rw [sub_eq_add_neg] at h
    rw [← neg_mul] at h
    rw [← mul_assoc (f (n + 2, m)),← right_distrib] at h
    have hh : f (n+1, m+1) ≠ 0 := by exact inftyFrieze.non_zero (m+1) n
    have hhh : f (n + 2, m) * f (2, m + 1+n ) + -f (n + 1, m) = f (n + 3, m) := by apply mul_right_cancel₀ hh h
    rw [add_assoc, add_comm 1 2, two_add_one_eq_three, add_assoc n 1, one_add_one_eq_two, sub_eq_add_neg, mul_comm]
    sorry
    -- How do we proceed from here ? This is driving me crazy









class closedPattern  (f : ℕ × ℤ → ℚ) (n : ℕ) : Prop where
  bordZeros: ∀m, f (0,m) = 0
  bordOnes : ∀ m, f (1,m) =1
  diamond : ∀ m, ∀ i,  f (i+1,m) * f (i+1,m+1) =1 + f (i+2,m)*f (i,m+1)
  width_n: ∀m, f (n+2,m) = 1
-- Careful that the n here is NOT the width; it is the width - 2. I believe this definition is more convenient for formalisation

def set_1_to_n (n : Nat) : Set Nat :=
  { i | 1 ≤ i ∧ i ≤ n }

-- The class below looks a bit dubious to me
class closedFrieze (f : ℕ × ℤ → ℚ) (n : ℕ) extends closedPattern f n where
  positive_n : ∀m, ∀ i ∈ (set_1_to_n n), f (i,m) > 0



/--  OLD CODE

example (f : Fin (n+2) × ℤ → ℚ) [Frieze n f] (m : ℤ): f (0,m) =1 := by
  apply Frieze.topBorder1s

example (f : Fin (n+2) × ℤ → ℚ) [Frieze n f] (m : ℤ): f (n+1,m) =1 := by
  exact Frieze.bottomBorder1s m

example (f : Fin (n+2) × ℤ → ℚ) [Frieze n f] (m : ℤ): ∀i, f (i,m) > 0 := by
  intro i
  exact Frieze.positiveValues m i

example (n : ℕ)(f : Fin (n+2) × ℤ → ℚ) [Frieze n f] : ∀ m, ∀ i, f (i+1,m) * f (i+1,m+1) = 1 + f (i+2,m) * f (i, m+1) := by
  exact fun m i ↦ Frieze.diamondrule m i


lemma diamond_example (n : ℕ)(f : Fin (n+2) × ℤ → ℚ) [Frieze n f] : ∀ m, f (1,m) * f (1,m+1) = 1 + f (2,m) * f (0, m+1) := by
  intro m
  calc f (1,m) * f (1,m+1) = f (0+1,m) * f (0+1,m+1) := by exact rfl
    _= 1 + f (0+2,m) * f (0, m+1) := by exact Frieze.diamondrule m 0
    _= 1 + f (2,m) * f (0,m+1) := by rw [zero_add]



lemma base_continuant (m : ℤ)  (f : Fin (n+2) × ℤ → ℚ) [Frieze n f] : f (2,m) = f (1,m) * f (1,m+1) -1 := by
  have h1 : f (0, m+1) = 1 := by exact Frieze.topBorder1s (m + 1)
  have h2 : f (2,m) = f (2,m) * f (0, m+1):=  by
    rw [h1]
    exact Eq.symm (Rat.mul_one (f (2, m)))
  have h3 :  f (1,m) * f (1,m+1) = 1 + f (2,m) * f (0, m+1) := by apply diamond_example

  calc f (2,m) = f (2,m) * f (0, m+1) := by exact h2
  _ = f (1,m) * f (1,m+1) -1  := by exact Eq.symm (sub_eq_of_eq_add' h3)





lemma continuant (n : ℕ) (f : Fin (n+2) × ℤ → ℚ) [Frieze n f] : ∀ i, ∀ m, f (i+2,m) = f (i+1,m)* f (1,m+i+1) - f (i,m) := by sorry

-/
