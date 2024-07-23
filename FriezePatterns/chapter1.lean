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

class pattern (f : ℕ × ℕ → ℚ) : Prop where
  bordZeros: ∀m, f (0,m) = 0
  bordOnes : ∀ m, f (1,m) =1
  diamond : ∀ m, ∀ i,  f (i+1,m) * f (i+1,m+1) -1= f (i+2,m)*f (i,m+1)

class inftyFrieze (f : ℕ × ℕ → ℚ) extends pattern f where
  positive : ∀ m, ∀ i, f (i+1,m) > 0
  non_zero : ∀ m, ∀ i, f (i+1,m) ≠ 0 -- Obviously follows from inftyFrieze.positive, but CfF

lemma scaledContinuant (f : ℕ×ℕ → ℚ) [inftyFrieze f] (i : ℕ) : ∀m, f (i+2,m) * f (i,m+1) = (f (2,m+i)*f (i+1,m) - f (i,m))* f (i,m+1) := by
  induction i with
  | zero =>
  intro m
  have h₀ : f (0,m) = 0 := by exact pattern.bordZeros m
  have h₁ : f (1,m) = 1 := by exact pattern.bordOnes m
  rw [h₀,h₁]
  simp
  | succ n ih =>
  intro m
  have h₂ : f (n+2,m+1) * f (n,m+1+1) = (f (2,m+1+n)*f (n+1,m+1) - f (n,m+1)) * f (n,m+2) := by exact ih (m + 1)
  have h₃ : f (n,m+2) ≠ 0 := by sorry -- This "should" just be proved by exact inftyFrieze.non_zero, but there is a problem with f (n,m) = f (n-1+1,m)..
  calc f (n + 1 + 2, m) * f (n + 1, m + 1) = f (n+3,m)* f (n+1, m+1) := by simp
  _= f (n+2, m) * f (n+2,m+1) - 1 := by exact Eq.symm (pattern.diamond m (n + 1))
  _= f (n+2, m) * (f (n+2,m+1) * f (n,m+1+1) * (f (n,m+2))⁻¹) -1 := by sorry -- we need to prove that a = f (n,m+1+1) has an inverse
  _= f (n+2, m) * ((f (n+2,m+1) * f (n,m+1+1)) * (f (n,m+2))⁻¹) -1 := by rw [mul_assoc]
  _= f (n+2, m) * ((f (2,m+1+n)*f (n+1,m+1) - f (n,m+1)) * f (n,m+2) * (f (n,m+2))⁻¹) -1 := by rw [h₂]
  _= f (n+2, m) * (f (2,m+1+n)*f (n+1,m+1) - f (n,m+1)) * f (n,m+2) * (f (n,m+2))⁻¹ -1 := by ring
  _= f (n+2, m) * ((f (2,m+1+n)*f (n+1,m+1) - f (n,m+1))) -1 := by sorry -- we need to prove that a * a⁻¹ = 1
  _= f (n+2, m) * f (2,m+1+n)*f (n+1,m+1) - f (n+2, m) *f (n,m+1) -1 := by ring
  _= f (n+2, m) * f (2,m+1+n)*f (n+1,m+1) - ( f (n+1, m)*f (n+1,m+1) -1 ) -1 := by rw [Eq.symm (pattern.diamond m n)]
  _= (f (n+2, m) * f (2,m+1+n) - f (n+1, m))*f (n+1,m+1) := by ring
  _= (f (2,m+1+n)*f (n+2, m) - f (n+1, m))*f (n+1,m+1) := by rw [mul_comm (f (n+2, m))]
  _= (f (2,m+1+n)*f (n+1+1, m) - f (n+1, m))*f (n+1,m+1) := by ring
  _= (f (2, m + (n+1)) * f (n + 1 + 1, m) - f (n + 1, m)) * f (n + 1, m + 1) := by rw [add_assoc m 1 n, add_comm 1 n]




class closedPattern  (f : ℕ × ℕ → ℚ) (n : ℕ) : Prop where
  bordZeros: ∀m, f (0,m) = 0
  bordOnes : ∀ m, f (1,m) =1
  diamond : ∀ m, ∀ i,  f (i+1,m) * f (i+1,m+1) =1 + f (i+2,m)*f (i,m+1)
  width_n: ∀m, f (n+2,m) = 1
-- Careful that the n here is NOT the width; it is the width - 2. I believe this definition is more convenient for formalisation

def set_1_to_n (n : Nat) : Set Nat :=
  { i | 1 ≤ i ∧ i ≤ n }

-- The class below looks a bit dubious to me
class closedFrieze (f : ℕ × ℕ → ℚ) (n : ℕ) extends closedPattern f n where
  positive_n : ∀m, ∀ i ∈ (set_1_to_n n), f (i,m) > 0
