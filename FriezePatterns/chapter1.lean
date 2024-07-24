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
  bordOnes : ∀ m, f (0,m) =1
  diamond : ∀ m, ∀ i,  f (i+1,m) * f (i+1,m+1) -1= f (i+2,m)*f (i,m+1)

class inftyFrieze (f : ℕ × ℕ → ℚ) extends pattern f where
  positive : ∀ m, ∀ i, f (i,m) > 0

-- An infinite frieze is nowhere zero
lemma friezeNonZero (f : ℕ×ℕ → ℚ) [inftyFrieze f] (i : ℕ) (m : ℕ): f (i,m) ≠ 0 := by
  apply LT.lt.ne'
  exact inftyFrieze.positive m i

lemma scaledContinuant (f : ℕ×ℕ → ℚ) [inftyFrieze f] (i : ℕ) : ∀m, f (i+2,m) * f (i,m+1) = (f (1,m+i+1)*f (i+1,m) - f (i,m))* f (i,m+1) := by
  induction i with
  | zero =>
  intro m
  have h₀ : f (0,m+1) = 1 := by exact pattern.bordOnes (m+1)
  have h₁ : f (0,m) = 1 := by exact pattern.bordOnes m
  rw [h₀,h₁]
  simp
  nth_rw 1 [← zero_add 1]
  nth_rw 3 [← zero_add 1]
  rw [mul_comm, pattern.diamond m 0, h₀]
  simp
  | succ n ih =>
  intro m
  have h₂ : f (n+2,m+1) * f (n,m+1+1) = (f (1,m+1+n+1)*f (n+1,m+1) - f (n,m+1)) * f (n,m+2) := by exact ih (m + 1)
  have h₃ : f (n,m+2) ≠ 0 :=  by exact friezeNonZero f n (m+2)
  have h₄ : f (n+2,m+1) = f (n+2,m+1) * f (n,m+2) * (f (n,m+2))⁻¹ := by rw [mul_inv_cancel_right₀ h₃ (f (n+2,m+1))]
  have h₅ : f (n,m+2) * (f (n,m+2))⁻¹ = 1 := by exact Rat.mul_inv_cancel (f (n, m + 2)) h₃
  calc f (n + 1 + 2, m) * f (n + 1, m + 1) = f (n+3,m)* f (n+1, m+1) := by simp
  _= f (n+2, m) * f (n+2,m+1) - 1 := by exact Eq.symm (pattern.diamond m (n + 1))
  _= f (n+2, m) * (f (n+2,m+1) * f (n,m+2) * (f (n,m+2))⁻¹) -1 := by exact congrFun (congrArg HSub.hSub (congrArg (HMul.hMul (f (n + 2, m))) h₄)) 1  -- we need to prove that a = f (n,m+1+1) has an inverse
  _= f (n+2, m) * ((f (n+2,m+1) * f (n,m+1+1)) * (f (n,m+2))⁻¹) -1 := by rw [mul_assoc]
  _= f (n+2, m) * ((f (1,m+1+n+1)*f (n+1,m+1) - f (n,m+1)) * f (n,m+2) * (f (n,m+2))⁻¹) -1 := by rw [h₂]
  _= f (n+2, m) * (f (1,m+1+n+1)*f (n+1,m+1) - f (n,m+1)) * (f (n,m+2) * (f (n,m+2))⁻¹) -1 := by ring
  _= f (n+2, m) * ((f (1,m+1+n+1)*f (n+1,m+1) - f (n,m+1))) * 1 -1 := by rw [h₅]
  _= f (n+2, m) * f (1,m+(n+1)+1)*f (n+1,m+1) - f (n+2, m) *f (n,m+1) -1 := by ring_nf
  _= f (n+2, m) * f (1,m+(n+1)+1)*f (n+1,m+1) - ( f (n+1, m)*f (n+1,m+1) -1 ) -1 := by rw [Eq.symm (pattern.diamond m n)]
  _= (f (n+2, m) * f (1,m+(n+1)+1) - f (n+1, m))*f (n+1,m+1) := by ring
  _= (f (1,m+(n+1)+1)*f (n+2, m) - f (n+1, m))*f (n+1,m+1) := by rw [mul_comm (f (n+2, m))]
  _= (f (1,m+(n+1)+1)*f (n+1+1, m) - f (n+1, m))*f (n+1,m+1) := by ring


lemma continuant (f : ℕ×ℕ → ℚ) [inftyFrieze f] (i : ℕ) : ∀m, f (i+2,m) = f (1,m+i+1)*f (i+1,m) - f (i,m) := by
  intro m
  have h : f (i+2,m) * f (i,m+1) = (f (1,m+i+1)*f (i+1,m) - f (i,m))* f (i,m+1) := by exact scaledContinuant f i m
  have h₁ : f (i,m+1) ≠ 0 := by exact friezeNonZero f  i (m + 1)
  calc f (i+2,m) = f (i+2,m) * f (i,m+1) * (f (i,m+1))⁻¹ := by rw [mul_inv_cancel_right₀ h₁ (f (i+2,m))]
  _= (f (1,m+i+1)*f (i+1,m) - f (i,m))* f (i,m+1) * (f (i,m+1))⁻¹ := by rw [h]
  _= (f (1,m+i+1)*f (i+1,m) - f (i,m))* (f (i,m+1) * (f (i,m+1))⁻¹) := by ring
  _= (f (1,m+i+1)*f (i+1,m) - f (i,m))*1 := by rw [Rat.mul_inv_cancel (f (i,m+1)) h₁]
  _= f (1,m+i+1)*f (i+1,m) - f (i,m) := by simp






class closedPattern  (f : ℕ × ℕ → ℚ) extends pattern f where
  width_n: ∃ (n : ℕ), ∀m, f (n+1,m) = 1

-- We need to find a way to define width as min over all exist variables


def set_1_to_n (n : Nat) : Set Nat :=
  { i | 1 ≤ i ∧ i ≤ n }

-- The class below looks a bit dubious to me
class closedFrieze (f : ℕ × ℕ → ℚ) (n : ℕ) extends closedPattern f where
  positive_n : ∀m, ∀ i ∈ (set_1_to_n n), f (i,m) > 0
