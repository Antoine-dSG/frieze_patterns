import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

-- Chapter 1: Background on frieze patterns
-- Section 1: Field-valued patterns
-- Infinite field-valued patterns

class pattern (F : Type*) [Field F] (f : ℕ × ℕ → F) : Prop where
  topBordOnes : ∀ m, f (0,m) =1
  diamond : ∀ m, ∀ i,  f (i+1,m) * f (i+1,m+1) -1= f (i+2,m)*f (i,m+1)

-- In the following class, dom stands for domestic. Roughly, domesticated pattern ⊆ tame pattern ⊆ pattern
class domPattern (F : Type*) [Field F] (f : ℕ × ℕ → F) extends pattern F f where
  non_zero : ∀ i, ∀ m, f (i,m) ≠ 0

class tamePattern (F : Type*) [Field F] (f : ℕ × ℕ → F) extends domPattern F f where
  -- tame condition ?

-- lemma scaledContinuant (f : ℕ×ℕ → ℚ) [inftyFrieze f] (i : ℕ) : ∀m, f (i+2,m) * f (i,m+1) = (f (1,m+i+1)*f (i+1,m) - f (i,m))* f (i,m+1) := by
lemma scaledContinuant (F : Type*) [Field F] (f : ℕ×ℕ → F) [domPattern F f] (i : ℕ) : ∀m, f (i+2,m) * f (i,m+1) = (f (1,m+i+1)*f (i+1,m) - f (i,m))* f (i,m+1) := by
  induction i with
  | zero =>
  intro m
  have h₀ : f (0,m+1) = 1 := by exact pattern.topBordOnes (m+1)
  have h₁ : f (0,m) = 1 := by exact pattern.topBordOnes m
  rw [h₀,h₁]
  simp
  nth_rw 1 [← zero_add 1]
  nth_rw 3 [← zero_add 1]
  rw [mul_comm, pattern.diamond m 0, h₀]
  simp
  | succ n ih =>
  intro m
  have h₂ : f (n+2,m+1) * f (n,m+1+1) = (f (1,m+1+n+1)*f (n+1,m+1) - f (n,m+1)) * f (n,m+2) := by exact ih (m + 1)
  -- have h₃ : f (n,m+2) ≠ 0 :=  by exact friezeNonZero f n (m+2)
  have h₃ : f (n,m+2) ≠ 0 :=  by exact domPattern.non_zero n (m + 2)
  have h₄ : f (n+2,m+1) = f (n+2,m+1) * f (n,m+2) * (f (n,m+2))⁻¹ := by rw [mul_inv_cancel_right₀ h₃ (f (n+2,m+1))]
  -- have h₅ : f (n,m+2) * (f (n,m+2))⁻¹ = 1 := by exact Rat.mul_inv_cancel (f (n, m + 2)) h₃
  have h₅ : f (n,m+2) * (f (n,m+2))⁻¹ = 1 := by exact CommGroupWithZero.mul_inv_cancel (f (n, m + 2)) h₃
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


-- lemma continuant (f : ℕ×ℕ → ℚ) [inftyFrieze f] (i : ℕ) : ∀m, f (i+2,m) = f (1,m+i+1)*f (i+1,m) - f (i,m) := by
lemma inftyContinuant (F : Type*) [Field F] (f : ℕ×ℕ → F) [domPattern F f] (i : ℕ) : ∀m, f (i+2,m) = f (1,m+i+1)*f (i+1,m) - f (i,m) := by
  intro m
  have h : f (i+2,m) * f (i,m+1) = (f (1,m+i+1)*f (i+1,m) - f (i,m))* f (i,m+1) := by exact scaledContinuant F f i m
  --have h₁ : f (i,m+1) ≠ 0 := by exact friezeNonZero f  i (m + 1)
  have h₁ : f (i,m+1) ≠ 0 := by exact domPattern.non_zero i (m + 1)
  calc f (i+2,m) = f (i+2,m) * f (i,m+1) * (f (i,m+1))⁻¹ := by rw [mul_inv_cancel_right₀ h₁ (f (i+2,m))]
  _= (f (1,m+i+1)*f (i+1,m) - f (i,m))* f (i,m+1) * (f (i,m+1))⁻¹ := by rw [h]
  _= (f (1,m+i+1)*f (i+1,m) - f (i,m))* (f (i,m+1) * (f (i,m+1))⁻¹) := by ring
  --_= (f (1,m+i+1)*f (i+1,m) - f (i,m))*1 := by rw [Rat.mul_inv_cancel (f (i,m+1)) h₁]
  _= (f (1,m+i+1)*f (i+1,m) - f (i,m))*1 := by rw [CommGroupWithZero.mul_inv_cancel (f (i,m+1)) h₁]
  _= f (1,m+i+1)*f (i+1,m) - f (i,m) := by simp


-- Bounded field-valued patterns
class closedPattern (F : Type*) [Field F] (f : ℕ × ℕ → F) extends pattern F f where
  bounded: ∃ (n : ℕ), ∀m, f (n+1,m) = 1

class pattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) : Prop where
  botBordOnes_n : ∀ m, f (n, m) = 1

class domPattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) extends pattern_n F f n where
  non_zero : ∀ i, ∀ m, i ≤ n ∧ f (i,m) ≠ 0

lemma continuantFrieze (F : Type*) [Field F] (f : ℕ×ℕ → F) (n : ℕ) [domPattern_n F f n] (i : ℕ) (h: i ≤ n) : ∀m, f (i+2,m) = f (1,m+i+1)*f (i+1,m) - f (i,m) := by
 induction i with
 | zero => sorry
 | succ k ih => sorry
