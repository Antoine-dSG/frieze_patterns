import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

-- Chapter 1: Background on frieze patterns
-- Section 1: Field-valued patterns
-- Infinite field-valued patterns

class pattern (F : Type*) [Field F] (f : ℕ × ℕ → F) : Prop where
  topBordOnes : ∀ m, f (0,m) =1
  diamond : ∀ m, ∀ i,  f (i+1,m) * f (i+1,m+1) -1= f (i+2,m)*f (i,m+1)

-- In the following class, nz stands for nowhere-zero pattern. we have nowhere-zero patterns ⊆ tame pattern ⊆ pattern
class nzPattern (F : Type*) [Field F] (f : ℕ × ℕ → F) extends pattern F f where
  non_zero : ∀ i, ∀ m, f (i,m) ≠ 0

class tamePattern (F : Type*) [Field F] (f : ℕ × ℕ → F) extends nzPattern F f where
  -- tame condition ?

-- The following proposition should be extended to include tame frieze patterns
-- Continuant property of nowhere-zero infinite patterns
lemma inftyContinuant (F : Type*) [Field F] (f : ℕ×ℕ → F) [nzPattern F f] (i : ℕ) : ∀m, f (i+2,m) = f (1,m+i+1)*f (i+1,m) - f (i,m) := by
  induction i with
  | zero =>
  intro m
  simp
  have h₀ : f (0,m) = 1 ∧ f (0,m+1) = 1 := by exact ⟨pattern.topBordOnes m, pattern.topBordOnes (m + 1)⟩
  rw [h₀.1, ← zero_add 2]
  nth_rw 1 [← zero_add 1]
  nth_rw 3 [← zero_add 1]
  rw[mul_comm, pattern.diamond m 0, h₀.2]
  simp
  | succ n ih =>
  intro m
  have h : f (n + 1, m+1) ≠ 0 := by exact nzPattern.non_zero (n + 1) (m+1)
  calc f (n + 1 + 2, m) = f (n + 1 + 2, m) * f (n + 1, m+1) * (f (n + 1, m+1))⁻¹ := by rw [mul_inv_cancel_right₀ h (f (n + 1 + 2, m))]
  _= (f (n+2,m)*f (n+2,m+1) - 1) * (f (n + 1, m+1))⁻¹ := by rw [pattern.diamond m (n+1)]
  _= (f (n+2,m)*(f (1, m +1 + n + 1) * f (n + 1, m+1) - f (n, m+1)) - 1) * (f (n + 1, m+1))⁻¹ := by rw [ih (m+1)]
  _= (f (1, m +1 + n + 1)*f (n+2,m)* f (n + 1, m+1) - f (n+2,m)*f (n, m+1) - 1) * (f (n + 1, m+1))⁻¹ := by ring
  _= (f (1, m +1 + n + 1)*f (n+2,m)* f (n + 1, m+1) - (f (n+1,m)*f (n+1,m+1) - 1) - 1) * (f (n + 1, m+1))⁻¹ := by rw [pattern.diamond]
  _= f (1, m +1 + n + 1)*f (n+2,m)*f (n + 1, m+1)* (f (n + 1, m+1))⁻¹ - f (n+1,m)*f (n + 1, m+1)* (f (n + 1, m+1))⁻¹ := by ring
  _= f (1, m +1 + n + 1)*f (n+2,m) - f (n+1,m) := by rw [mul_inv_cancel_right₀ h (f (1, m +1 + n + 1)*f (n+2,m)), mul_inv_cancel_right₀ h (f (n+1,m))]
  _= f (1, m + (n + 1) + 1) * f (n + 1 + 1, m) - f (n + 1, m) := by ring

-- It is not clear if the following definition is useful
-- Bounded field-valued patterns
class closedPattern (F : Type*) [Field F] (f : ℕ × ℕ → F) extends pattern F f where
  bounded: ∃ (n : ℕ), ∀m, f (n+1,m) = 1

class pattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) : Prop where
  botBordOnes_n : ∀ m, f (n+1, m) = 1
  topBordOnes : ∀ m, f (0,m) =1
  diamond : ∀ m, ∀ i, f (i+1,m) * f (i+1,m+1)-1 = f (i+2,m)*f (i,m+1)

class nzPattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) extends pattern_n F f n where
  non_zero : ∀ i, ∀ m, i ≤ n → f (i,m) ≠ 0
  botBordZeroes : ∀ m, f (n+2,m) = 0

-- Continuant property for patterns of finite width
lemma finiteContinuant (F : Type*) [Field F] (f : ℕ×ℕ → F) (n i: ℕ) [nzPattern_n F f n] (hi: i ≤ n) : ∀m, f (i+2,m) = f (1,m+i+1)*f (i+1,m) - f (i,m) := by
 induction i with
 | zero =>
  intro m
  simp
  have h₀ : f (0,m) = 1 ∧ f (0,m+1) = 1 := by exact ⟨pattern_n.topBordOnes n m, pattern_n.topBordOnes n (m + 1)⟩
  rw [h₀.1, ← zero_add 2]
  nth_rw 1 [← zero_add 1]
  nth_rw 3 [← zero_add 1]
  rw[mul_comm, pattern_n.diamond n m 0, h₀.2]
  simp
 | succ k ih =>
 intro m
 have h₁ : f (k+2,m+1) = f (1, m +1 + k + 1) * f (k + 1, m+1) - f (k, m+1) := by
  rw [ih]
  linarith
 have h₂ : f (k + 1, m+1) ≠ 0 := by exact nzPattern_n.non_zero (k + 1) (m + 1) hi
 calc f (k + 1 + 2, m) = f (k + 1 + 2, m) * f (k + 1, m+1) * (f (k + 1, m+1))⁻¹ := by rw [mul_inv_cancel_right₀ h₂ (f (k + 1 + 2, m))]
  _= (f (k+2,m)*f (k+2,m+1) - 1) * (f (k + 1, m+1))⁻¹ := by rw [pattern_n.diamond n m (k+1)]
  _= (f (k+2,m)*(f (1, m +1 + k + 1) * f (k + 1, m+1) - f (k, m+1)) - 1) * (f (k + 1, m+1))⁻¹ := by rw [h₁]
  _= (f (1, m +1 + k + 1)*f (k+2,m)* f (k + 1, m+1) - f (k+2,m)*f (k, m+1) - 1) * (f (k + 1, m+1))⁻¹ := by ring
  _= (f (1, m +1 + k + 1)*f (k+2,m)* f (k + 1, m+1) - (f (k+1,m)*f (k+1,m+1) - 1) - 1) * (f (k + 1, m+1))⁻¹ := by rw [pattern_n.diamond n m]
  _= f (1, m +1 + k + 1)*f (k+2,m)*f (k + 1, m+1)* (f (k + 1, m+1))⁻¹ - f (k+1,m)*f (k + 1, m+1)* (f (k + 1, m+1))⁻¹ := by ring
  _= f (1, m +1 + k + 1)*f (k+2,m) - f (k+1,m) := by rw [mul_inv_cancel_right₀ h₂ (f (1, m +1 + k + 1)*f (k+2,m)), mul_inv_cancel_right₀ h₂ (f (k+1,m))]
  _= f (1, m + (k + 1) + 1) * f (k + 1 + 1, m) - f (k + 1, m) := by ring


-- This is the first step in proving the glide symmetry
lemma firstRowSymm (F : Type*) [Field F] (f : ℕ×ℕ → F) (n : ℕ) [nzPattern_n F f n] : ∀ m, f (1,m+n+1) = f (n,m) := by
  intro m
  have h₁ : f (n+1,m) = 1 := by exact pattern_n.botBordOnes_n m
  have h₂ : f (n+2,m) = 0 := by exact nzPattern_n.botBordZeroes m
  have h₃ : n ≤ n := by rfl
  calc f (1,m+n+1) =  f (1,m+n+1)*1 - 0 := by simp
  _= f (1,m+n+1)*1 - f (n+2,m) := by rw [h₂]
  _= f (1,m+n+1) * f (n+1,m) - f (n+2,m) := by rw [h₁]
  _= f (1,m+n+1) * f (n+1,m) - (f (1,m+n+1)*f (n+1,m) - f (n,m)) := by rw [finiteContinuant F f n n h₃ m]
  _= f (n,m) := by simp

theorem glideSymm (F : Type*) [Field F] (f : ℕ×ℕ → F) (n i: ℕ) [nzPattern_n F f n] (hi: i ≤ n) : ∀m, f (i,m) = f (n+1-i,m+i+1) := by sorry
