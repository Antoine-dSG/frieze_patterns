import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

class pattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) : Prop where
  botBordOnes_n : ∀ m, f (n+1, m) = 1
  topBordOnes : ∀ m, f (0,m) =1
  diamond : ∀ m, ∀ i, f (i+1,m) * f (i+1,m+1)-1 = f (i+2,m)*f (i,m+1)

class nzPattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) extends pattern_n F f n where
  non_zero : ∀ i, ∀ m, i ≤ n+1 → f (i,m) ≠ 0
  botBordZeroes : ∀ m, f (n+2,m) = 0

-- Continuant property for patterns of finite width
-- This is probably a better formulation:
lemma finiteContinuant (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n+1 → ∀m, f (i+2,m) = f (1,m+i+1)*f (i+1,m) - f (i,m) := by
 intro i
 induction i with
 | zero =>
 intro _ m
 simp
 have h₀ : f (0,m) = 1 ∧ f (0,m+1) = 1 := by exact ⟨pattern_n.topBordOnes n m, pattern_n.topBordOnes n (m + 1)⟩
 rw [h₀.1, ← zero_add 2]
 nth_rw 1 [← zero_add 1]
 nth_rw 3 [← zero_add 1]
 rw[mul_comm, pattern_n.diamond n m 0, h₀.2]
 simp
 | succ k ih =>
 intro h m
 have h₁ : f (k+2,m+1) = f (1, m +1 + k + 1) * f (k + 1, m+1) - f (k, m+1) := by
  rw [ih]
  linarith
 have h₂ : f (k + 1, m+1) ≠ 0 := by exact nzPattern_n.non_zero (k + 1) (m + 1) h
 calc f (k + 1 + 2, m) = f (k + 1 + 2, m) * f (k + 1, m+1) * (f (k + 1, m+1))⁻¹ := by rw [mul_inv_cancel_right₀ h₂ (f (k + 1 + 2, m))]
  _= (f (k+2,m)*f (k+2,m+1) - 1) * (f (k + 1, m+1))⁻¹ := by rw [pattern_n.diamond n m (k+1)]
  _= (f (k+2,m)*(f (1, m +1 + k + 1) * f (k + 1, m+1) - f (k, m+1)) - 1) * (f (k + 1, m+1))⁻¹ := by rw [h₁]
  _= (f (1, m +1 + k + 1)*f (k+2,m)* f (k + 1, m+1) - f (k+2,m)*f (k, m+1) - 1) * (f (k + 1, m+1))⁻¹ := by ring
  _= (f (1, m +1 + k + 1)*f (k+2,m)* f (k + 1, m+1) - (f (k+1,m)*f (k+1,m+1) - 1) - 1) * (f (k + 1, m+1))⁻¹ := by rw [pattern_n.diamond n m]
  _= f (1, m +1 + k + 1)*f (k+2,m)*f (k + 1, m+1)* (f (k + 1, m+1))⁻¹ - f (k+1,m)*f (k + 1, m+1)* (f (k + 1, m+1))⁻¹ := by ring
  _= f (1, m +1 + k + 1)*f (k+2,m) - f (k+1,m) := by rw [mul_inv_cancel_right₀ h₂ (f (1, m +1 + k + 1)*f (k+2,m)), mul_inv_cancel_right₀ h₂ (f (k+1,m))]
  _= f (1, m + (k + 1) + 1) * f (k + 1 + 1, m) - f (k + 1, m) := by ring_nf



-- This is a finiteContinuant lemma "in the other direction"
lemma reverseFiniteContinuant (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀i, i≤n+1→∀m, f (i,m+2) = f (n,m+2)*f (i+1,m+1)-f (i+2,m) := by
  sorry
  -- The induction should be from n downwards

lemma glide1 (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀m, f (1,m) = f (n, m+2) := by sorry
 -- This is not so easy, to be done soon. Then place back into the proof of glide symmetry

lemma sillyℕ (n i : ℕ) (h : i ≤ n+1) : n + (1-1)-i = n - (i+1)+1 := by sorry
--
lemma glideSymm (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, (i ≤ n+1) → ∀m, f (i,m) = f (n+1-i, m+i+1) := by
  apply Nat.twoStepInduction
  ·intro h
   simp
   intro m
   have h₁ : f (0,m) = 1 := by exact pattern_n.topBordOnes n m
   have h₂ : f (n+1,m+1) = 1 := by exact pattern_n.botBordOnes_n (m+1)
   rw [h₁,h₂]
  ·intro h m
   simp
   rw [add_assoc]
   simp
   exact glide1 F f n m
  ·intro i Pi Pii
   simp at Pi
   simp at Pii
   simp
   intro h
   have h' : i ≤ n+1 := by linarith
   have h'' : n - (i+1) ≤ n+1 := by
    have h₄ : n - (i+1) ≤ n := by simp
    linarith
   have hi : ∀ (m : ℕ), f (i, m) = f (n + 1 - i, m + i + 1) := by
    apply Pi
    linarith
   have hii : ∀ (m : ℕ), f (i + 1, m) = f (n - i, m + (i + 1) + 1) := by
    apply Pii
    linarith
   intro m
   calc f (i + 1 + 1, m) = f (i+2,m) := by simp
   _= f (1,m+i+1)*f (i+1,m) - f (i,m) := by exact finiteContinuant F f n i h' m
   _= f (1,m+i+1)*f (i+1,m) - f (n + 1 - i, m + i + 1) := by rw [hi m]
   _= f (1,m+i+1)* f (n - i, m + (i + 1) + 1) - f (n + 1 - i, m + i + 1) := by rw [hii m]
   _= f (n, m+i+1+2)* f (n - i, m + (i + 1) + 1) - f (n + 1 - i, m + i + 1) := by rw [glide1 F f n (m+i+1)]
   _= f (n,(m+i+1)+2)* f (n - i, (m + i + 1) + 1)-f (n + 1 - i, m + i + 1) := by rw [add_assoc m]
   _= f (n,(m+i+1)+2)*f (n +(1-1)- i, (m + i + 1) + 1) - f (n + 1 - i, m + i + 1) := by ring_nf
   _= f (n,(m+i+1)+2)*f (n - (i+1)+1, (m + i + 1) + 1) - f (n -(i+1)+2, m + i + 1) := by sorry -- This is arithmetic-in-ℕ nonsense
   _= f (n - (i+1), (m+i+1)+2) := by exact Eq.symm (reverseFiniteContinuant F f n (n - (i+1)) h'' (m+i+1))


lemma translateInvar (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n+1 → ∀ m, f (i,m) = f (i,m+n+3) := by
  intro i h m
  have h₁ : n+1-i ≤ n+1 := by simp
  calc f (i,m) = f (n+1-i, m+i+1) := by exact glideSymm F f n i h m
  _= f (n+1-(n+1-i), (m+i+1)+(n+1-i)+1) := by exact glideSymm F f n (n+1-i) h₁ (m+i+1)
  _= f (i,m+n+3) := by sorry -- This is arithmetic-in-ℕ nonsense
