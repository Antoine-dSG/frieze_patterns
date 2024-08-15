import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic


-- NEED TO CHANGE DEFINITIONS FROM WIDTH TO HEIGHT: WIDTH n <=> HEIGHT n+2
----------- SECTION 1 ---------
---- Field-valued patterns ----
class pattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) : Prop where
  topBordZeros : ∀ m, f (0,m) = 0
  topBordOnes : ∀ m, f (1,m) =1
  botBordOnes_n : ∀ m, f (n, m) = 1
  botBordZeros_n : ∀ m, f (n+1,m) = 0
  diamond : ∀ m, ∀ i, f (i+1,m) * f (i+1,m+1)-1 = f (i+2,m)*f (i,m+1)

class nzPattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) extends pattern_n F f n where
  non_zero : ∀ i, ∀ m, 1 ≤ i → i ≤ n → f (i,m) ≠ 0

lemma pattern_nContinuant1 (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n-1 → ∀m, f (i+2,m) = f (2,m+i)*f (i+1,m) - f (i,m) := by
  intro i
  induction i with
  | zero =>
  simp
  intro m
  have h₀ : f (0, m) = 0 := by exact pattern_n.topBordZeros n m
  have h₁ : f (1, m) = 1 := by exact pattern_n.topBordOnes n m
  rw [h₀, h₁]
  simp
  | succ k ih =>
  intro h m
  have h₂ : f (k + 1, m + 1) ≠ 0 := by sorry /- exact nzPattern_n.non_zero (k+1) (m+1) h -/
  have h₃ : f (k + 3, m) * f (k + 1, m + 1) = (f (k + 2, m) * f (2, m + k + 1) - f (k + 1, m)) * f (k + 1, m + 1) :=
    calc f (k + 3, m) * f (k + 1, m + 1) = f (k + (2+1), m) * f (k + 1, m + 1) := by rw [two_add_one_eq_three]
      _= f ((k + 1) + 2, m) * f (k + 1, m + 1) := by rw [Nat.add_comm 1 2, ← Nat.add_assoc]
      _= f (k + 2, m) * f (k + 2, m + 1) - 1 := by rw [pattern_n.diamond n m (k+1)]
      _= f (k + 2, m) * (f (2, m + 1 + k) * f (k + 1, m + 1) - f (k, m + 1)) - 1 := by sorry /- nth_rw 2 [ih] -/
      _= f (k + 2, m) * (f (2, m + k + 1) * f (k + 1, m + 1) - f (k, m + 1)) - 1 := by rw [add_right_comm]
      _= f (k + 2, m) * (f (2, m + k + 1) * f (k + 1, m + 1)) - f (k + 2, m) * f (k, m + 1) - 1 := by rw [mul_sub_left_distrib]
      _= f (k + 2, m) * f (2, m + k + 1) * f (k + 1, m + 1) - (f (k + 2, m) * f (k, m + 1) + 1) := by rw [mul_assoc, sub_sub]
      _= f (k + 2, m) * f (2, m + k + 1) * f (k + 1, m + 1) - (f (k + 1, m) * f (k + 1, m + 1) - 1 + 1) := by rw [pattern_n.diamond n m k]
      _= f (k + 2, m) * f (2, m + k + 1) * f (k + 1, m + 1) - f (k + 1, m) * f (k + 1, m + 1) := by rw [add_comm_sub, sub_self, add_zero]
      _= (f (k + 2, m) * f (2, m + k + 1) - f (k + 1, m)) * f (k + 1, m + 1) := by rw [← sub_mul]
  rw [add_assoc, add_assoc, one_add_one_eq_two]
  nth_rw 2 [add_comm]
  rw [two_add_one_eq_three]
  rw [← add_assoc, mul_comm]
  rw [← mul_inv_cancel_right₀ h₂ (f (k + 3, m))]
  rw [mul_inv_eq_iff_eq_mul₀]
  exact h₃
  exact h₂

/-rw
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
-/

/-
intro i
  induction i with
  | zero =>
  simp
  intro m
  have h₀ : f (0, m) = 0 := by exact pattern_n.topBordZeros n m
  have h₁ : f (1, m) = 1 := by exact pattern_n.topBordOnes n m
  rw [h₀, h₁]
  simp
  | succ k ih =>
  intro i m
  have h₂ : f (i + 3, m) * f (i + 1, m + 1) = f (i + 2, m) * f (2, m + i + 1) * f (i + 1, m + 1) - f (i + 1, m) * f (i + 1, m + 1) :=
    calc f (i + 3, m) * f (i + 1, m + 1)
      _= f ((i+1) + 2, m) * f ((i+1), m + 1) := by ring_nf
      _= f (i + 2, m) * f (i + 2, m + 1) - 1 := by rw [← pattern_n.diamond n m (i+1)]
      _= f (i + 2, m) * (f (i + 2, m + 1)) - 1
-/

lemma pattern_nContinuant2 (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n-1 → ∀m, f (i,m) = f (n-1,m)*f (i+1,m-1) - f (i+2,m-2) := by sorry


theorem trsltInv (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n+1 → ∀m, f (i,m) = f (i,m+n+1) := by
  -- it suffices to prove glide symmetry
  suffices glideSymm : ∀ i, i ≤ n+1 → ∀ m, f (n+1-i, m+i) = f (i,m)
  · intros i ileq m
    have key := glideSymm i ileq m
    have key2 := glideSymm (n+1-i) (Nat.sub_le (n+1) i) (m+i)
    simp [Nat.sub_sub_eq_min, ileq, add_assoc] at key2
    rw [←key, ←key2, add_assoc]

  -- proof of glide symmetry
  · intros i ileq
    induction' i using Nat.strong_induction_on with i ih -- strong induction on i
    match i with
    | 0 => -- P₀
      simp
      intro m
      rw [@pattern_n.botBordZeros_n F _ f n _ (n+1) m (by linarith), @pattern_n.topBordZeros F _ f n _ m]
    | 1 => -- P₁
      simp at *
      intro m
      rw [@pattern_n.botBordOnes_n F _ f n _ (m+1), @pattern_n.topBordOnes F _ f n _ m]
    | i+2 =>
      simp at *
      intro m
      rw [Nat.sub_add_eq, ← add_assoc m i 2]
      have h₁ : i ≤ n-1 := by
        match n with
        | 0 => linarith
        | n+1 => linarith [Nat.add_sub_cancel n 1]
      have h₂ : f (2,m+i) = f (n-1,m+i+2) := by -- we first prove P₂
        have key := pattern_nContinuant2 F f n 0 (by linarith) (m+i+2)
        simp at key
        rw [@pattern_n.topBordZeros F _ f n _ (m+i+2), @pattern_n.topBordOnes F _ f n _ (m+i+1)] at key
        simp at key
        exact (sub_eq_zero.mp key.symm).symm
      have h₃ : f (i+1,m) = f (n-i,m+i+1) := by
        have := ih (i+1) (by linarith) (by linarith)
        simp at this
        rw [← this, add_assoc]
      have h₄ : f (i,m) = f (n+1-i,m+i) := by
        have := ih i (by linarith) (by linarith)
        simp at this
        rw [← this]
      have h₅ : f (n-i-1,m+i+2) = f (n-1,m+i+2) * f (n-i,m+i+1) - f (n+1-i,m+i) := by
        have key := pattern_nContinuant2 F f n (n-i-1) (by rw [Nat.sub_sub, add_comm i 1, ← Nat.sub_sub]; exact Nat.sub_le (n-1) i) (m+i+2)
        rw [key, Nat.sub_sub n i 1, ← Nat.sub_add_comm ileq, ← Nat.sub_add_comm ileq]
        simp
      symm
      calc
        f (i+2,m) = f (2,m+i) * f (i+1,m) - f (i,m) := by rw [pattern_nContinuant1 F f n i h₁ m]
                _ = f (n-1,m+i+2) * f (n-i,m+i+1) - f (n+1-i,m+i) := by rw [h₂, h₃, h₄]
                _ = f (n-i-1,m+i+2) := by rw [h₅]

lemma imageFinite (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : (Set.range f).Finite := by sorry

lemma testEqualPattern (F : Type*) [Field F] (f g : ℕ×ℕ → F) (n: ℕ) (hf : nzPattern_n F f n) (hg : nzPattern_n F g n) (h : ∀ i, i ≤ n → f (i,0) = g (i,0)) : f = g := sorry
/- Antoine: I have put the proof in comments for the moment to avoids bugs during compilation on GitHub pages
  funext ⟨i, m⟩

  induction m with
  | zero =>
    by_cases ileqn : i ≤ n
    exact h i ileqn
    have this := hf.botBordZeros_n i 0 (by linarith)


-- This is surely in mathlib, in some form
def isFiniteSet (g : ℕ×ℕ → F) : Prop :=
  ∃ (s : Finset F), ∀ i, ∀m, g (i,m) ∈ s

lemma imageFinite (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : isFiniteSet f := by sorry

lemma testEqualPattern (F : Type*) [Field F] (f g : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] [nzPattern_n F g n] (h : ∀ i, i ≤ n → f (i,0) = g (i,0)) : f = g := by sorry




------------- SECTION 2 ------------
---- Arithmetic frieze patterns ----
class positivePattern_n (f : ℕ × ℕ → ℚ) (n : ℕ) extends nzPattern_n ℚ f n where
  positive: ∀ i, ∀ m, i ≤ n+1 → f (i,m) >0


-- Need to add a definition of PosPat(n), the set of positive patterns

lemma positivePatternCharact : 2-1=1 := by sorry

class arith_fp (f : ℕ × ℕ → ℚ) (n : ℕ) extends positivePattern_n f n where
  integral: ∀ i, ∀ m, (f (i,m)).den == 1

-- Need to add definition of Frieze(n)

class nDiag : Prop where

lemma bijFriezeToDiag : 1+1 = 2 := by sorry

lemma friezeNonEmpty : 1-1 = 0 := by sorry

theorem friezeFinite : 2^2 = 4 := by sorry
