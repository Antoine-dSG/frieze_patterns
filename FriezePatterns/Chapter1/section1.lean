import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic


-- NEED TO CHANGE DEFINITIONS FROM WIDTH TO HEIGHT: WIDTH n <=> HEIGHT n+2
----------- SECTION 1 ---------
---- Field-valued patterns ----
class pattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) : Prop where
  botBordOnes_n : ∀ m, f (n+1, m) = 1
  topBordOnes : ∀ m, f (0,m) =1
  diamond : ∀ m, ∀ i, f (i+1,m) * f (i+1,m+1)-1 = f (i+2,m)*f (i,m+1)

class nzPattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) extends pattern_n F f n where
  non_zero : ∀ i, ∀ m, i ≤ n+1 → f (i,m) ≠ 0
  botBordZeroes : ∀ m, f (n+2,m) = 0

lemma pattern_nContinuant1 (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n+1 → ∀m, f (i+2,m) = f (1,m+i+1)*f (i+1,m) - f (i,m) := by
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

lemma pattern_nContinuant2 (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n+1 → ∀m, f (n-i,m) = f (n,m)*f (n-i+1,m-1) - f (n-i+2,m-2) := by
 intro i
 induction i with
 | zero =>
 intro _ m
 simp
 have hₙ : f (n+1,m-1) = 1 ∧ f (n+2,m-2) = 0 := by exact ⟨pattern_n.botBordOnes_n (m-1), nzPattern_n.botBordZeroes (m -2)⟩
 rw[hₙ.2,hₙ.1,sub_zero,mul_one]
 | succ k ih =>
 intro h m
 have a₁ : m = m - 1 + 1 := by sorry
 have a₂ : n - k + 1 = n - (k+1) + 2 := by sorry
 --Have a bunch of issues here due to this being defined on ℕ instead of ℤ, ask Antoine if there's a fix
 have a₃ : n-k+1 ≤ n+1 := by sorry
 have a₄ : n-k = n - (k+1)+1 := by sorry
 have a₅ : k ≤ n+1 := by sorry --have k≤k+1≤ n+1, how to apply transitivity to this?
 have a₆ : m-2+1 = m-1 := by sorry


 have h₂ : f (n - k + 1, m - 1) ≠ 0 := by exact nzPattern_n.non_zero (n-k+1) (m - 1) a₃

 calc f (n - (k + 1), m) = f (n - (k + 1), m) * f (n - k + 1, m - 1) * (f (n - k + 1, m - 1))⁻¹ := by rw [mul_inv_cancel_right₀ h₂ (f (n - (k + 1), m))]
  _= f (n - k + 1, m - 1) * f (n - (k + 1), m) * (f (n - k + 1, m - 1))⁻¹ := by rw[mul_comm (f (n - k + 1, m - 1))]
  _= f (n - (k + 1) + 2 , m - 1) * f (n - (k + 1), m-1+1) * (f (n - k + 1, m - 1))⁻¹ := by rw[a₂,← a₁]
  _= (f (n - (k+1)+1,m-1) * f (n - (k+1)+1, m-1+1) - 1) * (f (n - k + 1, m - 1))⁻¹ := by rw[pattern_n.diamond n (m-1) (n-(k+1))]
  _= (f (n - k,m-1) * f (n - k, m) - 1) * (f (n - k + 1, m - 1))⁻¹ := by rw[← a₁, ← a₄]
  _= (f (n - k,m-1) * (f (n, m) * f (n - k + 1, m - 1) - f (n - k + 2, m - 2)) - 1) * (f (n - k + 1, m - 1))⁻¹ := by rw[← ih a₅]
  _= (f (n, m)*f (n - k,m-1)*f (n - k + 1, m - 1) - f (n - k + 2, m - 2)*f (n - k,m-1) - 1) * (f (n - k + 1, m - 1))⁻¹ := by ring
  _= (f (n, m)*f (n - k,m-1)*f (n - k + 1, m - 1) - f (n - k + 2, m - 2)*f (n - k,(m-2)+1) - 1) * (f (n - k + 1, m - 1))⁻¹ := by rw[a₆]
  _= (f (n, m)*f (n - k,m-1)*f (n - k + 1, m - 1) - (f (n-k+1,m-2) * f (n-k+1,m-1)-1) - 1) * (f (n - k + 1, m - 1))⁻¹ := by rw[← a₆,pattern_n.diamond n (m-2) (n-k)]
  _= f (n, m)*f (n - k,m-1)*f (n - k + 1, m - 1)* (f (n - k + 1, m - 1))⁻¹  - f (n-k+1,m-2) * f (n-k+1,m-1)* (f (n - k + 1, m - 1))⁻¹  := by ring
  _= f (n, m)*f (n - k,m-1) - f (n-k+1,m-2) := by rw [mul_inv_cancel_right₀ h₂ (f (n, m)*f (n - k,m-1)), mul_inv_cancel_right₀ h₂ (f (n-k+1,m-2))]


theorem trsltInv : 1+1=2 := by sorry

lemma imageFinite : 2+2 = 4 := by sorry

lemma testEqualPattern (F : Type*) [Field F] (f g : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] [nzPattern_n F g n] (h : ∀ i, i ≤ n → f (i,0) = g (i,0)) : f = g := by
  funext ⟨i, m⟩

  induction m with
  | zero =>


  induction i with
    | zero =>

    apply h

    | succ k ih =>


  | succ k ih =>







------------- SECTION 2 ------------
---- Arithmetic frieze patterns ----
class positivePattern_n (f : ℕ × ℕ → ℚ) (n : ℕ) extends nzPattern_n ℚ f n where
  positive: ∀ i, ∀ m, i ≤ n+1 → f (i,m) >0

lemma positivePatternCharact : 2-1=1 := by sorry

class arith_fp (f : ℕ × ℕ → ℚ) (n : ℕ) extends positivePattern_n f n where
  integral: ∀ i, ∀ m, (f (i,m)).den == 1

lemma testCriteria1 : 1+1 = 2 := by sorry

lemma testCriteria2 : 2*2 = 4 := by sorry

lemma friezeNonEmpty : 1-1 = 0 := by sorry

theorem friezeFinite : 2^2 = 4 := by sorry
