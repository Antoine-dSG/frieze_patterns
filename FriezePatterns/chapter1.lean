import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

---- Field-valued patterns ----
class pattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) : Prop where
  topBordZeros : ∀ m, f (0,m) = 0
  topBordOnes : ∀ m, f (1,m) =1
  botBordOnes_n : ∀ m, f (n, m) = 1
  botBordZeros_n : ∀ i, ∀ m,  i ≥ n+1 → (f (i,m) = 0)
  diamond : ∀ i, ∀ m,  i ≤ n-1 → f (i+1,m) * f (i+1,m+1)-1 = f (i+2,m)*f (i,m+1)

class nzPattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) extends pattern_n F f n where
  non_zero : ∀ i, ∀ m, 1 ≤ i ∧ i ≤ n → f (i,m) ≠ 0


lemma pattern_nContinuant1 (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n-1 → ∀m, f (i+2,m) = f (2,m+i)*f (i+1,m) - f (i,m) := by
  intro i
  induction i with
  | zero =>
  simp
  intro m
  have h₀ : f (0, m) = 0 := pattern_n.topBordZeros n m
  have h₁ : f (1, m) = 1 := pattern_n.topBordOnes n m
  rw [h₀, h₁]
  simp
  | succ k ih =>
  intro h m
  have h' : 1 ≤ k+1 ∧ k+1 ≤ n := by omega
  have hh' : k ≤ n-1 := by omega
  have ih₁ : f (k + 2, m + 1) = f (2, m + 1 + k) * f (k + 1, m + 1) - f (k, m + 1) := ih hh' (m+1)
  have h₂ : f (k + 1, m + 1) ≠ 0 := nzPattern_n.non_zero (k+1) (m+1) h'
  have h₃ : f (k + 3, m) * f (k + 1, m + 1) = (f (k + 2, m) * f (2, m + k + 1) - f (k + 1, m)) * f (k + 1, m + 1) :=
    calc f (k + 3, m) * f (k + 1, m + 1) = f (k + (2+1), m) * f (k + 1, m + 1) := by rw [two_add_one_eq_three]
      _= f ((k + 1) + 2, m) * f (k + 1, m + 1) := by congr
      _= f ((k + 1)+1, m) * f ((k + 1)+1, m + 1) - 1 := by rw [← pattern_n.diamond (k+1) m h]
      _= f ((k + 1)+1, m) * f (k + 2, m + 1) - 1 := by simp
      _= f (k + 2, m) * (f (2, m + 1 + k) * f (k + 1, m + 1) - f (k, m + 1)) - 1 := by rw [ih₁]
      _= f (k + 2, m) * (f (2, m + k + 1) * f (k + 1, m + 1) - f (k, m + 1)) - 1 := by rw [add_right_comm]
      _= f (k + 2, m) * (f (2, m + k + 1) * f (k + 1, m + 1)) - f (k + 2, m) * f (k, m + 1) - 1 := by rw [mul_sub_left_distrib]
      _= f (k + 2, m) * f (2, m + k + 1) * f (k + 1, m + 1) - (f (k + 2, m) * f (k, m + 1) + 1) := by rw [mul_assoc, sub_sub]
      _= f (k + 2, m) * f (2, m + k + 1) * f (k + 1, m + 1) - (f (k + 1, m) * f (k + 1, m + 1) - 1 + 1) := by rw [← pattern_n.diamond k m hh']
      _= f (k + 2, m) * f (2, m + k + 1) * f (k + 1, m + 1) - f (k + 1, m) * f (k + 1, m + 1) := by rw [add_comm_sub, sub_self, add_zero]
      _= (f (k + 2, m) * f (2, m + k + 1) - f (k + 1, m)) * f (k + 1, m + 1) := by rw [← sub_mul]
  simp_arith
  rw [← mul_inv_cancel_right₀ h₂ (f (k + 3, m))]
  rw [mul_inv_eq_iff_eq_mul₀, mul_comm (f (2,m+(k+1)))]
  exact h₃
  exact h₂

-- The second continuant lemma is proved like the first
lemma pattern_nContinuant2 (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n-1 → ∀m, f (i,m+2) = f (n-1,m+2)*f (i+1,m+1) - f (i+2,m) := by
by_cases one_leq_n : 1 ≤ n
suffices pattern_nContinuant2flipped : ∀ i, i ≤ n-1 → ∀m, f (n-i-1,m+2) = f (n-1,m+2)*f (n-i,m+1) - f (n-i+1,m)
-- Flip i to n-i so we can induct forwards
·intro i h m
 have key : n - i - 1 ≤ n - 1 := by omega
 have i_plus_one_leq_n : i + 1 ≤ n := by omega
 have key2 : n - (n - i - 1) - 1 = i := by omega
 have key3 : n - (n - i - 1) = i + 1 := by omega

 calc f (i, m + 2) = f (n - (n - i - 1) - 1, m + 2) := by rw[key2]
          _= f (n-1,m+2)*f (n-(n - i - 1),m+1) - f (n-(n - i - 1) + 1,m) := by rw[pattern_nContinuant2flipped (n - i - 1) key]
          _= f (n-1,m+2)*f (i+1,m+1) - f (i+2,m) := by rw[key3]

-- Have proved sufficiency of the flipped version

·intro i h
 induction i with
 | zero =>
 intro m
 simp
 have hₙ : f (n,m+1) = 1 ∧ f (n+1,m) = 0 := by exact ⟨pattern_n.botBordOnes_n (m+1), pattern_n.botBordZeros_n (n+1) m (by linarith)⟩
 rw[hₙ.2,hₙ.1,sub_zero,mul_one]
 | succ k ih =>
 intro m

 have a₀₁ : 1 ≤ n - k - 1 := by omega
 have a₀₁' : 2 ≤ n - k := by omega
 have a₁ : n - (k + 1) - 1 + 2 = n - k := by omega
 have a₂ : n - (k + 1) - 1 + 1 = n - k - 1 := by omega
 have a₃ : 1 ≤ n - (k + 1) - 1 + 2 ∧ n - (k + 1) - 1 + 2 ≤ n := by omega
 have a₅ : k ≤ n-1 := by omega
 have a₇ : n - (k + 1) - 1 ≤ n - 1 := by omega
 have a₁₁ : n - (k + 1) - 1 + 1 = n - (k + 1) := Nat.sub_add_cancel (a₀₁)
 have a₁₂ : n - (k + 1) - 1 + 2 = n - (k + 1) + 1 := by omega
 have a₉ : n - (k + 1) - 1 + 1 + 2 = n - k + 1 := by omega
 have a₁₀ : n - (k + 1) - 1 + 1 ≤ n - 1 := by omega

 have h₂ : f (n - (k + 1) - 1 + 2, m + 1) ≠ 0 := by exact nzPattern_n.non_zero (n - (k + 1) - 1 + 2) (m + 1) a₃

 calc f (n - (k + 1) - 1, m + 2) =  f (n - (k + 1) - 1, m+2) * f (n - (k + 1) - 1 + 2, m + 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ := by rw [mul_inv_cancel_right₀ h₂ (f (n - (k + 1) - 1, m+2))]
          _= f (n - (k + 1) - 1 + 2, m + 1) * f (n - (k + 1) - 1, (m + 1) + 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ := by ring
          _= ( f (n - (k + 1) - 1 + 1, m + 1) * f (n - (k + 1) - 1 + 1, (m + 1) + 1) - 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ := by rw[pattern_n.diamond (n - (k + 1) - 1) (m+1) a₇]
          _= ( f (n - (k + 1) - 1 + 1, m + 1) * f (n - (k + 1) - 1 + 1, m + 2) - 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ := by simp
          _= ( f (n - (k + 1) - 1 + 1, m + 1) * f (n - k - 1, m + 2) - 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ := by rw[a₂]
          _= ( f (n - (k + 1) - 1 + 1, m + 1) * (f (n - 1, m + 2) * f (n - k, m + 1) - f (n - k + 1, m)) - 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ := by rw[← ih a₅]
          _= (f (n - 1, m + 2) * f (n - (k + 1) - 1 + 1, m + 1) * f (n - k, m + 1) - f (n - k + 1, m) * f (n - (k + 1) - 1 + 1, m + 1) - 1) * (f (n - (k + 1) - 1 + 2 , m + 1))⁻¹ := by ring
          _= (f (n - 1, m + 2) * f (n - (k + 1) - 1 + 1, m + 1) * f (n - k, m + 1) - f (n - (k + 1) - 1 + 1 + 2, m) * f (n - (k + 1) - 1 + 1, m + 1) - 1) * (f (n - (k + 1) - 1 + 2 , m + 1))⁻¹ := by rw[a₉]
          _= (f (n - 1, m + 2) * f (n - (k + 1) - 1 + 1, m + 1) * f (n - k, m + 1) - (f (n - (k + 1) - 1 + 1+1,m) * f (n - (k + 1) - 1 + 1 + 1, m + 1) - 1) - 1) * (f (n - (k + 1) - 1 + 2 , m + 1))⁻¹ := by rw[pattern_n.diamond (n - (k + 1) - 1 + 1) (m) a₁₀]
          _= f (n - 1, m + 2) * f (n - (k + 1) - 1 + 1, m + 1) * f (n - k, m + 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ - f (n - (k + 1) - 1 + 2,m) * f (n - (k + 1) - 1 + 2 , m + 1) * (f (n - (k + 1) - 1 + 2 , m + 1))⁻¹  := by ring
          _= f (n - 1, m + 2) * f (n - (k + 1), m + 1) * f (n - (k + 1) - 1 + 2, m + 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ - f (n - (k + 1) - 1 + 2, m) * f (n - (k + 1) - 1 + 2 , m + 1) * (f (n - (k + 1) - 1 + 2 , m + 1))⁻¹  := by rw[a₁₁, a₁]
          _= f (n - 1, m + 2) * f (n - (k + 1), m + 1) - f (n - (k + 1) - 1 + 2, m) := by rw[mul_inv_cancel_right₀ h₂ (f (n - 1, m + 2) * f (n - (k + 1), m + 1)), mul_inv_cancel_right₀ h₂ (f (n - (k + 1) - 1 + 2, m))]
          _= f (n - 1, m + 2) * f (n - (k + 1), m + 1) - f (n - (k + 1) + 1, m) := by rw[a₁₂]
--Have proved it in the case 1 ≤ n

have n_eq_zero : n = 0 := by linarith
intro i h m
have i_leq_zero : i ≤ 0 := by omega
have i_eq_zero : i = 0 := by linarith

rw[i_eq_zero, n_eq_zero]
simp
rw[@pattern_n.topBordZeros F _ f n _ (m+2), @pattern_n.botBordZeros_n F _ f n _ (2) m (by linarith),zero_mul, sub_zero]

theorem glideSymm (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n+1 → ∀ m, f (n+1-i, m+i) = f (i,m) := by
-- we need glideSymm in chapter 3
  intro i ileq
  induction' i using Nat.twoStepInduction with i ih₁ ih₂
  simp
  intro m
  rw [@pattern_n.botBordZeros_n F _ f n _ (n+1) m (by linarith), @pattern_n.topBordZeros F _ f n _ m]
  simp at *
  intro m
  rw [@pattern_n.botBordOnes_n F _ f n _ (m+1), @pattern_n.topBordOnes F _ f n _ m]
  simp at *
  intro m
  rw [Nat.sub_add_eq, ← add_assoc m i 2]
  have h₁ : i ≤ n-1 := by omega
  have h₂ : f (2,m+i) = f (n-1,m+i+2) := by -- we first prove P₂
    have key := pattern_nContinuant2 F f n 0 (by linarith) (m+i)
    simp [@pattern_n.topBordZeros F _ f n _ (m+i+2), @pattern_n.topBordOnes F _ f n _ (m+i+1)] at key
    exact (sub_eq_zero.mp key.symm).symm
  have h₃ : f (i+1,m) = f (n-i,m+i+1) := by
    have := ih₂ (by linarith) m
    simpa [add_assoc] using this.symm
  have h₄ : f (i,m) = f (n+1-i,m+i) := by
    have := ih₁ (by linarith) m
    simpa using this.symm
  have h₅ : f (n-i-1,m+i+2) = f (n-1,m+i+2) * f (n-i,m+i+1) - f (n+1-i,m+i) := by
    have key := pattern_nContinuant2 F f n (n-i-1) (by omega) (m+i)
    rw [key]
    congr <;> omega
  symm
  calc
    f (i+2,m) = f (2,m+i) * f (i+1,m) - f (i,m) := by rw [pattern_nContinuant1 F f n i h₁ m]
              _ = f (n-1,m+i+2) * f (n-i,m+i+1) - f (n+1-i,m+i) := by congr
              _ = f (n-i-1,m+i+2) := by rw [h₅]

theorem translationInvariance (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n+1 → ∀m, f (i,m) = f (i,m+n+1) := by
  intro i ileq m
  have key := glideSymm F f n i ileq m
  have key2 := glideSymm F f n (n+1-i) (Nat.sub_le (n+1) i) (m+i)
  simp [Nat.sub_sub_eq_min, ileq, add_assoc] at key2
  rw [←key, ←key2, add_assoc]


-- A stronger version of the translation invariance - may be useful
lemma strongTranslationInvariance (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n+1 → ∀m, f (i,m) = f (i,m%(n+1)) := by
  intro i ileq m
  induction' m using Nat.strong_induction_on with m ih
  by_cases hm : m < n+1
  rw [Nat.mod_eq_of_lt hm]
  simp at hm
  have h₁ : m ≥ (n+1) := by omega
  have h₂ : m - (n+1) < m := by omega
  have key : f (i, m - (n + 1)) = f (i, m) := by
    calc f (i,m - (n+1)) = f (i, m - (n+1) + (n+1)) := translationInvariance F f n i (by linarith) (m - (n + 1))
    _= f (i,m) := by congr ; omega
  rw [← key]
  specialize ih (m - (n+1)) h₂
  have h₃ : m % (n + 1) = (m - (n + 1)) % (n + 1) := by apply Nat.mod_eq_sub_mod h₁
  rw [h₃, ih]

lemma imageFinite (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : Finite (Set.range f) := by
-- We use i ≤ n instead of 1 ≤ i ≤ n to simplify the induction. Lean also automatically infers that {i : ℕ | i ≤ n} is finite.
  have key : Set.range f = f '' ({i : ℕ | i ≤ n} ×ˢ {m : ℕ | m ≤ n}) := by
    apply Set.ext_iff.mpr
    -- the hard part: L.H.S. is a subset of R.H.S.
    intro x ; apply Iff.intro
    intro hx ; unfold Set.range at hx
    rcases hx with ⟨⟨i, m⟩, hx⟩
    by_cases hi : i ≤ n
    · induction' m using Nat.strong_induction_on with m ih
      by_cases hm : m ≤ n
      · exact ⟨⟨i, m⟩, ⟨⟨hi, hm⟩, hx⟩⟩ -- we can just use (i,m) if m ≤ n
      · simp at hm
        specialize ih (m-(n+1)) (by omega)
        have key := translationInvariance F f n i (by linarith) (m - (n + 1))
        have : m - (n+1) + n + 1 = m := by omega
        simp [this, hx] at key
        exact ih key
    · use ⟨0, 0⟩ ; apply And.intro (by simp) -- if i > n, then f(i,n) = 0, so we can use (0,0)
      rw [@pattern_n.topBordZeros F _ f n _ 0, ← hx, @pattern_n.botBordZeros_n F _ f n _ i m (by linarith)]
    -- now the trivial part
    exact λ ⟨y, hy⟩ => ⟨y, hy.2⟩
  rw [key]
  have : Finite ({i : ℕ | i ≤ n} ×ˢ {m : ℕ | m ≤ n}) := Finite.Set.finite_prod _ _
  exact Finite.Set.finite_image ({i : ℕ | i ≤ n} ×ˢ {m : ℕ | m ≤ n}) f

