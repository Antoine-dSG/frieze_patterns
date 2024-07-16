import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
open Nat

-- Functions with a top border of 0s then 1s
def hasBorderTop (f: ℕ × ℤ → ℤ) :=
  ∀ m, f (0, m) = 0 ∧ f (1, m) = 1
--
-- Function satisfying the diamond rule
--
def hasDiamond (f: ℕ × ℤ → ℤ) :=
  ∀ i, ∀ m, i ≥ 1 ∧ f (i,m) * f (i,m+1) = 1 + f (i+1,m) * f (i-1, m+1)
--
-- Functions with a bottom border of 1s then 0s at the (n+1)th and (n+2)th rows
--
def hasBorderBot_n (f: ℕ × ℤ → ℤ) (n : ℕ):=
  ∀ m, f (n+1,m) = 1 ∧ f (n+2,m) = 0
--
-- Functions with a bottom border of 1s then 0s
--
def hasBorderBot (f: ℕ × ℤ → ℤ) :=
  ∃ n, hasBorderBot_n f n
--
-- Functions which are translation-invariant by n
--
def transInva_n (f: ℕ × ℤ → ℤ) (n : ℕ) :=
  ∀ i,∀ m, f (i,m) = f (i,m+n)
--
variable (f: ℕ × ℤ → ℤ)
variable (n : ℕ)
-- Translation-invariance of frieze patterns of width n
theorem hasTransInvar (hBT : hasBorderTop f) (hD : hasDiamond f) (hBB : hasBorderBot_n f n) : transInva_n f (n+3) := by sorry
