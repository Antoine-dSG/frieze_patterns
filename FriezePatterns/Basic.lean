import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
open Nat

-- Functions with a top border of 0s then 1s
def hasBorderTop (f: ℕ × ℤ → ℤ) :=
  ∀ m, f (0, m) = 0 ∧ f (1, m) = 1

-- Functions with a bottom border of 1s then 0s at the (n+1)th and (n+2)th rows
def hasBorderBot_n (f: ℕ × ℤ → ℤ) (n : ℕ):=
  ∀ m, f (n+1,m) = 1 ∧ f (n+2,m) = 0

-- Functions with a bottom border of 1s then 0s
def hasBorderBot (f: ℕ × ℤ → ℤ) :=
  ∃ n, hasBorderBot_n f n

-- Functions which are translation-invariant
def hasTrnsl_n (f: ℕ × ℤ → ℤ) (n : ℕ) :=
  ∀ i,∀ m, f (i,m) = f (i,m+n)




variable (f: ℕ × ℤ → ℤ)
variable (n : ℕ)
-- Translation-invariance of frieze patterns of width n
theorem trans_invar (hBT : hasBorderTop f) (hBB : hasBorderBot_n f n) : hasTrnsl_n f (n+3) := by sorry
