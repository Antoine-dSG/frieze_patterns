import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
-- open Nat

-- Functions with a top border of 0s then 1s
def hasBorderTop (f: ℕ × ℤ → ℤ) :=
  ∀ m, f (0, m) = 0 ∧ f (1, m) = 1
--
-- Function satisfying the diamond rule
--
def hasDiamond (f: ℕ × ℤ → ℤ) :=
  ∀ i, ∀ m, i ≥ 1 ∧ f (i,m) * f (i,m+1) = 1 + f (i+1,m) * f (i-1, m+1)
--
-- Functions with a bottom border of 1s then 0s at the (n+2)nd and (n+3)rd rows
--
def hasBorderBot_n (f: ℕ × ℤ → ℤ) (n : ℕ):=
  ∀ m, f (n+2,m) = 1 ∧ f (n+3,m) = 0
--
-- Functions with first (n+2) consecutive rows consisting of positive integers
--
def pos_n (f: ℕ × ℤ → ℤ) (n : ℕ):=
  ∀ i, ∀ m, (i ≥ 1) ∧ (n+2 ≥ i) ∧ (f (i,m) >0)
--
-- Definition of a frieze pattern of width n
def frieze_n (f: ℕ × ℤ → ℤ) (n : ℕ):=
  hasBorderTop f ∧ hasDiamond f ∧ hasBorderBot_n f n ∧ pos_n f n
--
-- Functions which are translation-invariant by n
--
def transInva_n (f: ℕ × ℤ → ℤ) (n : ℕ) :=
  ∀ i,∀ m, f (i,m) = f (i,m+n)
--
variable (f: ℕ × ℤ → ℤ)
variable (n : ℕ)
-- Translation-invariance of frieze patterns of width n
theorem hasTransInvar (hF : frieze_n f n) : transInva_n f (n+3) := by sorry


-- import SphereEversion.Notations
-- import SphereEversion.ToMathlib.Equivariant
-- import SphereEversion.ToMathlib.MeasureTheory.ParametricIntervalIntegral

/-!
# Basic definitions and properties of loops
-/


open Set Function FiniteDimensional Int TopologicalSpace

open scoped BigOperators Topology unitInterval

noncomputable section

variable {K X X' Y Z : Type*}

-- variable [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-! ## Definition and periodicity lemmas -/


variable (X)

/-- A loop is a function with domain `ℝ` and is periodic with period 1. -/
structure Loop where
  toFun : ℝ → X
  per' : ∀ t, toFun (t + 1) = toFun t
