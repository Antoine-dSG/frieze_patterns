import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
-- open Nat
-- Second attempt at defining frieze patterns. This time we use the
-- finite sets Fin and we consider rational valued patterns


--def border (n : ℕ) (f : Fin (n+2) × ℤ → ℚ) :=
--  ∀ (m : ℤ), f (0,m) =1

-- def diamond (n : ℕ) (f : Fin (n+2) × ℤ → ℚ) :=
--  ∀ i, ∀ m, 1 ≤ i.1 ∧ i.1 ≤ n ∧ (f (i,m) * f (i,m+1) = 1 + f (i+1,m) * f (i-1, m+1) )


-- def positive (n : ℕ) (f : Fin (n+2) × ℤ → ℚ) :=
--  ∀ m, ∀ i, f (i,m) >0

--def frieze (n : ℕ) (f : Fin (n+2) × ℤ → ℚ) :=
-- border n f ∧ diamond n f ∧ positive n f

variable (n : ℕ)
variable (f : Fin (n+2) × ℤ → ℚ)

class Frieze (n : ℕ) (f : Fin (n+2) × ℤ → ℚ) : Prop where
  diamondrule : ∀ m, ∀ i, f (i+1,m) * f (i+1,m+1) = 1 + f (i+2,m) * f (i, m+1)
  topBorder1s : ∀ (m : ℤ), f (0,m) =1
  bottomBorder1s : ∀ (m : ℤ), f (n+1,m) =1
  positiveValues: ∀ m, ∀ i, f (i,m) >0
  integral: ∀ m, ∀ i, (f (i,m)).den == 1




example (f : Fin (n+2) × ℤ → ℚ) [Frieze n f] (m : ℤ): f (0,m) =1 := by
  apply Frieze.topBorder1s

example (f : Fin (n+2) × ℤ → ℚ) [Frieze n f] (m : ℤ): f (n+1,m) =1 := by
  exact Frieze.bottomBorder1s m

example (f : Fin (n+2) × ℤ → ℚ) [Frieze n f] (m : ℤ): ∀i, f (i,m) > 0 := by
  intro i
  exact Frieze.positiveValues m i

example (n : ℕ)(f : Fin (n+2) × ℤ → ℚ) [Frieze n f] : ∀ m, ∀ i, f (i+1,m) * f (i+1,m+1) = 1 + f (i+2,m) * f (i, m+1) := by
  exact fun m i ↦ Frieze.diamondrule m i


lemma diamond_example (n : ℕ)(f : Fin (n+2) × ℤ → ℚ) [Frieze n f] : ∀ m, f (1,m) * f (1,m+1) = 1 + f (2,m) * f (0, m+1) := by
  intro m
  calc f (1,m) * f (1,m+1) = f (0+1,m) * f (0+1,m+1) := by exact rfl
    _= 1 + f (0+2,m) * f (0, m+1) := by exact Frieze.diamondrule m 0
    _= 1 + f (2,m) * f (0,m+1) := by rw [zero_add]



lemma base_continuant (m : ℤ)  (f : Fin (n+2) × ℤ → ℚ) [Frieze n f] : f (2,m) = f (1,m) * f (1,m+1) -1 := by
  have h1 : f (0, m+1) = 1 := by exact Frieze.topBorder1s (m + 1)
  have h2 : f (2,m) = f (2,m) * f (0, m+1):=  by
    rw [h1]
    exact Eq.symm (Rat.mul_one (f (2, m)))
  have h3 :  f (1,m) * f (1,m+1) = 1 + f (2,m) * f (0, m+1) := by apply diamond_example

  calc f (2,m) = f (2,m) * f (0, m+1) := by exact h2
  _ = f (1,m) * f (1,m+1) -1  := by exact Eq.symm (sub_eq_of_eq_add' h3)





lemma continuant (n : ℕ) (f : Fin (n+2) × ℤ → ℚ) [Frieze n f] : ∀ m, ∀ i, f (i+2,m) = f (i+1,m)* f (1,m+i+1) - f (i,m) := by  sorry
-- How do we make a proof by induction?
