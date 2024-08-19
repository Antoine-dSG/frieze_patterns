import FriezePatterns.chapter1
---- n-Diagonals ----

class flute (n : ℕ) where
  a : Fin (n + 1) → ℕ
  pos : ∀ i, a i > 0
  hd : a 0 =1
  hteq : a 0 = a n -- head-tail equality
  div : ∀ i, i ≤ n-2 → a (i+1) ∣ (a i + a (i+2))
/-
Mathlib recommends using Fin n → α to define n-tuples.

Choice of index: Using Fin (n+1) and indexing from 0 to n is probably more convenient: we want to have a coercion from ℕ to Fin _, but it doesn't work if we use Fin n, since Fin 0 is empty.

Warning: flute of height n has n+1 entries
Compare with pattern_n.
-/

lemma nFluteNonEmpty (n : ℕ) : Nonempty (flute n) := by
  let a : Fin (n + 1) → ℕ := λ _ => 1
  have pos : ∀ i, a i > 0 := λ _ => by simp
  have hd : a 0 = 1 := by rfl
  have hteq : a 0 = a n := by rfl
  have div : ∀ i, i ≤ n-2 → a (i+1) ∣ (a i + a (i+2)) := λ i _ => by simp
  exact ⟨⟨a,pos,hd, hteq, div⟩⟩


-- Note the parity of the indices in the definitions below are different from the LaTeX version, since we are using Fin (n+1) instead of Fin n.

-- this case corresponds to n=2k+1 in the LaTeX version, I am using k+k instead of 2k because Mathlib doesn't have many theorems about multiplication of coercions from ℕ to Fin _.

def fib_flute_even (k : ℕ) : flute (k+k) := by
  let a : Fin (k+k+1) → ℕ := by
    intro i
    induction' i with i ih
    use ite (i < k) (Nat.fib (i+i+2)) (Nat.fib (1+k+k+k+k-i-i))
  have pos : ∀ i, a i > 0 := by
    intro i
    induction' i with i ih
    simp [a]
    split
    next h => simp_all only [Nat.fib_pos, lt_add_iff_pos_left, add_pos_iff, pos_add_self_iff, Nat.ofNat_pos, or_true] -- proof term provided by aesop
    next h =>
      simp_all only [not_lt, Nat.fib_pos, tsub_pos_iff_lt] -- aesop
      omega
  have hteq : a 0 = a ↑(k+k) := by
    by_cases hk : k > 0
    · simp [a, hk]
      have key : ↑((k : Fin (k+k+1)) + k) = k+k := by
        rw [Fin.val_add_eq_ite, Fin.val_cast_of_lt (by linarith)]
        simp_all only [gt_iff_lt, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, ↓reduceIte] -- aesop
      simp_all only [gt_iff_lt, add_lt_iff_neg_left, not_lt_zero', ↓reduceIte] -- aesop
      rw [← Nat.sub_sub _ k k, ← Nat.sub_sub _ k k]
      simp_all only [add_tsub_cancel_right, Nat.fib_one] -- aesop
    · simp at hk ; simp [hk]
  have div : ∀ i, i ≤ k+k-2 → a (i+1) ∣ (a i + a (i+2)) := by
    intro i hi
    by_cases hi₂ : i+2 < k
    · simp [a, hi₂]
      norm_cast ; rw [Fin.val_cast_of_lt (by linarith), Fin.val_cast_of_lt (by linarith)]
      -- Most of the following steps are just if-then-else reductions. These are still required even if we define a : ℕ → ℕ.
      have key1 : (if i + 1 < k then Nat.fib (i + 1 + (i + 1) + 2) else Nat.fib (1 + k + k + k + k - (i + 1) - (i + 1))) = Nat.fib (i + 1 + (i + 1) + 2) := by simp [↓reduceIte] ; intros ; linarith
      have : i % (k+k+1) = i := Nat.mod_eq_of_lt (by linarith)
      have key2 : (if i % (k + k + 1) < k then Nat.fib (i % (k + k + 1) + i % (k + k + 1) + 2)
      else Nat.fib (1 + k + k + k + k - i % (k + k + 1) - i % (k + k + 1))) = Nat.fib (i + i + 2) := by
        rw [this]
        simp [↓reduceIte]
        intros ; linarith
      have key3 : (if i + 2 < k then Nat.fib (i + 2 + (i + 2) + 2) else Nat.fib (1 + k + k + k + k - (i + 2) - (i + 2))) = Nat.fib (i + 2 + (i + 2) + 2) := by simp [↓reduceIte] ; intros ; linarith
      rw [key1, key2, key3]
      ring_nf
      have : 6 + i*2 = (2*i+3)+2+1 := by omega
      rw [this, Nat.fib_add (2*i+3) 2]
      ring_nf
      have h :=
        calc Nat.fib (2+i*2) + Nat.fib (3+i*2) = Nat.fib (i*2+2) + Nat.fib ((i*2+2)+1) := by ring_nf
        _ = Nat.fib ((i*2+2)+2) := by rw [←Nat.fib_add_two]
        _ = Nat.fib (4+i*2) := by ring_nf
      rw [h]
      use 3
      omega
    · sorry -- there are ~5 more cases to consider
  exact ⟨a, pos, hteq, div⟩

#eval (fib_flute_even 5).1 -- check the definition is correct

-- this case corresponds to n=2k in the LaTeX version
def fib_flute_odd (k : ℕ) : flute (k+k+1) := by
  let a : Fin (k+k+1+1) → ℕ := by
    intro i
    induction' i with i ih
    use ite (i < k+1) (Nat.fib (i+i+2)) (Nat.fib (3+k+k+k+k-i-i))
  have pos : ∀ i, a i > 0 := sorry
  have hteq : a 0 = a ↑(k+k+1) := sorry
  have div : ∀ i, i ≤ k+k+1-2 → a (i+1) ∣ (a i + a (i+2)) := sorry
  exact ⟨a, pos, hteq, div⟩

#eval (fib_flute_odd 5).1


lemma FluteReduction : 2^2 = 4 := by linarith

theorem FluteBounded : 2^3 = 8 := by linarith
