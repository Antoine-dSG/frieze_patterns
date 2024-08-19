import FriezePatterns.chapter1
---- n-Flutes ----

class flute (n : ℕ) where
  a : ℕ → ℕ
  pos : ∀ i, a i > 0
  hd : a 0 = 1
  period : ∀ k, a k = a (k+n-1)
  div : ∀ k, a (k+1) ∣ (a k + a (k+2))

def nFluteNonEmpty (n : ℕ) : Inhabited (flute n) := by -- Inhabited is probably better than Nonempty here, as we actually construct an inhabitant of flute n, so Lean lets us extract *the* inhabitant
  let a : ℕ → ℕ := λ _ => 1
  have pos : ∀ i, a i > 0 := λ _ => by simp
  have hd : a 0 = 1 := by rfl
  have period : ∀ k, a k = a (k+n-1) := λ k => by rfl
  have div : ∀ k, a (k+1) ∣ (a k + a (k+2)) := λ k => by simp
  exact ⟨a, pos, hd, period, div⟩

def a_odd (k i : ℕ) : ℕ :=
  if k = 0 then
    1
  else if i ≥ 2*k then
    a_odd k (i-2*k) -- this does not terminate when k=0
    else
    if i < k then
      Nat.fib (2*i+2)
    else
      Nat.fib (1+4*k-2*i)

def fib_flute_odd (k : ℕ) : flute (2*k+1) := by
  by_cases hk : k = 0
  exact ⟨a_odd k 0, λ i => by simp [hk, a_odd], by simp [hk, a_odd], by simp [hk, a_odd], λ _ => by simp⟩
  have pos : ∀ i, a_odd k i > 0 := by
    intro i
    induction' i using Nat.strong_induction_on with i ih
    by_cases hi : i ≥ 2*k
    unfold a_odd ; simp [hi, hk]
    exact ih (i-(2*k)) (by omega)
    by_cases hi₂ : i < k
    simp [a_odd, hk, hi, hi₂]
    simp [a_odd, hk, hi, hi₂] ; omega
  have hd : a_odd k 0 = 1 := by
    simp [hk, a_odd]
  have period : ∀ i, a_odd k i = a_odd k (i+(2*k+1)-1) := by
    intro i
    nth_rw 2 [a_odd]
    simp [hk]
  have div : ∀ i, a_odd k (i+1) ∣ (a_odd k i + a_odd k (i+2)) := by
    intro i
    induction' i using Nat.strong_induction_on with i ih
    by_cases hi : i ≥ 2*k
    · have hi₂ : 2*k ≤ i+1 := by omega
      have hi₃ : 2*k ≤ i+2 := by omega
      unfold a_odd ; simp [hk, hi, hi₂, hi₃]
      specialize ih (i-(2*k)) (by omega)
      have hi₄ : i - 2 * k + 1 = i + 1 - 2 * k := by omega
      have hi₅ : i - 2 * k + 2 = i + 2 - 2 * k := by omega
      rw [hi₄, hi₅] at ih
      exact ih
    · by_cases hi₂ : i+2<k
      have hi₃ : i+1 < k := by omega
      have hi₄ : i < k := by omega
      have hi₅ : ¬ 2*k ≤ i+1 := by omega
      have hi₆ : ¬ 2*k ≤ i+2 := by omega
      unfold a_odd ; simp [hk, hi, hi₂, hi₃, hi₄, hi₅, hi₆]
      ring_nf
      have : 6 + i*2 = (2*i+3)+2+1 := by omega
      rw [this, Nat.fib_add (2*i+3) 2]
      ring_nf
      have h :=
        calc Nat.fib (2+i*2) + Nat.fib (3+i*2) = Nat.fib (i*2+2) + Nat.fib ((i*2+2)+1) := by ring_nf
        _ = Nat.fib ((i*2+2)+2) := by rw [←Nat.fib_add_two]
        _ = Nat.fib (4+i*2) := by ring_nf
      rw [h]
      use 3 ; omega
      by_cases hi₃ : i+1 < k
      have hi₄ : ¬ 2*k ≤ i+1 := by omega
      have hi₅ : ¬ 2*k ≤ i+2 := by omega
      have hi₆ : i < k := by omega
      have hi₇ : 2 * (i+1)+2 = 2*k := by omega
      have hi₈ : 2 * i+2 = 2*k-2 := by omega
      have hi₉ : 1+4*k-2*(i+2) = (2*k-1)+2 := by omega
      unfold a_odd ; simp [hk, hi, hi₂, hi₃, hi₄, hi₅, hi₆, hi₇, hi₈, hi₉]
      simp [Nat.fib_add_two, ←add_assoc]
      have : Nat.fib (2*k-2) + Nat.fib (2*k-1) = Nat.fib (2*k) := by
        have : 2*k = (2*k-2)+2 := by omega
        nth_rw 3 [this]
        rw [Nat.fib_add_two]
        have : 2*k-2+1=2*k-1 := by omega
        rw [this]
      rw [this]
      have : 2*k-1+1=2*k := by omega
      rw [this]
      use 2 ; omega
      · by_cases hi₄ : i < k
        have hi₅ : ¬ 2*k ≤ i+1 := by omega
        unfold a_odd ; simp [hk, hi, hi₂, hi₃, hi₄, hi₅]
        by_cases hk₁ : k = 1
        have hi₀ : i = 0 := by omega
        simp [hk₁, hi₀]
        use 1 ; rfl
        have hi₆ : ¬ 2*k ≤ i+2 := by omega
        simp [hi₆]
        have hi₇ : 1+4*k-2*(i+1) = (2*k-1)+2 := by omega
        have hi₈ : 2*i+2 = (2*k-1)+1 := by omega
        have hi₉ : 1+4*k-2*(i+2) = 2*k-1 := by omega
        rw [hi₇, hi₈, hi₉]
        use 1; simp [Nat.fib_add_two] ; omega
        by_cases hi₅ : ¬ 2*k ≤ i+2
        have hi₆ : ¬ 2*k ≤ i+1 := by omega
        unfold a_odd ; simp [hk, hi, hi₂, hi₃, hi₄, hi₅, hi₆]
        have hi₇ : 1+4*k-2*(i+1) = 4*k-2*i-1 := by omega
        have hi₈ : 1+4*k-2*i = 4*k-2*i-2+2+1 := by omega
        have hi₉ : 1+4*k-2*(i+2) = 4*k-2*i-3 := by omega
        rw [hi₇, hi₈, hi₉, Nat.fib_add]
        simp [Nat.fib_add_two]
        use 3
        rw [add_assoc, add_comm, add_assoc]
        have hi₁₀ : 4*k-2*i-2 = (4*k-2*i-3)+1 := by omega
        have hi₁₁ : 4*k-2*i-3+1+1 = 4*k-2*i-1 := by omega
        rw [hi₁₀, ← Nat.fib_add_two, hi₁₁]
        omega
        · push_neg at hi₅
          by_cases hi₆ : ¬ 2*k ≤ i+1
          unfold a_odd ; simp [hk, hi, hi₂, hi₃, hi₄, hi₅, hi₆]
          have hi₇ : 1+4*k-2*(i+1) = 3 := by omega
          have hi₈ : 1+4*k-2*i = 5 := by omega
          have hi₉ : i+2-2*k = 0 := by omega
          have hk₂ : 0<k := by omega
          unfold a_odd
          simp [hi₇, hi₈, hi₉, hk, hk₂]
          use 3 ; simp [Nat.fib_add_two]
          push_neg at hi₆
          have hi₇ : i+1-2*k = 0 := by omega
          have hi₈ : i+2-2*k = 1 := by omega
          unfold a_odd ; simp [hk, hi, hi₂, hi₃, hi₄, hi₅, hi₆, hi₇, hi₇, hi₈]
          unfold a_odd ; simp [hk]
  exact ⟨a_odd k, pos, hd, period, div⟩

def a_even (k i : ℕ) : ℕ :=
  if i ≥ 2*k+1 then
    a_even k (i-2*k-1)
  else if i < k+1 then
    Nat.fib (2*i+2)
    else
    Nat.fib (3+4*k-2*i)

def fib_flute_even (k : ℕ) : flute (2*k+2) := by
  -- flute 0 is inhabited under our definition, but it is trivial (and there are no frieze patterns of height 0 anyways)
  -- the proof should be similar to the odd case, maybe we don't even have to by cases on k=0 here?
  have pos : ∀ i, a_even k i > 0 := by sorry
  have hd : a_even k 0 = 1 := by sorry
  have period : ∀ i, a_even k i = a_even k (i+(2*k+2)-1) := by sorry
  have div : ∀ i, a_even k (i+1) ∣ (a_even k i + a_even k (i+2)) := by sorry
  exact ⟨a_even k, pos, hd, period, div⟩


lemma FluteReduction (n : ℕ)(f : flute n) : ((f.a 1 =1) ∨ (f.a (n-2) = 1)) ∨ (∃ i ≤ n-3, f.a (i+1) = f.a i + f.a (i+2)) := by
  by_contra! H
  rcases H with ⟨⟨h₁, h₂⟩, h₃⟩
  have ha₁ : (↑ (f.a 1) : ℤ) - f.a 0 > 0 := by
    have := f.pos 1
    have := f.hd
    omega
  have ha₂ : (↑ (f.a (n-1)) : ℤ) - f.a (n-2) < 0 := by
    have := f.pos (n-2)
    have := f.period 0
    simp [f.hd] at this
    rw [←this]
    omega
  have key : ∀ i ≤ n-3, (↑(f.a i):ℤ) + f.a (i+2) ≥ (f.a (i+1))*2 := by
    intro i hi
    rcases f.div i with ⟨k, hk⟩
    match k with
    | 0 =>
      simp at hk
      have := f.pos i
      omega
    | 1 =>
      specialize h₃ i hi
      omega
    | k+2 =>
      nlinarith
  have key₂ : ∀ i ≤ n-3, (↑ (f.a (i+2)) : ℤ) - f.a (i+1) ≥ f.a 1 - f.a 0 := by
    intro i hi
    induction' i with i ih
    specialize key 0 hi
    linarith
    specialize key (i+1) hi
    specialize ih (by omega)
    linarith
  have key₃ : f.a (n-1) = 1 := by
    have := f.period 0
    simp [f.hd] at this
    rw [←this]
  match n with -- n ≤ 2 contradicts with h₁ and h₂
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith
  | n+3 =>
    simp_all
    specialize key₂ n (by omega)
    linarith

theorem FluteBounded (n : ℕ)(f : flute n) : ∀ i, f.a i ≤ Nat.fib n := by sorry
