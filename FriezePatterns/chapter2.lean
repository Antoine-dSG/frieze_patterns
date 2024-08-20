import FriezePatterns.chapter1
---- n-Flutes ----

structure flute (n : ℕ) where -- changed class to structure so that Lean displays f.a g.a instead of flute (n+3).a flute (n+2).a
  a : ℕ → ℕ
  pos : ∀ i, a i > 0
  hd : a 0 = 1
  period : ∀ k, a k = a (k+n-1)
  div : ∀ k, a (k+1) ∣ (a k + a (k+2))

def csteFlute (n : ℕ) : Inhabited (flute n) := by -- Inhabited is probably better than Nonempty here, as we actually construct an inhabitant of flute n, so Lean lets us extract *the* inhabitant
  let a : ℕ → ℕ := λ _ => 1
  have pos : ∀ i, a i > 0 := λ _ => by simp
  have hd : a 0 = 1 := by rfl
  have period : ∀ k, a k = a (k+n-1) := λ k => by rfl
  have div : ∀ k, a (k+1) ∣ (a k + a (k+2)) := λ k => by simp
  exact ⟨a, pos, hd, period, div⟩

-- Set of all flutes of height n.
def fluteSet (n : ℕ) : Set (flute n) :=
  { f | true }

-- The set of all flutes of height n is nonempty. We might need this in Chapter 3.
lemma fluteSetNonEmpty (n : ℕ) : Nonempty (fluteSet n) := by
  rcases csteFlute n with ⟨f⟩
  use f
  rfl



-- Might not be useful
def FibFluteEven (n k : ℕ) : ℕ :=
  if n = 0 then
    1
  else if n = 1 then
    1
  else if k ≥ n-1 then
      FibFluteEven n (k-(n-1))
  else if k < n/2 then -- careful of the inequality here
        Nat.fib (2*k+1)
  else
        Nat.fib (2*(n-k))

def FibFluteOdd (n k : ℕ) : ℕ :=
  if n = 0 then
    1
  else if n = 1 then
    1
  else
    if k ≥ n-1 then
      FibFluteOdd n (k-(n-1))
    else
      if k ≤ n/2 then -- careful of the inequality here
        Nat.fib (2*k+1)
      else
        Nat.fib (2*(n-k))


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
  have pos : ∀ i, a_even k i > 0 := by
    intro i
    induction' i using Nat.strong_induction_on with i ih
    by_cases hi : i ≥ 2*k+1
    unfold a_even ; simp [hi]
    exact ih (i-(2*k)-1) (by omega)
    by_cases hi₂ : i < k+1
    simp [a_even, hi, hi₂]
    simp [a_even, hi, hi₂] ; omega
  have hd : a_even k 0 = 1 := by
    simp [a_even]
  have period : ∀ i, a_even k i = a_even k (i+(2*k+2)-1) := by
    intro i
    nth_rw 2 [a_even]
    simp
    have hj : i + (2 * k + 1) - 2 * k - 1 = i := by omega
    simp [hj]
  have div : ∀ i, a_even k (i+1) ∣ (a_even k i + a_even k (i+2)) := by
    intro i
    induction' i using Nat.strong_induction_on with i ih
    by_cases hi : i ≥ 2*k + 1
    have hi₂ : i + 1 ≥ 2 * k + 1 := by omega
    have hi₃ : 2 * k ≤ i + 1 := by omega
    unfold a_even
    simp [hi₂, hi, hi₃]
    have hi₄ : i + 1 - 2 * k - 1 = (i - 2 * k - 1) + 1 := by omega
    have hi₅ : i + 2 - 2 * k - 1 = (i - 2 * k - 1) + 2 := by omega
    have hi₆ : (i - 2 * k - 1) < i := by omega
    rw [hi₄, hi₅]
    -- exact ih (i - 2 * k - 1)
    sorry
    sorry
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


def a_1 (n : ℕ) (f : flute (n+3)) (h : f.a 1 = 1) (k : ℕ) : ℕ :=
  if k ≥ n+1 then
    a_1 n f h (k-(n+1))
  else if k = 0 then
    f.a 0
  else
    f.a (k+1)

def aux_1 (n : ℕ) (f : flute (n+3)) (h : f.a 1 = 1) : flute (n+2) := by
  have pos : ∀ i, a_1 n f h i > 0 := by
    intro i
    induction' i using Nat.strong_induction_on with i ih
    by_cases hi : i ≥ n+1
    unfold a_1 ; simp [hi]
    exact ih (i-(n+1)) (by omega)
    by_cases hi₂ : i = 0
    simp [a_1, hi₂]
    exact f.pos 0
    simp [a_1, hi, hi₂]
    exact f.pos (i+1)
  have hd : a_1 n f h 0 = 1 := by
    simp [a_1, f.hd]
  have period : ∀ i, a_1 n f h i = a_1 n f h (i+(n+2)-1) := by
    intro i
    nth_rw 2 [a_1]
    simp
  have div : ∀ i, a_1 n f h (i+1) ∣ (a_1 n f h i + a_1 n f h (i+2)) := by
    intro i
    induction' i using Nat.strong_induction_on with i ih
    by_cases hi : i ≥ n+1
    have hi₂ : n ≤ i := by omega
    have hi₃ : n ≤ i+1 := by omega
    unfold a_1 ; simp [hi, hi₂, hi₃]
    specialize ih (i-(n+1)) (by omega)
    have hi₄ : i-(n+1)+1 = i-n := by omega
    have hi₅ : i-(n+1)+2 = i+1-n := by omega
    rw [hi₄, hi₅] at ih ; exact ih
    by_cases hi₂ : i = 0
    unfold a_1 ; simp [hi, hi₂]
    match n with
    | 0 => simp [hd]
    | 1 =>
      simp
      rw [hd, f.hd]
      nth_rw 1 [←h]
      have : f.a 3 = 1 := by
        have := f.period 0
        simp [f.hd] at this
        rw [←this]
      nth_rw 3 [←this]
      simp [f.div 1]
    | n+2 =>
      simp [f.hd]
      rw [←h]
      exact f.div 1
    by_cases hi₃ : i+1 ≥ n+1
    have hi₄ : i=n := by omega
    unfold a_1 ; simp [hi, hi₂, hi₃, hi₄, hd]
    by_cases hi₄ : i+2 ≥ n+1
    have hi₅ : i+1 = n := by omega
    unfold a_1 ; simp [hi, hi₂, hi₃, hi₄, hi₅]
    match n with
    | 0 => simp [f.hd]
    | 1 =>
      simp
      rw [hd]
      have : f.a 3 = 1 := by
        have := f.period 0
        simp [f.hd] at this
        rw [←this]
      nth_rw 2 [←this]
      simp [f.div 1]
    | n+2 =>
      simp [hd]
      have h : f.a (n+2+2) = 1 := by
        have := f.period 0
        simp [f.hd] at this
        rw [←this]
      nth_rw 2 [←h]
      exact f.div (n+2)
    unfold a_1 ; simp [hi, hi₂, hi₃, hi₄]
    exact f.div (i+1)
  exact ⟨a_1 n f h, pos, hd, period, div⟩

def a_2 (n : ℕ) (f : flute (n+3)) (h : f.a (n+1) = 1) (k : ℕ) : ℕ :=
  if k ≥ n+1 then
    a_2 n f h (k-(n+1))
  else
    f.a k

def aux_2 (n : ℕ) (f : flute (n+3)) (h : f.a (n+1) = 1) : flute (n+2) := by
  have pos : ∀ i, a_2 n f h i > 0 := by sorry
  have hd : a_2 n f h 0 = 1 := by
    simp [a_2, f.hd]
  have period : ∀ i, a_2 n f h i = a_2 n f h (i+(n+2)-1) := by
    intro i
    nth_rw 2 [a_2]
    simp
  have div : ∀ i, a_2 n f h (i+1) ∣ (a_2 n f h i + a_2 n f h (i+2)) := by sorry
  exact ⟨a_2 n f h, pos, hd, period, div⟩

def a_3 (n : ℕ) (f : flute (n+3)) (i : ℕ) (hi : i ≤ n ∧ f.a (i+1) = f.a i + f.a (i+2)) (k : ℕ) : ℕ :=
  if k ≥ n+1 then
    a_3 n f i hi (k-(n+1))
  else if k ≤ i then
    f.a k
  else f.a (k+1)

def aux_3 (n : ℕ) (f : flute (n+3)) (j : ℕ) (hj : j ≤ n ∧ f.a (j+1) = f.a j + f.a (j+2)) : flute (n+2) := by
  -- the proof of this will probably be more complicated than the previous two
  have pos : ∀ i, a_3 n f j hj i > 0 := by sorry
  have hd : a_3 n f j hj 0 = 1 := by sorry
  have period : ∀ i, a_3 n f j hj i = a_3 n f j hj (i+(n+2)-1) := by sorry
  have div : ∀ i, a_3 n f j hj (i+1) ∣ (a_3 n f j hj i + a_3 n f j hj (i+2)) := by sorry
  exact ⟨a_3 n f j hj, pos, hd, period, div⟩

theorem FluteBounded (n : ℕ) (hn: n>0) (f : flute n) : ∀ i ≤ n-1, f.a i ≤ Nat.fib n := by
  -- note the statement is false without hn
  suffices : ∃ l, ∀ i ≤ n-1, ((i ≠ l → f.a i ≤ Nat.fib (n-2+1)) ∧ (i=l → f.a i ≤ Nat.fib n)) -- we strengthen the inductive hypothesis to avoid having to do everything twice
  · rcases this with ⟨l, hl⟩
    intro i hi
    match n with
    | 0 => linarith
    | 1 =>
      simp at *
      simp [hi, f.hd]
    | n+2 =>
      simp at hl
      specialize hl i (by omega)
      by_cases hil : i=l
      exact hl.2 hil
      have := hl.1 hil
      have : Nat.fib (n+1) ≤ Nat.fib (n+2) := Nat.fib_mono (by omega)
      omega
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => linarith
  | 1 =>
    use 0
    intro i hi
    simp at *
    apply And.intro (λ _ => by omega)
    simp [hi, f.hd]
  | 2 =>
    use 2
    intro i hi
    simp at *
    apply And.intro _ (λ _ => by omega)
    have h₀ := f.hd
    have h₁ : f.a 1 = 1 := by
      have := f.period 0
      simp [f.hd] at this
      rw [←this]
    match i with
    | 0 => simp [h₀]
    | 1 => simp [h₁]
    | i+2 => linarith
  | n+3 =>
    have h₁ := ih (n+2) (by linarith) (by linarith)
    simp at *
    have hh : 0 < Nat.fib (n+2) := Nat.fib_pos.mpr (by omega)
    have hh₂ : Nat.fib (n+1) ≤ Nat.fib (n+2) := Nat.fib_mono (by omega)
    have hh₃ : Nat.fib (n+3) = Nat.fib (n+1) + Nat.fib (n+2) := Nat.fib_add_two
    have hh₄ : 0 < Nat.fib (n+3) := Nat.fib_pos.mpr (by omega)
    rcases FluteReduction _ f with (h₂ | h₂) | h₂
    let g := aux_1 n f h₂ -- case 1: f.a 1 = 1
    use n+3 ; intros i hi
    apply And.intro _ (λ _ => by omega)
    intro
    match i with
    | 0 =>
      simp [f.hd, hh, add_assoc]
      omega
    | 1 =>
      simp [h₂, add_assoc]
      omega
    | i+2 =>
      specialize h₁ g
      rcases h₁ with ⟨l, h₁⟩
      specialize h₁ (i+1) (by omega)
      unfold_let at h₁ ; unfold aux_1 at h₁ ; unfold a_1 at h₁ ; simp at h₁
      simp [add_assoc]
      by_cases hi₂ : n ≤ i
      have : i = n := by omega
      rw [this]
      have : f.a (n+2) = 1 := by
        have := f.period 0
        simp [f.hd] at this
        rw [←this]
      simp [this, hh]
      omega
      simp [hi₂, add_assoc] at h₁
      by_cases hil : i+1 = l
      exact h₁.2 hil
      have := h₁.1 hil
      omega
    let g := aux_2 n f h₂ -- case 2 : f.a (n+1) = 1
    simp [add_assoc] at h₂
    use n+3 ; intros i hi ; apply And.intro _ (λ _ => by omega)
    intro
    by_cases hi₂ : i = n+1
    simp [hi₂, h₂, hh, add_assoc] ; omega
    by_cases hi₃ : i = n+2
    have := f.period 0
    simp at this ; simp [add_assoc, hi₃, ←this, f.hd, hh] ; omega
    rcases h₁ g with ⟨l, h₁⟩
    specialize h₁ i (by omega)
    have hi₄ : ¬ n+1 ≤ i := by omega
    unfold_let at h₁ ; unfold aux_2 at h₁ ; unfold a_2 at h₁ ; simp [hi₄] at h₁
    by_cases hil : i = l
    exact h₁.2 hil
    have := h₁.1 hil
    simp [add_assoc] ; omega
    rcases h₂ with ⟨j, hj⟩
    simp at hj ; simp [add_assoc]
    let g := aux_3 n f j hj -- case 3 : ∃ i ≤ n, f.a (i+1) = f.a i + f.a (i+2)
    have key₁ : ∀ i ≤ n+2, i ≠ j+1 → f.a i ≤ Nat.fib (n+2) := by
      intro i hi hij
      by_cases hij : i≤j
      rcases h₁ g with ⟨l, h₁⟩
      specialize h₁ i (by omega)
      have hi₂ : ¬ n+1 ≤ i := by omega
      unfold_let at h₁ ; unfold aux_3 at h₁ ; unfold a_3 at h₁ ; simp [hij, hi₂] at h₁
      omega
      have hij : ¬ i≤j+1 := by omega
      rcases h₁ g with ⟨l, h₁⟩
      specialize h₁ (i-1) (by omega)
      unfold_let at h₁ ; unfold aux_3 at h₁ ; unfold a_3 at h₁ ; simp [hij] at h₁
      by_cases hi₃ : n+1 ≤ i-1
      have hi₄ : i = n+2 := by omega
      rw [hi₄]
      have := f.period 0
      simp [f.hd] at this
      have : Nat.fib (n+2) > 0 := Nat.fib_pos.mpr (by omega)
      omega
      have hi₄ : ¬ i-1<j := by omega
      simp [hi₃, hi₄, @Nat.sub_add_cancel i 1 (by omega)] at h₁
      omega
    use j+1 ; intro i hi
    by_cases hij : i = j+1
    · rw [hij, hj.2]
      specialize ih (n+1) (by omega) (by omega)
      apply And.intro (λ _ => by omega)
      intro
      rcases h₁ g with ⟨l, h₁⟩
      by_cases hjl : l = j+1
      have hf₁ := (h₁ j (by omega)).1 (by omega)
      unfold_let at hf₁ ; unfold aux_3 at hf₁ ; unfold a_3 at hf₁ ; simp [hjl] at hf₁
      have : ¬ (n+1) ≤ j := by omega
      simp [this] at hf₁
      have hf₂ := (h₁ (j+1) (by omega)).2 (by omega)
      unfold_let at hf₂ ; unfold aux_3 at hf₂ ; unfold a_3 at hf₂ ; simp [hjl] at hf₂
      by_cases hj : n ≤ j
      simp [hj] at hf₂
      have hj : j = n := by omega
      rw [hj] ; rw [hj] at hf₁
      have := f.period 0
      simp [f.hd] at this
      omega
      simp [hj, add_assoc] at hf₂
      omega
      have hf₁ := (h₁ (j+1) (by omega)).1 (by omega)
      have hf₂ := key₁ j (by omega) (by omega)
      unfold_let at hf₁ ; unfold aux_3 at hf₁ ; unfold a_3 at hf₁ ; simp [hj] at hf₁
      by_cases hj : n ≤ j
      have hj : j = n := by omega
      rw [hj] ; rw [hj] at hf₂
      have := f.period 0
      simp [f.hd] at this
      have : Nat.fib (n+1) > 0 := Nat.fib_pos.mpr (by omega)
      omega
      simp [hj, add_assoc] at hf₁
      omega
    · have := key₁ i hi hij
      exact And.intro (by omega) (by omega)
