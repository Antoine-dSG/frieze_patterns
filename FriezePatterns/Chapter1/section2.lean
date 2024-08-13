import FriezePatterns.Chapter1.section1

-- How do we define a sequence? Do we use "instances" ?

theorem mainTheorem : 2^3 = 8 := by linarith

lemma unLB : 2^3 ≥ 8 := by linarith

lemma unUB : 2^3 ≤ 8 := by linarith
