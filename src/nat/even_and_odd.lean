import tactic
/-
The theory of even and odd numbers
-/
def even (n : ℕ) : Prop := ∃ d, n = 2 * d
def odd (n : ℕ) : Prop := ∃ d, n = 2 * d + 1

/-
see https://www.codewars.com/kata/5e998b42dcf07b0001581def/lean
for a completely different approach (inductive definitions)
-/

/- ## interaction with 0 -/

lemma even_zero : even 0 :=
begin
  unfold even,

end

/- ## interaction with succ -/

lemma even_add_one {n : ℕ} : even n → odd (n + 1) := sorry

lemma odd_add_one {n : ℕ} : odd n → even (n + 1) := sorry

/- ## interaction with add -/

theorem odd_add_odd {n m : ℕ} (hn : odd n) (hm : odd m) :
  even (n + m) := sorry

theorem odd_add_even {n m : ℕ} (hn : odd n) (hm : even m) :
  odd (n + m) := sorry

theorem even_add_odd {n m : ℕ} (hn : even n) (hm : odd m) :
  odd (n + m) := sorry

theorem even_add_even {n m : ℕ} (hn : even n) (hm : even m) :
  even (n + m) := sorry

/- ## interaction with one -/

theorem odd_one : odd 1 := sorry

/- ## interaction with mul -/

theorem even_mul_even {n m : ℕ} (hn : even n) (hm : even m) :
  even (n * m) := sorry

theorem even_mul_odd {n m : ℕ} (hn : even n) (hm : odd m) :
  even (n * m) := sorry

theorem odd_mul_even {n m : ℕ} (hn : odd n) (hm : even m) :
  even (n * m) := sorry

theorem odd_mul_odd {n m : ℕ} (hn : odd n) (hm : odd m) :
  odd (n * m) := sorry

/- ## interaction with each other -/

lemma odd_or_even (n : ℕ) : odd n ∨ even n := sorry 

-- hard?
lemma not_odd_and_even {n : ℕ} : ¬ (odd n ∧ even n) := sorry

