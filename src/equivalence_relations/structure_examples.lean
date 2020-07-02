import tactic

-- what's a structure?

structure group' (G : Type) [has_mul G] [has_one G] [has_inv G] :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(one_mul : ∀ a : G, 1 * a = a)
(mul_one : ∀ a : G, a * 1 = a)
(mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

-- easy structure

@[ext] structure silly :=
(sillyint : ℤ)
(sillynat : ℕ)

#print prefix silly

/-
silly.sillyint : silly → ℤ
silly.sillynat : silly → ℕ
silly.mk : ℤ → ℕ → silly
silly.rec -- useful for induction
silly.ext : ∀ (x y : silly), x.sillyint = y.sillyint → x.sillynat = y.sillynat → x = y
silly.ext_iff : ∀ (x y : silly), x = y ↔ x.sillyint = y.sillyint ∧ x.sillynat = y.sillynat

-/

-- #check silly -- silly : Type, i.e. silly is a Type

-- how to make a term of type silly

def x : silly := silly.mk 7 37

def y : silly :=
{ sillyint := 0,
  sillynat := 1
}

-- silly is an implementation of ℤ × ℕ
-- ℤ × ℕ is another implentation of this

example : x ≠ y :=
begin
  intro h,
  rw silly.ext_iff at h,
  cases h,
  simp [x,y] at *,
  linarith [x, y],
end

-- proof that silly is the same as ℤ × ℕ

example : silly ≃ ℤ × ℕ :=
{ to_fun := λ s, ⟨s.sillyint, s.sillynat⟩,
  inv_fun := λ x, {sillyint := x.1, sillynat := x.2},
  left_inv := λ s, by {ext; refl},
  right_inv := λ x, by {ext; refl}
}
