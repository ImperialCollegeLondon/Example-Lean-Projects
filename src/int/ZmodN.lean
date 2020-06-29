-- Integers mod 37

-- a demonstration of how to use equivalence relations and equivalence classes in Lean.

-- We define the "congruent mod 37" relation on integers,
-- prove it is an equivalence relation, define Zmod37 to be the equivalence classes,
-- and put a ring structure on the quotient.

import tactic


definition cong_mod37 (a b : ℤ) := ∃ (k : ℤ), k * 37 = b - a

-- Now check it's an equivalence reln!

theorem cong_mod_refl : reflexive (cong_mod37) :=
begin
  intro x,
  -- to prove cong_mod37 x x we just observe that k=0 will do.
  use 0, -- this is k
  simp,
end

theorem cong_mod_symm : symmetric (cong_mod37) :=
begin
  intros a b H,
  -- H : cond_mod37 a b
  cases H with k Hk,
  -- Hk : k * 37 = (b - a)
  -- Goal is to find an integer k' with k' * 37 = a - b  
  use -k,
  simp [Hk],
end

theorem cong_mod_trans : transitive (cong_mod37) :=
begin
  intros a b c Hab Hbc,
  cases Hab with k Hk,
  cases Hbc with l Hl,
  -- k*37 = b - a, l*37 = c - b
  -- need to solve m*37 = c - a
  sorry -- can you finish it?
end

-- so we've now seen a general technique for proving a ≈ b -- existsi (the k that works)

theorem cong_mod_equiv : equivalence (cong_mod37) :=
⟨cong_mod_refl, cong_mod_symm, cong_mod_trans⟩

instance Z_setoid : setoid ℤ := { r := cong_mod37, iseqv := cong_mod_equiv }

definition Zmod37 := quotient (Z_setoid)

namespace Zmod37

definition reduce_mod37 : ℤ → Zmod37 := quot.mk (cong_mod37)

-- now a little bit of basic interface

instance coe_int_Zmod37 : has_coe ℤ (Zmod37) := ⟨reduce_mod37⟩

instance : has_zero (Zmod37) := ⟨reduce_mod37 0⟩
instance : has_one (Zmod37) := ⟨reduce_mod37 1⟩
instance : inhabited (Zmod37) := ⟨0⟩

@[simp] theorem of_int_zero : (0 : (Zmod37))  = reduce_mod37 0 := rfl 
@[simp] theorem of_int_one : (1 : (Zmod37))  = reduce_mod37 1 := rfl 

-- now back to the maths

-- here's a useful lemma -- it's needed to prove addition is well-defined on the quotient.
-- Note the use of quotient.sound to get from Zmod37 back to Z

lemma congr_add (a₁ a₂ b₁ b₂ : ℤ) : a₁ ≈ b₁ → a₂ ≈ b₂ → ⟦a₁ + a₂⟧ = ⟦b₁ + b₂⟧ :=
begin
  intros H1 H2,
  cases H1 with m Hm, -- Hm : m * 37 = b₁ - a₁
  cases H2 with n Hn, -- Hn : n * 37 = b₂ - a₂
  -- goal is ⟦a₁ + a₂⟧ = ⟦b₁ + b₂⟧
  apply quotient.sound,
  -- goal now a₁ + a₂ ≈ b₁ + b₂, and we know how to do these.
  use (m + n),
  rw [add_mul, Hm, Hn],
  ring,
end 

-- That lemma above is *exactly* what we need to make sure addition is
-- well-defined on Zmod37, so let's do this now, using quotient.lift 

-- note: stuff like "add" is used everywhere so it's best to protect.
protected definition add : Zmod37 → Zmod37 → Zmod37 :=
quotient.lift₂ (λ a b : ℤ, ⟦a + b⟧) (begin
  show ∀ (a₁ a₂ b₁ b₂ : ℤ), a₁ ≈ b₁ → a₂ ≈ b₂ → ⟦a₁ + a₂⟧ = ⟦b₁ + b₂⟧,
  -- that's what quotient.lift₂ reduces us to doing. But we did it already!
  exact congr_add,
end)

-- Now here's the lemma we need for the definition of neg

-- I spelt out the proof for add, here's a quick term proof for neg.

lemma congr_neg (a b : ℤ) : a ≈ b → ⟦-a⟧ = ⟦-b⟧ :=
λ ⟨m, Hm⟩, quotient.sound ⟨-m, by simp [Hm]⟩

protected def neg : Zmod37 → Zmod37 := quotient.lift (λ a : ℤ, ⟦-a⟧) congr_neg

-- For multiplication I won't even bother proving the lemma, I'll just let ring do it

protected def mul : Zmod37 → Zmod37 → Zmod37 :=
quotient.lift₂ (λ a b : ℤ, ⟦a*b⟧) (λ a₁ a₂ b₁ b₂ ⟨m₁,H₁⟩ ⟨m₂,H₂⟩,quotient.sound ⟨b₁ * m₂ + a₂ * m₁,
  by {rw [add_mul, mul_assoc, mul_assoc, H₁, H₂], ring}⟩)

-- this adds notation to the quotient

instance : has_add (Zmod37) := ⟨Zmod37.add⟩
instance : has_neg (Zmod37) := ⟨Zmod37.neg⟩
instance : has_mul (Zmod37) := ⟨Zmod37.mul⟩

-- these are now very cool proofs:
@[simp] lemma coe_add {a b : ℤ} : (↑(a + b) : Zmod37) = ↑a + ↑b := rfl
@[simp] lemma coe_neg {a : ℤ} : (↑(-a) : Zmod37) = -↑a := rfl
@[simp] lemma coe_mul {a b : ℤ} : (↑(a * b) : Zmod37) = ↑a * ↑b := rfl

-- The proof of coe_add would not be rfl at all if you defined addition on the quotient
-- by choosing representatives and then adding them. Note that choosing reps
-- and adding them is exactly what mathematicians do; they shoot first and
-- ask questions later.

-- Now here's how to use quotient.induction_on and quotient.sound

instance : add_comm_group (Zmod37)  :=
{ add_comm_group .
  zero         := 0, -- because we already defined has_zero
  add          := (+), -- could also have written has_add.add
  neg          := has_neg.neg,
  zero_add     := 
    λ abar, quotient.induction_on abar (begin
      -- goal is ∀ (a : ℤ), 0 + ⟦a⟧ = ⟦a⟧ -- that's what quotient.induction_on does for us
      intro a,
      apply quotient.sound, -- works because 0 + ⟦a⟧ is by definition ⟦0⟧ + ⟦a⟧ which is by definition ⟦0 + a⟧
      -- goal is now 0 + a ≈ a
      -- here's the way we used to do it.
      existsi (0 : ℤ),
      simp,
      -- but there are tricks now, which I'll show you with add_zero and add_assoc.
    end),
  add_assoc    := λ abar bbar cbar,quotient.induction_on₃ abar bbar cbar (λ a b c,
    begin
      -- goal now ⟦a⟧ + ⟦b⟧ + ⟦c⟧ = ⟦a⟧ + (⟦b⟧ + ⟦c⟧)
      apply quotient.sound,
      -- goal now a + b + c ≈ a + (b + c)
      rw add_assoc, -- done :-) because after a rw a goal is closed if it's of the form x ≈ x, as ≈ is
                    -- known to be reflexive.
    end),
  add_zero     := -- I will introduce some more sneaky stuff now now
                  -- add_zero for Zmod37 follows from add_zero on Z.
                  -- Note use of $ instead of the brackets
    λ abar, quotient.induction_on abar $ λ a, quotient.sound $ by rw add_zero,
                  -- that's it! Term mode proof.
  add_left_neg := -- super-slow method not even using quotient.induction_on 
    begin
      intro abar,
      cases (quot.exists_rep abar) with a Ha,
      rw [←Ha],
      apply quot.sound,
      existsi (0:ℤ),
      simp,
    end,
  -- but really all proofs should just look something like this
  add_comm     := λ abar bbar, quotient.induction_on₂ abar bbar $ λ _ _,quotient.sound $ by rw add_comm,
  -- the noise at the beginning is just the machine; all the work is done by the rewrite
}

-- Now let's just nail this using all the tricks in the book. All ring axioms on the quotient
-- follow from the corresponding axioms for Z.
instance : comm_ring (Zmod37) :=
{ 
  mul := (*), 
  -- Now look how the proof of mul_assoc is just the same structure as add_comm above
  -- but with three variables not two
  mul_assoc := λ a b c, quotient.induction_on₃ a b c $ λ _ _ _, quotient.sound $ by rw mul_assoc,
  one := 1,
  one_mul := λ a, quotient.induction_on a $ λ _, quotient.sound $ by rw one_mul,
  -- can you finish the job?
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
  mul_comm := sorry,
  ..Zmod37.add_comm_group
}

end Zmod37
