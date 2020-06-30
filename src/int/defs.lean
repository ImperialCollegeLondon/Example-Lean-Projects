-- make all the tactics work
import tactic
--import algebra.pi_instances -- you'll get the wrong 1 on ℕ² if you do this

-- Let's just use Lean's definition of the naturals and not worry
-- about what they are or how to make them.

import data.nat.basic

-- later on we'll do isomorphisms of rings
-- ≃+*
import data.equiv.ring

-- some missing simp lemma that Kenny needed
@[simp] theorem quotient.lift_on_beta₂ {α : Type} {β : Type} [setoid α] (f : α → α → β) (h)
  (x y : α) : ⟦x⟧.lift_on₂ ⟦y⟧ f h = f x y := rfl

-- Let's now experiment 
namespace experiment

/-
An experiment where we try different definitions of the integers. 
-/

--#print int
-- important todo: change all this to Lean 4 syntax
-- TODO: Look up Lean 4 definition of Int.
inductive int : Type
-- with notation ℤ
| of_nat : ℕ → int -- error -- I want this to be a ℤ
-- with notation ↑ [lemme add coercion `ℕ → ℤ` now, named automatically by computer]
| neg_succ_of_nat : ℕ → int

-- a mathematician does not need direct
-- access to either `of_nat` or `neg_succ_of_nat`, because the former is
-- the coercion and the latter is a function of no relevance 
-- (it sends n to -1-n)

notation `ℤ1` := int

namespace int

-- done.

-- EXERCISE: prove it's a ring.

instance : has_zero ℤ1 := ⟨of_nat 0⟩
instance : has_one ℤ1 := ⟨of_nat 1⟩

-- all going fine so far

-- come back to these sorrys
/-
def add : ℤ1 → ℤ1 → ℤ1 
| (of_nat a) (of_nat b) := of_nat (a + b)
| (neg_succ_of_nat a) (of_nat b) := sorry -- this is so horrible. It is 
-- not the "right" way to do it.
| _ _ := sorry

-- troublemaking coecion? Is it?
instance : has_coe ℕ ℤ1 := sorry -- want to put something other than of_nat
-/

-- it looks so awful
-- Let's define addition on CS int via mathematician's int.

end int

-- more experimental int2

constant int2 : Type

notation `ℤ2` := int2

namespace int2

-- I'm going to be defined by my eliminator.
-- At the time of writing this is not dependent and does not cover induction.
-- My plan was to see what I really needed and start small because I need
-- to define add somehow
constant rec
(X : Type)
(F : ℕ → ℕ → X)
(H : ∀ a b c d : ℕ, a + d = b + c → F a b = F c d) :
ℤ2 → X

-- internal outputs of recursors are different. One is dependent
-- and one isn't. Does this matter to me? But I think there is another
-- difference involving quotients somehow.
--#print int.rec
--#print int2.rec

-- They're both the same though, right?

-- ℤ2 is a quotient of ℕ².
-- computer scientists call this map `mk`

constant sub : ℕ × ℕ → ℤ2

-- computer science version
noncomputable def mk : ℕ → ℕ → ℤ2 := function.curry sub

-- give it its proper name
infix ` minus `:65 := mk

-- the quotient map satisfies the quotient axioms.
-- First, the map to the quotient is surjective.
axiom sub_surj : function.surjective sub

-- Second, if two points are in the same equivalance class,
-- their images in the quotient are equal.

axiom probably_has_cs_name : ∀ a b c d : ℕ, a + d = b + c →
  (a minus b) = (c minus d)

open int

noncomputable def canonical1 : ℤ → ℤ2
| (of_nat n) := n minus 0
| (neg_succ_of_nat n) := 0 minus n.succ 
-- enter math mode

-- now let's make ℤ2 into a ring

-- Hendrik Lenstra told me that older works often used bold face Z
noncomputable instance : has_zero ℤ2 := ⟨0 minus 0⟩
@[simp] lemma zero_sub_zero : 0 minus 0 = 0 := rfl

noncomputable def coe : ℕ → ℤ2 :=
λ n, n minus 0
noncomputable def neg : ℕ → ℤ2 :=
λ n, 0 minus n
open function

theorem neg_zero : neg 0 = 0 := by simp [neg]

-- OK we're making the integers into a ring
-- and we've defined the integers as nat squared mod equivalence

-- "choose a random preimage" function. We love the axiom of choice.
noncomputable def cs_name : ℤ2 → ℕ × ℕ :=
λ z, classical.some (sub_surj z)

--z : ℤ2
--⊢ sub (classical.some _) = z
-- theorem it_is_a_lift (z : ℤ2) : (cs_name z).1 minus (cs_name z).2 = z :=
-- begin
--   have h := classical.some_spec (sub_surj z),
--   sorry -- for all I know this is another axiom
-- end

def some_universal_property :=
λ z, classical.some_spec (sub_surj z)

-- not got this straight at all.
-- def add : ℤ2 → ℤ2 → ℤ2 := sorry
--λ a, rec _ (λ r s, sub (a.1 + r) (a.2 + s) : ℕ → ℕ → ℤ2)

end int2

open int2

-- Question. Are ℤ and Z2 the same?
noncomputable def sub (X : Type) (F : ℤ → X) : ℤ2 → X :=
begin
  apply int2.rec,
  swap,
  { intros a b,
    apply F,
    exact (a : ℤ) - b},
  -- hello what's this
  intros a b c d,
  intro h,
  -- it'a a proof obligation
  simp only [],
  suffices : (a : ℤ) - b = c - d,
    rw this,
  -- come on Lean
  have h1 : (a : ℤ) + d = b + c,
    norm_cast, assumption,
  have h2 : (a : ℤ) = (b + c) - d,
    rw ←h1,
  simp,
  rw h2,
  ring,
end

--#check and_congr
--#check congr
noncomputable def internal_eqality_thing (X : Type) (F : ℤ2 → X) : ℤ → X :=
λ z, F $ canonical1 z

-- Z2 and ℤ are the same.

--set_option pp.all true
-- fun exercise
-- noncomputable def canonical : ℤ ≃ ℤ2 := 
-- { to_fun := canonical1,
--   inv_fun := sub _ id,
--   left_inv := begin
--     intro x,
--     unfold sub,
--     dsimp,
--     have h := @int.rec,
--     cases x with n neg_one_minus_n,
--     { sorry},
--     { sorry}
--   end,
--   right_inv := sorry }

  -- I'm going to try doing int with quotients

namespace int3

notation `ℕ²` := ℕ × ℕ

namespace natsquared

notation `first` := prod.fst

notation `second` := prod.snd

@[ext] lemma ext {a b : ℕ²} : first a = first b → second a = second b → a = b :=
by tidy

lemma ext_iff (a b : ℕ²) : a = b ↔ first a = first b ∧ second a = second b :=
⟨λ h, by cases h; simp, λ ⟨p, q⟩, ext p q⟩

instance : has_zero ℕ² := ⟨(0, 0)⟩
@[simp] lemma first_zero : first (0 : ℕ²) = 0 := by refl
@[simp] lemma second_zero : second (0 : ℕ²) = 0 := by refl


def has_one : has_one ℕ² := ⟨(1, 0)⟩
local attribute [instance] has_one

@[simp] lemma first_one : first (1 : ℕ²) = 1 := by refl
@[simp] lemma second_one : second (1 : ℕ²) = 0 := by refl


def r (a b : ℕ²) := first a + second b = second a + first b

instance : has_equiv ℕ² := ⟨r⟩

namespace r
theorem refl (a : ℕ²) : a ≈ a :=
begin
  -- unfold it in your head
  change first a + second a = second a + first a,
  -- if you delete the line above, the line below still works
  apply add_comm,
end

theorem symm (a b : ℕ²) : a ≈ b → b ≈ a :=
begin
  intro hab,
  unfold has_equiv.equiv at *,
  rw [r] at *,
  omega,
end

theorem trans (a b c : ℕ²) : a ≈ b → b ≈ c → a ≈ c :=
begin
  intro hab,
  intro hbc,
  unfold has_equiv.equiv at *,
  rw [r] at *,
  omega,
end

theorem equiv : equivalence r :=
⟨refl, symm, trans⟩

end r

instance : setoid ℕ² :=
{ r := r,
  iseqv := r.equiv }

end natsquared

local attribute [instance] natsquared.has_one -- the canonical 1 is another one!

-- definition of int as quotient type
notation `ℤ3` := quotient natsquared.setoid

-- theorem! It's a ring!

def zero : ℤ3 := ⟦0⟧
instance : has_zero ℤ3 := ⟨zero⟩
@[simp] lemma zero.thing0 : (0 : ℤ3) = ⟦0⟧ := rfl



def one : ℤ3 := ⟦1⟧
instance : has_one ℤ3 := ⟨one⟩
@[simp] lemma one.thing0 : (1 : ℤ3) = ⟦1⟧ := rfl

@[simp] lemma one.first : first (1 : ℕ²) = 1 := by refl
@[simp] lemma one.second : second (1 : ℕ²) = 0 := by refl

open natsquared

@[simp] lemma thing (a b : ℕ²) : a ≈ b ↔ first a + second b = second a + first b := iff.rfl

@[simp] def add (a b : ℤ3) : ℤ3 := quotient.lift_on₂ a b (λ z w,
  ⟦(first z + first w, second z + second w)⟧) begin
  intros,
  simp at *,
  omega,
end

instance : has_add ℤ3 := ⟨add⟩

@[simp] lemma thing2 (a b : ℤ3) : a + b = add a b := rfl 

@[simp] def neg (a : ℤ3) : ℤ3 := quotient.lift_on a (λ b, ⟦(second b, first b)⟧)
begin
  intros,
  simp at *,
  omega
end

instance : has_neg ℤ3 := ⟨neg⟩

@[simp] lemma neg.thing0 (a : ℤ3) : -a = neg a := rfl

instance : add_comm_group ℤ3 :=
{ add := (+),
  add_assoc := 
  begin
    intros a b c,
    apply quotient.induction_on₃ a b c,
    intros,
    simp * at *,
    omega,
  end,    
  zero := 0,
  zero_add :=
  begin
    intro a,
    apply quotient.induction_on a,
    intros,
    simp * at *,
    omega
  end,
  add_zero :=
  begin
    intro a,
    apply quotient.induction_on a,
    intros,
    simp * at *,
    omega
  end,
  neg := has_neg.neg,
  add_left_neg :=
  begin
    intro a,
    apply quotient.induction_on a,
    intros,
    simp * at *,
    omega
  end,
  add_comm :=
  begin
    intros a b,
    apply quotient.induction_on₂ a b,
    intros,
    simp * at *,
    omega
  end
}

theorem useful (p q r s t u v w : ℕ) (h1 : p + u = q + t) (h2 : r + w = s + v) :
  p * r + q * s + (t * w + u * v) = p * s + q * r + (t * v + u * w) :=
begin
  have h3 : (p + u) * r = (q + t) * r,
    rw h1,
  rw [add_mul, add_mul] at h3,
  apply @nat.add_left_cancel (u * r),
  rw [show u * r + (p * r + q * s + (t * w + u * v)) = p * r + u * r + q * s + t * w + u * v, by ring],
  rw h3,
  rw [show q * r + t * r + q * s + t * w + u * v = t * (r + w) + q * s + u * v + q * r, by ring],
  rw [show u * r + (p * s + q * r + (t * v + u * w)) = u * (r + w) + p * s + t * v + q * r, by ring],
  rw [h2, mul_add, mul_add],
  rw [show t * s + t * v + q * s + u * v + q * r = t * s + q * s + t * v + u * v + q * r, by ring],
  --uv cancels tv cancels qr cancels
  suffices : t * s + q * s = (p + u) * s,
    rw this, ring,
  rw h1,
  ring,
end


@[simp] def mul (a b : ℤ3) : ℤ3 := quotient.lift_on₂ a b (λ z w,
  ⟦(first z * first w + second z * second w, first z * second w + second z * first w)⟧) 
  -- why is this well-defined?
begin
  intros,
  simp at *,
  apply useful _ _ _ _ _ _ _ _ a_1 a_2,
end

instance : has_mul ℤ3 := ⟨mul⟩

@[simp] lemma thing3 (a b : ℤ3) : a * b = mul a b := rfl 


-- the proof of every lemma is "just multiply it out"
instance : comm_ring ℤ3 :=
{ mul := (*),
  one := 1,
  mul_assoc := begin
    intros a b c,
    apply quotient.induction_on₃ a b c,
    intros,
    simp,
    ring
  end,
  one_mul := begin
    intro a,
    apply quotient.induction_on a,
    intros,
    simp,
    ring,
  end,
  mul_one := begin
    intro a,
    apply quotient.induction_on a,
    intros,
    simp,
    ring,
  end,
  left_distrib := begin
    intros a b c,
    apply quotient.induction_on₃ a b c,
    intros,
    apply quotient.sound,
    simp,
    ring,
  end,
  right_distrib := begin
    intros a b c,
    apply quotient.induction_on₃ a b c,
    intros,
    apply quotient.sound,
    simp,
    ring,
  end,
  mul_comm := begin
    intros a b,
    apply quotient.induction_on₂ a b,
    intros,
    simp,
    ring,
  end,
  ..int3.add_comm_group
}

-- is this a terrible idea??
example : ℤ ≃+* ℤ3 :=
{ to_fun := coe,
  inv_fun := λ a, quotient.lift_on a (λ b, ((first b : ℕ) : ℤ) - (second b : ℕ)) begin
    intros,
    simp * at *,
    rw sub_eq_sub_iff_add_eq_add,
    norm_cast,
    rw a_2,
    ring,
  end,
  left_inv := begin
    intro x,
    simp,
    sorry,
  end,
  right_inv := begin
    intro x,
    apply quotient.induction_on x,
    intros,
    simp * at *,
    sorry
  end,
  map_mul' := sorry,
  map_add' := sorry }

end int3

namespace int4

-- want amazing Amelia-like definition as localisation of a semiring
-- by a well-behaved equivalence relation.

-- TODO

instance : comm_semiring ℕ := by apply_instance

-- now what do I localise by to get ℤ as, say, an add_comm_group? Can I get a semiring?


end int4

/- question asked to me on Twitter today:
"How easy is it to show that ℤ are the initial objects
for pointed types with a self-equivalence"

  This means:
  if X is a type, if x : X, and if f : X ≃ X is a bijection
  then you want to define a map ℤ → X
  sending n to f^{(n)}(x). 
-/

end experiment