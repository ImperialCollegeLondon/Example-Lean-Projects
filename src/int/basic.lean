-- make all the tactics work
import tactic

-- Let's just use Lean's definition of the naturals and not worry
-- about what they are or how to make them.

import data.nat.basic

-- Let's now experiment 
namespace experiment

/-
An experiment where we try different definitions of the integers. 
-/

--#print int
-- important todo: change all this to Lean 4 syntax
inductive int1 : Type
-- with notation ℤ
| of_nat : ℕ → int1 -- error -- I want this to be a ℤ
-- with notation ↑ [lemme add coercion `ℕ → ℤ` now, named automatically by computer]
| garbage_name : ℕ → int1 -- I will pick up the pieces later

-- 
constant int2 : Type

notation `𝗭` := int2
--notation `ℤ` := int2

namespace int2

-- I'm going to be defined by my eliminator.
constant rec
(X : Type)
(F : ℕ → ℕ → X)
(H : ∀ a b c d : ℕ, a + d = b + c → F a b = F c d) :
int2 → X

-- internal outputs of recursors are completely different
-- #print int.rec
-- #print int2.rec

-- They're both the same though, right?

constant internal_name : ℕ → ℕ → 𝗭

open int

noncomputable def garbage_name : ℤ → 𝗭
| (of_nat n) := internal_name n 0
| (neg_succ_of_nat n) := internal_name 0 n.succ 
-- enter math mode

-- Hendrik Lenstra told me that older works often used bold face 𝗭
noncomputable instance : has_zero 𝗭 := ⟨internal_name 0 0⟩
noncomputable def coe : ℕ → 𝗭 :=
λ n, internal_name n 0
noncomputable def neg : ℕ → 𝗭 :=
λ n, internal_name 0 n
theorem neg_zero : neg 0 = 0 := rfl

end int2

-- Question. Are ℤ and 𝗭 the same?
noncomputable def internal_name (X : Type) (F : ℤ → X) : 𝗭 → X :=
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

noncomputable def internal_eqality_thing (X : Type) (F : 𝗭 → X) : ℤ → X :=
λ z, F $ int2.garbage_name z

-- 𝗭 and ℤ are the same.

-- fun exercise
def canonical : ℤ ≃ 𝗭 :=
{ to_fun := _,
  inv_fun := _,
  left_inv := _,
  right_inv := _ }



end experiment