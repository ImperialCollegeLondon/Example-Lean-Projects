-- topological spaces from first principles.

import tactic

open set

class topological_space (X : Type) :=
(is_open        : set X → Prop)
(is_open_univ   : is_open univ)
(is_open_inter  : ∀ (U V : set X), is_open U → is_open V → is_open (U ∩ V))
(is_open_sUnion : ∀ (𝒞 : set (set X)), (∀U ∈ 𝒞, is_open U) → is_open (⋃₀ 𝒞))

namespace topological_space

variables {X : Type} [topological_space X]

variable {ι : Type}

lemma is_open_Union {f : ι → set X} (h : ∀i, is_open (f i)) : is_open (⋃i, f i) :=
begin
  apply is_open_sUnion,
  intros U,
  intro hU,
  cases hU with i hi,
  dsimp at hi,
  rw ←hi,
  apply h,
end

-- remember `U : set X` means "U is a subset of X", or "U is a set of terms of X"
variables (U V : set X)

lemma is_open_union (h₁ : is_open U) (h₂ : is_open V) : is_open (U ∪ V) :=
begin
  let f : bool → set X := λ b, if b = tt then U else V,
  have hf : ∀ b : bool, is_open (f b),
  { intro b,
    cases b,
      exact h₂,
      exact h₁
  },
  convert is_open_Union hf,
  
end

end topological_space

