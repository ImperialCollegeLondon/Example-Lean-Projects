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
  let 𝒞 : set (set X) := {U, V},
  have h𝒞 : ∀ U ∈ 𝒞, is_open U,
  { intros W hW,
    rcases hW with rfl | ⟨_, _⟩; assumption},
  convert is_open_sUnion 𝒞 h𝒞,
  simp only [sUnion_singleton, sUnion_insert]
end

lemma is_open_empty : is_open (∅ : set X) :=
begin
  let 𝒞 : set (set X) := ∅,
  have h𝒞 : ∀ U ∈ 𝒞, is_open U,
    rintro U ⟨⟩,
  convert is_open_sUnion 𝒞 h𝒞,
  apply sUnion_empty.symm,
end

/-- A set is closed if its complement is open -/
def is_closed (U : set X) : Prop := is_open Uᶜ

end topological_space

open topological_space

variables {X : Type} [topological_space X] {Y : Type} [topological_space Y]

/-- A function between topological spaces is continuous if the preimage
  of every open set is open. -/
def continuous (f : X → Y) := ∀U, is_open U → is_open (f ⁻¹' U)

theorem continuous_id : continuous (id : X → X) :=
begin
  intros U hU,
--  have h1 : U = id '' U := rfl, -- fails
--  have h2 : U = id ⁻¹' U := rfl, -- works
  exact hU,
end

variables {Z : Type} [topological_space Z]

theorem continuous.comp {g : Y → Z} {f : X → Y} (hg : continuous g) (hf : continuous f) :
continuous (g ∘ f) :=
--λ U hU, hf (g⁻¹' U) $ hg _ hU
begin
  intros U hU,
--  change is_open (f⁻¹' (g⁻¹' U)),
  apply hf (g⁻¹' U),
  apply hg,
  assumption,
end
