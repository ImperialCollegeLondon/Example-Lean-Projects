-- topological spaces from first princples!

-- Turns out there's quite a lot to it, but it's all straightforward

-- I'll start in a second

import tactic

-- remember : in Lean, `set X` means the type of subsets of X
-- or, the type of "sets of elements of X"

open set

/-- The definition of a topological space -/
class topological_space (X : Type) :=
 -- some subsets of X are called "open sets"
(is_open : set X → Prop)
 -- X itself is open
(is_open_univ : is_open univ)
 -- intersection of two open sets is open
(is_open_inter : ∀ U V : set X, is_open U → is_open V → is_open (U ∩ V))
-- arbitrary union of open sets is open
(is_open_sUnion : ∀ (𝒞 : set (set X)), (∀ U ∈ 𝒞, is_open U) → is_open (⋃₀ 𝒞))

-- what is an "arbitrary union of open sets"?
-- I've set it up as a set of open sets
-- but you might have an "indexed family of open sets"
-- ie some type ι, and for all  i ∈ ι an open set U_i
-- and you want ⋃ U_i open

namespace topological_space

-- let X be a topological space

variables {X : Type} [topological_space X]

-- let's do indexed unions

lemma is_open_Union {ι : Type} {f : ι → set X} (hf : ∀ i : ι, is_open (f i)) :
  is_open (⋃ i, f i) :=
begin
  apply is_open_sUnion,
  intros U hU,
  cases hU with i hi,
  dsimp at hi,
  rw ←hi,
  apply hf,
end

-- empty set is open
lemma is_open_empty : is_open (∅ : set X) :=
begin
  let 𝒞 : set (set X) := ∅,
  have h𝒞 : ∀ U ∈ 𝒞, is_open U,
  { rintro U ⟨⟩,
  },
  convert is_open_sUnion 𝒞 h𝒞,
  rw sUnion_empty,
end

-- finite intersection of open sets is open
-- proof by induction on size of finite set
lemma is_open_sInter {𝒞 : set (set X)} (h𝒞 : finite 𝒞) :
  (∀ U ∈ 𝒞, is_open U) → is_open ⋂₀ 𝒞 :=
begin
  apply finite.induction_on h𝒞,
  { -- base case,
    intros,
    convert is_open_univ,
    rw sInter_empty },
  { -- inductive step
    -- going to use is_open_inter
    intro U,
    intro 𝒞,
    intro hU𝒞,
    intro h𝒞,
    intro h𝒞2,
    -- h says "assume both U and every element of 𝒞 is open"
    -- insert U 𝒞 means {U} ∪ 𝒞
    intro h,
    rw sInter_insert,
    apply is_open_inter,
    { apply h,
      simp },
    { apply h𝒞2,
      intros U hU,
      apply h,
      simp [hU] }},
end

def is_closed (C : set X) : Prop := is_open Cᶜ

@[simp] lemma is_closed_iff (C : set X) : is_closed C ↔ is_open Cᶜ := iff.rfl

-- clearly could spend all day proving facts about closed sets now

lemma is_closed_empty : is_closed (∅ : set X) :=
begin
  simp [is_open_univ],
end

end topological_space

-- next : continuous functions

open topological_space

variables {X : Type} [topological_space X]
  {Y : Type} [topological_space Y]

/-- a function X → Y between topological spaces is continuous if the
  preimage of every open set is open -/
def continuous (f : X → Y) : Prop :=
∀ U, is_open U → is_open (f⁻¹' U)

theorem continuous_id : continuous (id : X → X) :=
begin
  intro U,
  intro hU,
  -- interesting question
  -- clearly id⁻¹' U = U
  -- But this is true *by definition*?
  -- another interesting question
  -- clearly id'' U = U (pushforward)
  -- but is this true *by definition*?
  -- THESE QUESTIONS ARE NOT MATHEMATICAL QUESTIONS
  -- They depend not on the specification, but on the *implementation*
--   have h1 : U = id '' U,
--   { --refl, -- fails!
--     -- not true by definition
--     ext x,
--     split,
--       intro h,
--       unfold set.image,
--       use x, -- this is why it's not true by definition
--       split, assumption, refl,
--       rintro ⟨y, hy1, rfl⟩,
--       exact hy1,
--   },
--   have h2 : U = id⁻¹' U, -- true by definition
--     refl,
  exact hU,
end

variables {Z : Type} [topological_space Z]

theorem continuous.comp {f : X → Y} {g : Y → Z} (hf : continuous f)
  (hg : continuous g) : continuous (g ∘ f) :=
begin
  intro U,
  intro hU,
  change is_open ((g ∘ f)⁻¹' U),
  change is_open (f⁻¹' (g⁻¹' U)),
  -- proving it backwards
  apply hf,
  apply hg,
  exact hU
end

-- term mode proof (same proof!)
theorem continuous.comp' {f : X → Y} {g : Y → Z} (hf : continuous f)
  (hg : continuous g) : continuous (g ∘ f) :=
λ U hU, hf (g⁻¹' U) (hg _ hU)

/-- a subset C of a top space X is compact if every open cover has a finite subcover -/
def compact (C : set X) : Prop :=
∀ 𝒞 : set (set X), (∀ U ∈ 𝒞, is_open U) → (C ⊆ ⋃₀ 𝒞) →
  ∃ F : set (set X), F ⊆ 𝒞 ∧ finite F ∧ C ⊆ ⋃₀ 𝒞

def hausdorff (X : Type) [topological_space X] : Prop :=
∀ x y : X, x ≠ y → ∃ U V : set X, is_open U ∧ is_open V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅

-- theorem (finish this next time)
-- continuous image of a compact set is compact
theorem compact_map {f : X → Y} (hf : continuous f) {C : set X} (hC : compact C) :
  compact (f '' C) :=
begin
  intro 𝒞,
  intro h𝒞,
  intro hC𝒞,
  unfold compact at hC,
  --have test := (f⁻¹' : set Y → set X),
  -- want 𝒟 to be a collectio of subsets of X
  -- given by pulling back all the elements of Y.
  set 𝒟 := (f ⁻¹' : set Y → set X)'',
  sorry
end

theorem is_closed_of_compact (hX : hausdorff X) {C : set X} (hC : compact C) : is_closed C :=
begin
  sorry
end


