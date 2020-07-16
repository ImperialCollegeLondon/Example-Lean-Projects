-- topological spaces from first princples!

-- Turns out there's quite a lot to it, but it's all straightforward

-- I'll start on the hour. I'll do a brief review of last week
-- (the below file, 
-- https://github.com/ImperialCollegeLondon/Example-Lean-Projects/blob/master/src/topology/twitch.lean
-- and then I'll start on the proof that the continuous image of compact is compact.

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
  ∀ (ι : Type) (U : ι → set X) (hi : ∀ i : ι, is_open (U i)) (hC : C ⊆ ⋃i, U i),
  ∃ F : set ι, finite F ∧ C ⊆ ⋃ i ∈ F, U i

-- this definition seems to me to be easier to work with

def hausdorff (X : Type) [topological_space X] : Prop :=
∀ x y : X, x ≠ y → ∃ U V : set X, is_open U ∧ is_open V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅

-- Theorem: continuous image of a compact set is compact
theorem compact_map {f : X → Y} (hf : continuous f) {C : set X} (hC : compact C) :
  compact (f '' C) :=
begin
  -- suffices to prove that if f(C) is covered by open sets, it has a 
  -- finite subcover
  intros I U hU hUC,
  -- hUC : f(C) ⊆ ⋃_{i ∈ I} Uᵢ
  -- So say we've covered f(C) by open sets
  -- Then C has a cover by open sets, namely Vᵢ := f⁻¹(Uᵢ),
  let V : I → set X := λ i, f⁻¹' (U i),
  -- Let's check that all the Vᵢ are open
  have hV : ∀ i : I, is_open (V i),
  { intro i,
    apply hf,
    apply hU },
  -- Let's check that the Vᵢ cover C
  have hVC : C ⊆ ⋃ i, V i,
  { -- say x ∈ C,
    intro x,
    intro hx,
    -- then f(x) ∈ ⋃_i Uᵢ
    have hx2 : f x ∈ ⋃ i, U i,
      apply hUC,
      use [x, hx],
    -- f(x) ∈ ⋃_i Uᵢ, so ∃ i s.t. f(x) ∈ Uᵢ
    rw mem_Union at hx2 ⊢,
    cases hx2 with i hi,
    use i,
    exact hi },
  -- but C is compact
  specialize hC I V hV hVC,
  -- so there exists a finite subcover of Vᵢ,
  rcases hC with ⟨F, hF, hFC⟩,
  -- I claim that corresponding Uᵢ will work
  use [F, hF],
  -- Let's check they cover f(C),
  rintros _ ⟨x, hx1, rfl⟩,
  specialize hFC hx1,
  rw mem_bUnion_iff at hFC ⊢,
  exact hFC,
  -- They do, so the cover of f(C) had a finite subcover :D
end

-- To prove that a compact subspace of a Hausdorff space is closed,
-- we need the fact that a "locally open" set is open!

-- So let's prove that first

lemma open_iff_locally_open (V : set X) :
  is_open V ↔ ∀ x : X, x ∈ V → ∃ U : set X, x ∈ U ∧ is_open U ∧ U ⊆ V :=
⟨λ hV x hx, ⟨V, hx, hV, subset.refl _⟩, λ h, begin
  let 𝒞 : set (set X) := {U : set X | is_open U ∧ U ⊆ V},
    -- 𝒞 doesn't just contain the neighbourhoods of x for each x ∈ V
    -- 𝒞 contains more sets, e.g. the empty set!
    -- Clearly every set in 𝒞 is open, so their union is open
    convert is_open_sUnion 𝒞 _,
    swap,
    { intros U H, cases H, assumption},
    -- It suffices to prove that V is the union of the elements of 𝒞
    { ext x,
      split,
      -- let's prove inclusions in both directions
      { intro hx,
        rcases h x hx with ⟨U, hU1, hU2, hU3⟩,
        rw mem_sUnion,
        use U,
        use hU2,
        exact hU3,
        exact hU1 },
      { -- easy way
        intro hx,
        rw mem_sUnion at hx,
        rcases hx with ⟨U, hUC, hxU⟩,
        cases hUC with h1 h2,
        apply h2 hxU }}
end⟩
-- #exit
-- begin
--   split,
--   { -- This way is easy. Say V is open.
--     intro hV,
--     -- say x ∈ V
--     intros x hx,
--     -- Want an open neighbourhood of x contained in V
--     -- let's just use V :-)
--     use V,
--     use hx,
--     use hV }, -- last goal V ⊆ V closed automatically by `refl`,
--   { intro h,
--     -- Reid Barton trick!
--     let 𝒞 : set (set X) := {U : set X | is_open U ∧ U ⊆ V},
--     -- 𝒞 doesn't just contain the neighbourhoods of x for each x ∈ V
--     -- 𝒞 contains more sets, e.g. the empty set!
--     -- Clearly every set in 𝒞 is open, so their union is open
--     convert is_open_sUnion 𝒞 _,
--     swap,
--     { tidy },
--     -- It suffices to prove that V is the union of the elements of 𝒞
--     { ext x,
--       split,
--       -- let's prove inclusions in both directions
--       { intro hx,
--         rcases h x hx with ⟨U, hU1, hU2, hU3⟩,
--         rw mem_sUnion,
--         use U,
--         use hU2,
--         exact hU3,
--         exact hU1 },
--       { -- easy way
--         intro hx,
--         rw mem_sUnion at hx,
--         rcases hx with ⟨U, hUC, hxU⟩,
--         cases hUC with h1 h2,
--         apply h2 hxU }}}
-- end

-- prove this next Tues
theorem is_closed_of_compact (hX : hausdorff X) {C : set X} (hC : compact C) : is_closed C :=
begin
  unfold is_closed,
  -- let's start with the maths proof
  -- We're going to prove that Cᶜ is open by showing it's locally open
  -- Let x ∈ Cᶜ i.e. x : X and x ∉ C
  -- If we can find an open subset U ⊆ Cᶜ with x ∈ U then we're done
  -- by the previous lemma
  rw open_iff_locally_open,
  intros x hx,
  -- Where do we find such U?
  -- Now is where we use compactness.
  -- We're going to cover C by a bunch of open sets
  -- Where do we get the open sets?
  -- We get them from Hausdorffness
  -- Say y ∈ C
  -- Then x ≠ y because x ∉ C
  -- so by Hausdorff, x ∈ V₁ and y ∈ V₂ and V₁ ∩ V₂ = ∅
  -- In particular x ∉ V₂ = V₂(y)
  -- The union of the V₂(y) covers C because y ∈ C was arbitrary and y ∈ V₂(y)
  -- So there's a finite subcover
  -- Now take the intersection of the corresponding V₁(y)
  -- finite intersection of open sets is open
  -- and completely misses C
  
end


