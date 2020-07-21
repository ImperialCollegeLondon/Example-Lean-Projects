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

-- a variant of finite intersection of opens is open
lemma is_open_bInter {I : Type} {F : set I} (hf : finite F)
  (U : I → set X) (hU : ∀ (i : I), is_open (U i)) : 
  is_open (⋂ i ∈ F, U i) :=
begin
  rw bInter_eq_Inter,
  show is_open (⋂₀ set.range (λ x : F, U x)),
  apply is_open_sInter,
  { rw ←image_univ,
    apply finite.image,
    haveI := classical.choice hf,
    apply finite_univ },
  finish,
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



-- stream starts at 10am UK time (UTC+2)

-- Goal today


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
  rw mem_compl_iff at hx,
  -- Where do we find such U?
  -- Now is where we use compactness.
  -- We're going to cover C by a bunch of open sets
  -- Where do we get the open sets?
  -- We get them from Hausdorffness
  -- Let's regard x as fixed.
  -- Say y ∈ C (y is moving)
  -- Then x ≠ y because x ∉ C
  -- so by Hausdorff there exists opens U=U(y) and V=V(y)
  -- disjoint, with x ∈ V and y ∈ U
  -- In particular x ∉ U = U(y)
  -- The union of the U(y) covers C because y ∈ C was arbitrary and y ∈ U(y)
  -- So there's a finite subcover, U(y₁), U(y₂)...U(yₙ) of C
  -- Now take the intersection of the corresponding V(y)'s
  -- this is an open nhd of x
  -- and it's disjoint from the union of the U(y)'s so it's disjoint from C
  -- This V works!

  -- "issue" with the maths proof -- uses the axiom of choice!
  -- Grateful to Reid Barton and Andrej Bauer who independently showed
  -- me a "AC removal principle" -- which makes proofs look (a) a bit slicker
  -- and (b) a bit harder to remember (possibly).

  -- AC removal principle says "DON'T CHOOSE! USE ALL THE CHOICES!"

  -- in our actual proof we'll define a slightly different cover

  -- I is the set of pairs (V,U) of open subsets of X, with
  -- x ∈ V, and U ∩ V empty
  let I := {VU : set X × set X //
    x ∈ VU.1 ∧ is_open VU.1 ∧ is_open VU.2 ∧ VU.1 ∩ VU.2 = ∅},
  -- We want to consider all the U's coming from pairs (V,U) in I
  let U : I → set X := λ VUH, VUH.1.2, -- send (V,U) to U
  -- My claim is that as i ranges through I, the U(i) are an open cover
  -- Let's first prove they're all open
  have hU1 : ∀ i : I, is_open (U i),
  { rintro ⟨⟨V, U⟩, _, _, h, _⟩,
    exact h },
  -- now let's prove they cover C
  have hU2 : C ⊆ ⋃ i, U i,
  { intros y hy,
    /-
    def hausdorff (X : Type) [topological_space X] : Prop :=
    ∀ x y : X, x ≠ y → ∃ U V : set X, is_open U ∧ is_open V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅
    -/
    have hxy : x ≠ y,
    { rintro rfl,
      contradiction },
    -- now use that X is Hausdorff
    rcases hX x y hxy with ⟨V, U, hV, hU, hxV, hyU, hUV⟩,
    rw mem_Union,
    -- now let's give the term of type I
    use ⟨(V, U), ⟨hxV, hV, hU, hUV⟩⟩,
    exact hyU },
  /-
  def compact (C : set X) : Prop :=
  ∀ (ι : Type) (U : ι → set X) (hi : ∀ i : ι, is_open (U i)) (hC : C ⊆ ⋃i, U i),
  ∃ F : set ι, finite F ∧ C ⊆ ⋃ i ∈ F, U i
  -/
  specialize hC I U hU1 hU2,
  rcases hC with ⟨F, hF, hFC⟩,
  -- now we have our finite subcover
  -- now let's create the open nhd of x
  let W := ⋂ i ∈ F, (i : I).1.1,
  use W,
  refine ⟨_, _, _⟩,
  { show x ∈ ⋂ (i : I) (H : i ∈ F), i.val.fst,
    rw mem_bInter_iff,
    rintro ⟨⟨V, U⟩, hxV, hV, hU, hUV⟩,
    intro hi,
    use hxV },
  { -- we're missing a lemma here
    -- need a different kind of "finite intersection of opens is open"
    show is_open (⋂ (i : I) (H : i ∈ F), i.val.fst),
    apply is_open_bInter hF,
    rintro ⟨⟨V, U⟩, hxV, hV, hU, hUV⟩,
    exact hV,
  },
  { rw subset_compl_comm,
    rw compl_Inter,
    refine set.subset.trans hFC _,
    apply Union_subset_Union,
    intro i,
    rw compl_Inter,
    apply Union_subset_Union,
    rintro hi,
    rcases i with ⟨⟨V, U⟩, hxV, hV, hU, hUV⟩,
    show U ⊆ Vᶜ,
    rw subset_compl_iff_disjoint,
    rw inter_comm,
    exact hUV },
end




