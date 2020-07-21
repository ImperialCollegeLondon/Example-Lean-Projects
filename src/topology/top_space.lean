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

-- lemma is_open_sInter {𝒞 : set (set X)} (hs : finite 𝒞) : (∀U ∈ 𝒞, is_open U) → is_open (⋂₀ 𝒞) :=
-- finite.induction_on hs (λ _, by rw sInter_empty; exact is_open_univ) $
-- λ a s has hs ih h, by rw sInter_insert; exact
-- is_open_inter _ _ (h _ $ mem_insert _ _) (ih $ λ t, h t ∘ mem_insert_of_mem _)

lemma is_open_sInter {𝒞 : set (set X)} (hs : finite 𝒞) : (∀U ∈ 𝒞, is_open U) → is_open (⋂₀ 𝒞) :=
begin
  apply finite.induction_on hs,
  { intros,
    convert is_open_univ,
    simp},
  intros U 𝒞 hU h𝒞 h1 h2,
  rw sInter_insert,
  apply is_open_inter,
  apply h2, simp,
  apply h1,
  intros U hU,
  apply h2,
  rw mem_insert_iff,
  right,
  assumption,
end

lemma is_open_bInter {I : Type} {F : set I} (hF : finite F) (U : I → set X)
  (hU : ∀ i ∈ F, is_open (U i)) : is_open (⋂ i ∈ F, U i) :=
begin
  rw bInter_eq_Inter,
  show is_open (⋂₀ range (λ x : F, U x)),
  apply is_open_sInter,
  { rw ←image_univ,
    apply finite.image,
    haveI := classical.choice hF,
    exact finite_univ },
  finish
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

-- /-- A set `s` is compact if for every filter `f` that contains `s`,
--     every set of `f` also meets every neighborhood of some `a ∈ s`. -/
-- def compact (s : set α) := ∀f, f ≠ ⊥ → f ≤ 𝓟 s → ∃a∈s, cluster_pt a f

def compact (C : set X) :=
  ∀ (ι : Type) (U : ι → set X) ( hU : ∀ i : ι, is_open (U i)) (hC : C ⊆ ⋃ i, U i),
  ∃ F : set ι, set.finite F ∧ C ⊆ ⋃ (i ∈ F), U i

theorem cts_image_of_compact (f : X → Y) (hf : continuous f) (C : set X) (hC : compact C) :
compact (f '' C) :=
begin
  intros ι U hU hUC,
  let V : ι → set X := λ i, f⁻¹' (U i),
  specialize hC ι V,
  have hV : ∀ i : ι, is_open (V i),
  { intro i,
    apply hf,
    apply hU },
  specialize hC hV,
  specialize hC _, swap,
  { intros x hx,
    rcases hUC ⟨x, hx, rfl⟩ with ⟨_, ⟨i, rfl⟩, hfx⟩,
    rw mem_Union,
    use i,
    exact hfx },
  rcases hC with ⟨F, hF1, hF2⟩,
  use [F, hF1],
  rintro _ ⟨x, hx1, rfl⟩,
  specialize hF2 hx1,
  rw mem_bUnion_iff at hF2 ⊢,
  rcases hF2 with ⟨i, hi, hVi⟩,
  use [i, hi],
  exact hVi
end

lemma open_iff_locally_open (V : set X) :
  is_open V ↔ ∀ x : X, x ∈ V → ∃ U : set X, x ∈ U ∧ is_open U ∧ U ⊆ V :=
begin
  split,
  { intro hV,
    intros x hx,
    use [V, hx, hV] },
  { intro h,
    let 𝒞 : set (set X) := {U : set X | is_open U ∧ U ⊆ V},
    convert is_open_sUnion 𝒞 _,
    { ext x,
      split,
      { intro hx,
        rcases h x hx with ⟨U, h1, h2, h3⟩,
        rw mem_sUnion,
        use U,
        use [h2, h3, h1] },
      { rw mem_sUnion,
        rintro ⟨U, ⟨h, hUV⟩, hxU⟩,
        exact hUV hxU }},
    { rintro U ⟨hU, hUV⟩,
      exact hU }}
end


class t2_space (X : Type) [topological_space X] : Prop :=
(t2 : ∀x y, x ≠ y → ∃U V : set X, is_open U ∧ is_open V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅)

theorem compact_subset_of_Hausdorff_space_is_closed [t2_space X] (C : set X) (hC : compact C) :
is_closed C :=
begin
  unfold is_closed,
  rw open_iff_locally_open,
  intros x hx,
  -- Bartonification
  let I := {VU : set X × set X // x ∈ VU.1 ∧ is_open VU.1 ∧ is_open VU.2 ∧ VU.1 ∩ VU.2 = ∅},
  let U : I → set X := λ VUH, VUH.1.2,
  -- claim : U i open for all i
  have hU1 : ∀ (i : I), is_open (U i),
  { rintros ⟨⟨V, U⟩, _, _, h, _⟩,
    exact h,
  },
  -- claim: U covers C
  have hU : C ⊆ ⋃ i, U i,
  { intros y hy,
    rcases t2_space.t2 x y begin rintros rfl, contradiction end with ⟨V, U, hV, hU, hxV, hyU, hVU⟩,
    rw mem_Union,
    use ⟨(V, U), hxV, hV, hU, hVU⟩,
    exact hyU },
  rcases hC I U hU1 hU with ⟨F, hF, hFC⟩,
  use (⋂ VUH ∈ F, (VUH : I).1.1),
  refine ⟨_, _, _⟩,
  { simp, tauto },
  { apply is_open_bInter hF,
    intros VUH _,
    exact VUH.2.2.1 },
  { rw subset_compl_comm,
    refine subset.trans hFC _,
    simp only [compl_Inter],
    apply Union_subset_Union,
    intro i, 
    apply Union_subset_Union,
    intro hi,
    have := i.2.2.2.2,
    change i.val.snd ⊆ _,
    rw subset_compl_comm,
    rw subset_compl_iff_disjoint,
    assumption },
end





