import data.equiv.basic -- bijections with inverses
import tactic -- we want to use tactics

open set

/-- Definition of a partition as a collection of disjoint nonempty
  subsets of X whose union is X-/
@[ext] structure partition (X : Type) :=
(C : set (set X))
(Hnonempty : ∀ c ∈ C, c ≠ ∅)
(Hcover : ∀ x, ∃ c ∈ C, x ∈ c)
(Hunique : ∀ c d ∈ C, c ∩ d ≠ ∅ → c = d)

namespace partition

variables (X : Type) (P : partition X) (x : X)

lemma block_eq (B : set X) (hB : B ∈ P.C) (hx : x ∈ B) :
B = {y : X | ∃ (c : set X), c ∈ P.C ∧ x ∈ c ∧ y ∈ c} :=
begin
      ext y,
      dsimp,
      split,
      { intro hy,
        use B,
        use hB,
        use hx,
        use hy},
      { rintro ⟨C, hC, hCx, hCy⟩,
        convert hCy,
        apply P.Hunique B C hB hC,
        rw ne_empty_iff_nonempty,
        use x,
        exact ⟨hx, hCx⟩,
      },
end

end partition


/-- Equivalence class for a binary relation -/
def equivalence_class {X : Type} (R : X → X → Prop) (x : X) := {y : X | R x y}

variables {X : Type} (R : X → X → Prop)

/-- x is in the equivalence class of x -/
lemma mem_class (HR : equivalence R) (x : X) :
  x ∈ equivalence_class R x := HR.1 x

lemma subset_of_rel (HR : equivalence R) (x y : X) (hxy : R x y) :
  equivalence_class R y ⊆ equivalence_class R x :=
begin
  intro z,
  intro hz,
  change R y z at hz,
  change R x z,
  exact HR.2.2 hxy hz,
end

/-- There is a bijection between equivalence relations on X and partitions of X -/
example (X : Type) : {R : X → X → Prop // equivalence R} ≃ partition X :=
-- The map in one direction: given a relation, use the set of equivalence classes.
{ to_fun := λ R,
-- R is an equivalence relation
-- and we need to make a partition
{
    C := { S : set X | ∃ x : X, S = equivalence_class R.1 x},
-- I claim that this is a partition.
    Hnonempty := begin -- equiv classes are nonempty
      rintro _ ⟨x, rfl⟩,
      rw ne_empty_iff_nonempty,
      use x,
      exact mem_class R.1 R.2 x,
    end,
    Hcover := begin -- they cover
      intro x,
      use equivalence_class R x,
      dsimp,
      split,
        use x,
      exact mem_class R.1 R.2 x,
    end,
    Hunique := begin -- and distinct equiv classes are disjoint
      intros b1 b2,
      rintro ⟨x, rfl⟩,
      rintro ⟨y, rfl⟩,
      intro h,
      rw ne_empty_iff_nonempty at h,
      cases h with z hz,
      cases hz with hxz hyz,
      change R.1 x z at hxz,
      change R.1 y z at hyz,
      apply set.subset.antisymm;
      apply subset_of_rel R.1 R.2;
      rcases R.2 with ⟨ref, sym, tra⟩,
      apply tra hyz,
      exact sym hxz,
      apply tra hxz,
      exact sym hyz
    end
},
-- The map the other way: given a partition, say two elements are related
-- if there's a set in the partition that they both lie in.
  inv_fun := λ P, ⟨λ x y, ∃ c ∈ P.C, x ∈ c ∧ y ∈ c, ⟨
    -- Claim this is an equivalence relation.
    begin -- reflexive
      change ∀ (x : X), ∃ (c : set X) (H : c ∈ P.C), x ∈ c ∧ x ∈ c,
      intro x,
      rcases P.Hcover x with ⟨B, hB, hx⟩,
      use B,
      use hB,
      cc,
    end,
    begin -- symmetric
      change ∀ (x y : X), (∃ (c : set X) (H : c ∈ P.C), x ∈ c ∧ y ∈ c) →
        (∃ (d : set X) (H : d ∈ P.C), y ∈ d ∧ x ∈ d),
      intros x y,
      rintro ⟨B, hB, hx, hy⟩,
      use [B, hB, hy, hx],
      -- tidy bug
    end,
    begin -- transitive
      change ∀ (x y z : X),
        (∃ (c : set X) (H : c ∈ P.C), x ∈ c ∧ y ∈ c) →
        (∃ (d : set X) (H : d ∈ P.C), y ∈ d ∧ z ∈ d) →
        (∃ (e : set X) (H : e ∈ P.C), x ∈ e ∧ z ∈ e),
      intros x y z,
      rintro ⟨B, hB, hBx, hBy⟩, 
      rintro ⟨C, hC, hCy, hCz⟩,
      use [B, hB],
      use hBx,
      convert hCz,
      apply P.Hunique B C hB hC,
      rw ne_empty_iff_nonempty,
      use y,
      split; assumption
    end
  ⟩⟩,
  -- Furthermore, I claim that these two constructions are inverse to each other.
  left_inv := begin
    rintro ⟨R, ref, sym, tra⟩,
    ext x y,
    dsimp,
    split,
    { rintro ⟨_, ⟨z, rfl⟩, hzx, hzy⟩,
      unfold equivalence_class at *,
      apply tra,
      apply sym,
      exact hzx,
      exact hzy},
    { intro hxy,
      use equivalence_class R x,
      use x,
      use ref x,
      exact hxy},
  end,
  -- (in both directions)
  right_inv := begin
    intro P,
    ext B,
    simp only [exists_prop, mem_set_of_eq],
    split,
    { rintro ⟨x, rfl⟩,
      dsimp [equivalence_class],
      rcases P.Hcover x with ⟨B, hB, hx⟩,
      suffices : {y : X | ∃ (c : set X), c ∈ P.C ∧ x ∈ c ∧ y ∈ c} = B,
        rw this,
        assumption,
      rw partition.block_eq X P x B hB hx
    },
    { intro hB,
      let h := P.Hnonempty B hB,
      rw ne_empty_iff_nonempty at h,
      cases h with x hx,
      use x,
      rw partition.block_eq X P x B hB hx,
      refl}
  end }
