import data.equiv.basic -- bijections with inverses

open set

/-- Definition of a partition as a collection of disjoint nonempty
  subsets of X whose union is X-/
@[ext] structure partition (X : Type) :=
(C : set (set X))
(Hnonempty : ∀ c ∈ C, c ≠ ∅)
(Hcover : ∀ x, ∃ c ∈ C, x ∈ c)
(Hunique : ∀ c d ∈ C, c ∩ d ≠ ∅ → c = d)

/-- Equivalence class for a binary relation -/
def equivalence_class {X : Type} (R : X → X → Prop) (x : X) := {y : X | R x y}


/-- x is in the equivalence class of x -/
lemma mem_class {X : Type} {R : X → X → Prop} (HR : equivalence R) (x : X) :
  x ∈ equivalence_class R x :=
begin
  sorry
end

/-- There is a bijection between equivalence relations on X and partitions of X -/
example (X : Type) : {R : X → X → Prop // equivalence R} ≃ partition X :=
-- The map in one direction: given a relation, use the set of equivalence classes.
{ to_fun := λ R, {
    C := { S : set X | ∃ x : X, S = equivalence_class R x},
-- I claim that this is a partition.
    Hnonempty := begin -- equiv classes are nonempty
      sorry,
    end,
    Hcover := begin -- they cover
      sorry,
    end,
    Hunique := begin -- and distinct equiv classes are disjoint
      sorry
    end },
-- The map the other way: given a partition, say two elements are related
-- if there's a set in the partition that they both lie in.
  inv_fun := λ P, ⟨λ x y, ∃ c ∈ P.C, x ∈ c ∧ y ∈ c, ⟨
    -- Claim this is an equivalence relation.
    begin -- reflexive
      change ∀ (x : X), ∃ (c : set X) (H : c ∈ P.C), x ∈ c ∧ x ∈ c,
      sorry,
    end,
    begin -- symmetric
      change ∀ (x y : X), (∃ (c : set X) (H : c ∈ P.C), x ∈ c ∧ y ∈ c) →
        (∃ (d : set X) (H : d ∈ P.C), y ∈ d ∧ x ∈ d),
      sorry,
    end,
    begin -- transitive
      change ∀ (x y z : X),
        (∃ (c : set X) (H : c ∈ P.C), x ∈ c ∧ y ∈ c) →
        (∃ (d : set X) (H : d ∈ P.C), y ∈ d ∧ z ∈ d) →
        (∃ (e : set X) (H : e ∈ P.C), x ∈ e ∧ z ∈ e),
      sorry,
    end
  ⟩⟩,
  -- Furthermore, I claim that these two constructions are inverse to each other.
  left_inv := begin
    sorry,
  end,
  -- (in both directions)
  right_inv := begin
    sorry,
  end }
