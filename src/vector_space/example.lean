-- boilerplate -- ignore for now
import tactic
import linear_algebra.finite_dimensional

open vector_space
open finite_dimensional
open submodule

-- Let's prove that if V is a 9-dimensional vector space, and X and Y are 5-dimensional subspaces
-- then X ∩ Y is non-zero

universes u u'

-- mathlib PR
theorem finite_dimensional.dim_sup_add_dim_inf_eq {K : Type u} {V : Type u'} [field K]
  [add_comm_group V] [vector_space K V] [finite_dimensional K V] (s t : submodule K V) :
  findim K ↥(s ⊔ t) + findim K ↥(s ⊓ t) = findim K ↥s + findim K ↥t :=
begin
  have key : dim K ↥(s ⊔ t) + dim K ↥(s ⊓ t) = dim K s + dim K t := dim_sup_add_dim_inf_eq s t,
  repeat { rw ←findim_eq_dim at key },
  norm_cast at key,
  exact key
end

theorem five_inter_five_in_nine_is_nonzero
-- let K be a field
(K : Type) [field K]

-- let V be a finite-dimensional vector space over K
(V : Type) [add_comm_group V] [vector_space K V] [hVfin : finite_dimensional K V]

-- and let's assume V is 9-dimensional
-- (note that dim will return a cardinal! findim returns a natural number)
(hV : findim K V = 9)

-- Let X and Y be subspaces of V
(X Y : subspace K V)

-- and let's assume they're both 5-dimensional
(hX : findim K X = 5)
(hY : findim K Y = 5)

-- then X ∩ Y isn't 0
: X ⊓ Y ≠ ⊥

-- Proof
:= begin
-- I will give a proof which uses *the current state of mathlib*.
-- Note that mathlib can be changed, and other lemmas can be proved,
-- and notation can be created, which will make this proof much more
-- recognisable to undergraduates

-- The key lemma from the library we'll need is that dim(X + Y) + dim(X ∩ Y) = dim(X)+dim(Y)
have key : findim K ↥(X ⊔ Y) + findim K ↥(X ⊓ Y) = findim K X + findim K Y,
  exact finite_dimensional.dim_sup_add_dim_inf_eq X Y,

-- `key` is now a statement about natural numbers. It says dim(X+Y)+dim(X∩Y)=dim(X)+dim(Y)
-- Now let's substitute in the hypothesis that dim(X)=dim(Y)=5
rw hX at key, rw hY at key,

-- so now we know dim(X+Y)+dim(X∩Y)=10.

-- Let's now turn to the proof of the theorem.
-- Let's prove it by contradiction. Assume X∩Y is 0
intro hXY,

-- then we know dim(X+Y) + dim(0) = 10
rw hXY at key,

-- and dim(0) = 0
rw findim_bot at key,

-- so the dimension of X+Y is 10

norm_num at key,

-- But the dimension of a subspace is at most the dimension of a space

have key2 : findim K ↥(X ⊔ Y) ≤ findim K V := findim_le (X ⊔ Y),

-- and now we can get our contradiction by just doing linear arithmetic
linarith,


end

section lattice

variables (K : Type u) [field K] (V : Type u') [add_comm_group V]
  [vector_space K V]


lemma foo.exists : 2 + 2 = 4 := rfl

namespace bar

lemma «exists» : 2 + 2 = 4 := rfl

end bar

#check bar.exists

@[ext] structure subspace' (K : Type u) [field K] (V : Type u') [add_comm_group V]
  [vector_space K V] :=
(carrier : set V)
(zero_mem' : (0 : V) ∈ carrier)
(add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier)
(smul_mem' : ∀ (c:K) {x}, x ∈ carrier → c • x ∈ carrier)

namespace subspace'

variables (W X : subspace' K V)

instance : has_mem V (subspace' K V) := ⟨λ v W, v ∈ W.carrier⟩

variables {K V}

lemma zero_mem : (0 : V) ∈ W := zero_mem' W
lemma add_mem {a b : V} : a ∈ W → b ∈ W → a + b ∈ W := add_mem' W
lemma smul_mem (c : K) {x : V} : x ∈ W → c • x ∈ W := smul_mem' W c

#check add_mem

instance : partial_order (subspace' K V) :=
partial_order.lift (carrier : subspace' K V → set V)
begin
    intros S T h,
    ext, 
    rw h,
end

def inf (W X : subspace' K V) : subspace' K V :=
{ carrier := W.carrier ∩ X.carrier,
  zero_mem' := ⟨W.zero_mem, X.zero_mem⟩,
  add_mem' := λ a b ⟨haW, haX⟩ ⟨hbW, hbX⟩, ⟨W.add_mem haW hbW, X.add_mem haX hbX⟩,
  smul_mem' := λ c a h, ⟨W.smul_mem _ h.1, X.smul_mem _ h.2⟩ }

instance : semilattice_inf (subspace' K V) :=
{ inf := inf,
  inf_le_left := λ W X, set.inter_subset_left _ _,
  inf_le_right := λ W X, set.inter_subset_right _ _,
  le_inf := λ W X Y, set.subset_inter,
  ..subspace'.partial_order}

def sup (W X : subspace' K V) : subspace' K V :=
{ carrier := W.carrier + X.carrier,
  zero_mem' := begin use 0, use 0, use W.zero_mem, use X.zero_mem, simp, end,
  add_mem' := begin intros a b, 
  rintro ⟨w₁, x₁, hw₁, hx₁, rfl⟩,
  rintro ⟨w₂, x₂, hw₂, hx₂, rfl⟩,
  use (w₁ + w₂),
  use (x₁ + x₂),
  use W.add_mem hw₁ hw₂,
  use X.add_mem hx₁ hx₂,
  abel,
  end,
  smul_mem' := begin
    rintros c v ⟨w, x, hw, hx, rfl⟩,
    use c • w, use c • x, 
    use W.smul_mem c hw,
    use X.smul_mem c hx,
    rw smul_add
  end }


instance : semilattice_sup (subspace' K V) :=
{ sup := sup,
  le_sup_left := begin
    intros W X,
    intro w,
    intro hw,
    use w,
    use 0,
    use hw,
    use X.zero_mem,
    simp,
  end,
  le_sup_right := begin
    intros W X,
    intro x,
    intro hx,
    use 0,
    use x,
    use W.zero_mem,
    use hx,
    simp,
  end,  
  sup_le := begin
    intros W X Y,
    intros hWY hXY,
    rintro v ⟨w, x, hw, hx, rfl⟩,
    apply Y.add_mem,
    apply hWY,
    apply hw,
    apply hXY,
    apply hx,
  end,
  ..subspace'.partial_order }

instance : lattice (subspace' K V) :=
{ ..subspace'.semilattice_sup, ..subspace'.semilattice_inf}

-- exercise : distrib_lattice

#check distrib_lattice
-- TODO
-- should library_search find this? Because I don't know how to look for it
-- def partial_order.lift' {α : Type u} {β : Type u'} [partial_order β] (f : α → β)
--     (hf : function.injective f) : partial_order α :=
-- by suggest

#check lattice


end subspace'


end lattice
