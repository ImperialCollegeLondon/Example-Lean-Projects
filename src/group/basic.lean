import tactic

/-
Making group theory in a theorem prover
-/

namespace mygroup

-- A group needs multiplication, inverse, identity
class group (G : Type) extends has_mul G, has_inv G, has_one G :=
-- axioms go here
(mul_assoc : ∀ (a b c : G), (a * b) * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)


/-
non-example of a group: G is any non-empty set, 1 is any element,
and define g * h = h, g⁻¹ = 1 for all g

NOT A GROUP because mul_left_inv fails
-/

namespace group

attribute [simp] mul_left_inv one_mul

variables {G : Type} [group G]

-- Students at my uni also learn that mul_one : a * 1 = a and mul_right_inv are axioms
-- let's prove them!

-- let's start by showing you can cancel on the left


lemma mul_left_cancel (a b c : G) (H : a * b = a * c) : b = c :=
calc b = 1 * b         : by rw one_mul
...    = (a⁻¹ * a) * b : by rw mul_left_inv
...    = a⁻¹ * (a * b) : by rw mul_assoc
...    = a⁻¹ * (a * c) : by rw H
...    = (a⁻¹ * a) * c : by rw mul_assoc
...    = 1 * c         : by rw mul_left_inv
...    = c             : by rw one_mul

-- that proof is nice to look at

lemma mul_left_cancel' (a b c : G) (H : a * b = a * c) : b = c :=
by rw [←one_mul b, ←mul_left_inv a, mul_assoc, H, ←mul_assoc, mul_left_inv, one_mul]

lemma mul_eq_of_eq_inv_mul {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
begin
  apply mul_left_cancel a⁻¹,
  rw ←mul_assoc,
  -- ⊢ (a⁻¹ * a) * x = a⁻¹ * y
  -- know : x = a⁻¹ * y
  -- simplifier can now do the rest
  simp [h],
end

@[simp] lemma mul_one (a : G) : a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  simp,
end

-- term mode proof
lemma mul_one' (a : G) : a * 1 = a :=
mul_eq_of_eq_inv_mul $ by simp

@[simp] lemma mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  simp,
end

@[simp] lemma inv_mul_right_cancel (a b : G) : (b * a⁻¹) * a = b := by simp [mul_assoc]
@[simp] lemma mul_inv_right_cancel (a b : G) : (b * a) * a⁻¹ = b := by simp [mul_assoc]
@[simp] lemma inv_mul_left_cancel (a b : G) : a⁻¹ * (a * b) = b := by simp [←mul_assoc]

example (a b c : G) : a * a⁻¹ * a⁻¹ * a = 1 := by simp
example (a b c : G) : a * a⁻¹ * b * a * a⁻¹ = b := by simp
example (a b c : G) : a * a⁻¹ * b * c * c⁻¹ * b⁻¹ = 1 := by simp
example (a b c : G) : b * c * c⁻¹ * b⁻¹ * a * a⁻¹ = 1 := by simp


@[simp] lemma mul_eq_iff_eq_inv_mul {a x y : G} : x = a⁻¹ * y ↔ a * x = y :=
begin
  split,
  { apply mul_eq_of_eq_inv_mul},
  { intro h,
    simp [h.symm]}
end

@[simp] lemma mul_eq_iff_eq_inv_mul' {a x y : G} : a⁻¹ * y = x ↔ y = a * x :=
by simp [eq_comm]

@[simp] lemma mul_left_cancel_iff (a b c : G) : a * b = a * c ↔ b = c :=
begin
  split,
  { apply mul_left_cancel},
  { rintro rfl, refl}
end

example (a b c : G) : a * b * c * (c⁻¹ * a * a⁻¹) = a * c * c⁻¹ * b := by simp

-- this is exactly what the simplifier is good at

end group

structure subgroup (G : Type) [group G] :=
-- carrier is the name of the subset
(carrier : set G)
(one_mem' : (1 : G) ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)

namespace subgroup

variables {G : Type} [group G] (H J K : subgroup G) (a b c : G)

-- want to be able to say a ∈ H

instance : has_mem G (subgroup G) := ⟨λ g H, g ∈ H.carrier⟩

-- want to talk about H₁ ≤ H₂ (meanning H₁ ⊆ H₂)

-- "subgroups of a group form a lattice"

instance : has_le (subgroup G) := ⟨λ S T, S.carrier ⊆ T.carrier⟩

lemma le_def (H J : subgroup G) : H.carrier ≤ J.carrier ↔ H ≤ J := iff.rfl

@[ext] theorem ext {H J : subgroup G} (h : ∀ (x : G), x ∈ H ↔ x ∈ J) : H = J :=
begin
  cases H,
  cases J,
  suffices : H_carrier = J_carrier,
    simpa,
  ext x,
  exact h x,
end

lemma mem_coe {g : G} : g ∈ H.carrier ↔ g ∈ H := iff.rfl

theorem one_mem : (1 : G) ∈ H := H.one_mem'
theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H := subgroup.mul_mem' H
theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H := subgroup.inv_mem' H

-- definition in Lean because `subgroup` contains data
/-- "Theorem" : intersection of two subgroups is a subgroup -/
def inf (H K : subgroup G) : subgroup G :=
{ carrier := H.carrier ∩ K.carrier,
  one_mem' := ⟨H.one_mem', K.one_mem'⟩,
  inv_mem' := λ x ⟨hH, hK⟩, ⟨H.inv_mem' hH, K.inv_mem' hK⟩,
  mul_mem' := λ x y ⟨hxH, hxK⟩ ⟨hyH, hyK⟩, ⟨H.mul_mem' hxH hyH, K.mul_mem' hxK hyK⟩ }

open set

-- intersection of any number of subgroups is a subgroup
def Infi (ι : Type) (H : ι → subgroup G) : subgroup G :=
{ carrier := ⋂(i : ι), (H i).carrier,
  one_mem' := begin
    rw mem_Inter,
    intro i,
    apply subgroup.one_mem',
  end,
  inv_mem' := begin
    intro x,
    intro hx,
    rw mem_Inter at hx ⊢,
    intro i,
    apply subgroup.inv_mem',
    tauto!,
  end,
  mul_mem' := begin
    intros x y hx hy,
    rw mem_Inter at *,
    intro i,
    apply subgroup.mul_mem';
    tauto!,
  end }

-- why is H bug not fixed?

def Inf (S : set (subgroup G)) : subgroup G :=
{ carrier := -- ⋂₀ {H.carrier | H ∈ S},
             -- ⋂₀ {T : set G | ∃ J ∈ S, T = subgroup.carrier J},
             Inf (subgroup.carrier '' S),
  one_mem' := begin
    rw mem_sInter,
    rintro t ⟨⟨H_w_carrier, H_w_one_mem', H_w_inv_mem', H_w_mul_mem'⟩, H_h_w, rfl⟩,
    apply subgroup.one_mem',
  end,
  inv_mem' := begin
    intros x hx,
    rw mem_sInter at hx ⊢,
    rintro t ⟨H, H_h_w, rfl⟩,
    apply H.inv_mem',
    apply hx,
    use H,
    tauto!,
  end,
  mul_mem' :=  begin
    intros x y hx hy,
    rw mem_sInter at hx hy ⊢,
    rintro t ⟨H, hH, rfl⟩,
    apply H.mul_mem',
    apply hx, use H, tauto,
    apply hy, use H, tauto,
  end }

instance : has_Inf (subgroup G) := ⟨Inf⟩

-- goal -- make subgroups of a group into a complete lattice
/-
complete_lattice_of_Inf :
  Π (α : Type u_1) [H1 : partial_order α] [H2 : has_Inf α],
    (∀ (s : set α), is_glb s (Inf s)) → complete_lattice α
-/

instance : partial_order (subgroup G) :=
{ le := (≤),
  le_refl := by tidy,
  le_trans := by tidy,
  le_antisymm := by tidy }

instance : complete_lattice (subgroup G) := complete_lattice_of_Inf _ begin
  intro S,
    apply @is_glb.of_image _ _ _ _ subgroup.carrier,
  intros, refl,
  apply is_glb_Inf,
end

-- adjoint functor to carrier functor is the span functor
-- from subsets to subgroups
def span (S : set G) : subgroup G := Inf {H : subgroup G | S ⊆ H.carrier}

lemma monotone_carrier : monotone (subgroup.carrier : subgroup G → set G) :=
λ H J, id

lemma monotone_span : monotone (span : set G → subgroup G) :=
λ S T h, Inf_le_Inf $ λ H hH x hx, hH $ h hx

lemma subset_span (S : set G) : S ≤ (span S).carrier :=
begin
  rintro x hx _ ⟨H, hH, rfl⟩,
  exact hH hx,
end

lemma span_subgroup (H : subgroup G) : span H.carrier = H :=
begin
  ext,
  split,
  { intro hx,
    unfold span at hx,
    replace hx := mem_sInter.1 hx,
    apply hx,
    use H,
    simp,
    tauto! },
  { intro h,
    apply subset_span,
    exact h},
end

-- the functors are adjoint
def gi_subgroup : galois_insertion span (@subgroup.carrier G _) :=
galois_insertion.monotone_intro monotone_carrier monotone_span subset_span span_subgroup

-- claim : if g ∈ G then the map ℤ → G, n ↦ g^n is a group hom. Duh.

/-- definition of map sending g, n to gⁿ , n ∈ ℕ -/
def pow (g : G) : ℕ → G
| 0 := 1
| (n+1) := pow n * g -- $6,000,000 : do I do that or g * pow n ??

-- #check nat.iterate

--example {α : Type} (h : α ≃ α) : ℤ → α ≃ α := by hint

def pow' (g : G) (n : ℕ) := ((*) g)^[n] 1

open int

def int.iterate {α : Type} (h : α ≃ α) : ℤ → α → α
| (of_nat n) := h^[n]
| (neg_succ_of_nat n) := h.symm^[n+1]

notation f`^⦃`:91 n`⦄`:91 := int.iterate f n

namespace int.iterate

variables {α : Type} (h : α ≃ α)

--example (a b : ℕ) : h^[a+b] = (h^[a]) ∘ (h^[b]) := sorry -- brackets needed

@[simp] lemma zero : h^⦃0⦄ = id := rfl
@[simp] lemma one : h^⦃1⦄ = h := by funext; refl  --rfl --funext $ λ x, rfl
@[simp] lemma neg_one : h^⦃-1⦄ = h.symm := funext $ λ x, rfl -- :-)

lemma neg (a : ℤ) : h^⦃-a⦄ = h.symm^⦃a⦄ :=
begin
  cases a,
  cases a,
  ext, refl,
  ext, refl,
  ext, refl,
end

example (i : ℕ) : -[1+ i] = -((i : ℤ) + 1) := by exact neg_succ_of_nat_eq i

lemma add_one (a : ℤ) : h^⦃a+1⦄ = h^⦃a⦄ ∘ h :=
begin
  cases a with i i,
  { refl},
  { suffices :  h^⦃(-↑i)⦄ = h^⦃-(i + 1)⦄ ∘ h,
      convert this, rw neg_succ_of_nat_eq, ring,
    rw neg,
    rw neg,
    ext,
    norm_cast,
    have : h.symm^⦃↑i⦄ ∘ h.symm = h.symm^⦃↑(i + 1)⦄,
      refl,
    rw ←this,
    simp},
end

lemma sub_one (a : ℤ) : h^⦃a-1⦄ = h^⦃a⦄ ∘ h.symm :=
begin
  rw ←neg_one,
  rw ←h.symm_symm,
  rw ←neg,
  rw (show -(a-1)=-a+1, by ring),
  rw add_one,
  simp [neg],
end


lemma add (a b : ℤ) : h^⦃a + b⦄ = h^⦃a⦄ ∘ h^⦃b⦄ :=
begin
  apply int.induction_on b,
  {simp},
  { intro i,
    intro useful,
    rw ←add_assoc,
    rw add_one,
    rw useful,
    rw add_one,
  },
  { intro i,
    intro useful,
    rw ←add_sub_assoc,
    rw sub_one,
    rw useful,
    rw sub_one,
  },
end

end int.iterate

-- def pow_hom (g : G) (a b : ℕ) : pow g a * pow g b = pow g (a + b) :=
-- begin

--   sorry
-- end

-- /-- definition of map sending g, n to gⁿ , n ∈ ℤ -/
-- def zpow (g : G) : ℤ → G
-- | (of_nat n) := pow g n
-- | (neg_succ_of_nat n) := pow g⁻¹ (n+1)

--example (g : G) : G ≃ G := by suggest

def thing (g : G) : G ≃ G :=
{ to_fun := (* g),
  inv_fun := (* g⁻¹),
  left_inv := by intro x; simp,
  right_inv := by intro x; simp }

  open int.iterate

lemma foo (g j : G) (a : ℤ) : j * (thing g^⦃a⦄ 1) = thing g^⦃a⦄ j :=
begin
  revert j,
  apply int.induction_on a,
  { simp},
  { intro i,
    intro hi,
    intro j,
    rw int.iterate.add_one,
    unfold function.comp,
    rw ←hi (thing _ j),
    rw ←hi,
    unfold thing, simp [mygroup.group.mul_assoc],
  },
  { intro i,
    intro hi,
    intro j,
    rw int.iterate.sub_one,
    unfold function.comp,
    conv_rhs begin
      rw ←hi,
    end,
    rw ←hi,
    unfold thing, simp [mygroup.group.mul_assoc],
  }
end

def zpow' (g : G) : ℤ → G := λ z, (thing g)^⦃z⦄ 1

instance : has_pow G ℤ := ⟨zpow'⟩

lemma zpow_hom (g : G) (a b : ℤ) : g^a * g^b = g^(a + b) :=
begin
  unfold has_pow.pow,
  unfold zpow',
  rw add_comm,
  rw int.iterate.add,
  unfold function.comp,
  rw foo,
end



/-- The subgroup generated by an element of a group equals the set of integer number powers of
    the element. -/
lemma mem_span_singleton {x y : G} : y ∈ span ({x} : set G) ↔ ∃ n : ℤ, x ^ n = y :=
begin
  sorry
end



end subgroup

end mygroup
