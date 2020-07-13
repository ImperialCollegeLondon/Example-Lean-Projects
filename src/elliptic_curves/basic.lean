import tactic

open_locale classical -- assume the law of the excluded middle
noncomputable theory -- because Lean can't calculate with an arbitrary field

-- "let k be a field"
variables {k : Type} [field k]

def disc (a1 a2 a3 a4 a6 : k) : k :=
-a6*a1^6 + a4*a3*a1^5 + ((-a3^2 - 12*a6)*a2 + a4^2)*a1^4 + 
(8*a4*a3*a2 + (a3^3 + 36*a6*a3))*a1^3 + ((-8*a3^2 - 48*a6)*a2^2 + 8*a4^2*a2 + 
(-30*a4*a3^2 + 72*a6*a4))*a1^2 + (16*a4*a3*a2^2 + (36*a3^3 + 144*a6*a3)*a2 - 96*a4^2*a3)*a1
 + ((-16*a3^2 - 64*a6)*a2^3 + 16*a4^2*a2^2 + (72*a4*a3^2 + 288*a6*a4)*a2 + 
 (-27*a3^4 - 216*a6*a3^2 + (-64*a4^3 - 432*a6^2)))

/-- An elliptic curve over a field -/
structure elliptic_curve (k : Type) [field k] :=
(a1 a2 a3 a4 a6 : k)
(disc_nonzero : disc a1 a2 a3 a4 a6 ≠ 0)

namespace elliptic_curve

/-- The set of points on an elliptic curve, considered as the affine
  solutions plus an extra term "none" -/
def points (E : elliptic_curve k) := with_zero {P : k × k // let ⟨x, y⟩ := P in 
  y^2 + E.a1*x*y + E.a3*y = x^3 + E.a2*x^2 + E.a4*x + E.a6}

-- "let E be an elliptic curve over k"
variable (E : elliptic_curve k)

/-- notation 0 for the "extra point" we added -/
instance : has_zero (points E) := with_zero.has_zero

def scale (E : elliptic_curve k) (d : k) (hd : d ≠ 0) :
  elliptic_curve k :=
{ a1 := d*E.a1,
  a2 := d*d*E.a2,
  a3 := d*d*d*E.a3,
  a4 := d*d*d*d*E.a4,
  a6 := d*d*d*d*d*d*E.a6,
  disc_nonzero := begin
    have hE : disc E.a1 E.a2 E.a3 E.a4 E.a6 ≠ 0,
      exact E.disc_nonzero,
    have h12 : d^12*disc E.a1 E.a2 E.a3 E.a4 E.a6 ≠ 0,
      refine mul_ne_zero _ hE,
      exact pow_ne_zero 12 hd,
    convert h12,
    unfold disc,
    ring,
  end }

example (a b c : k) (h : b = c) : a * b = a * c := congr_arg (has_mul.mul a) h

def to_scale (E : elliptic_curve k) (d : k) (hd : d ≠ 0) : points E → points (scale E d hd)
| 0 := 0
| (some P) :=
let ⟨⟨x, y⟩, h⟩ := P in
some ⟨⟨d*d*x, d*d*d*y⟩, begin
  change y^2 + E.a1*x*y + E.a3*y = x^3 + E.a2*x^2 + E.a4*x + E.a6 at h,
  replace h := congr_arg (λ t, d^6*t) h,
  dsimp at h,
  change _ = _,
  unfold scale,
  dsimp,
  convert h,
    ring_exp,
    ring_exp,
end⟩

@[simp] lemma helper (a b : k) (h : b ≠ 0) : (a * b⁻¹) * b = a :=
begin
  rw mul_assoc,
  rw inv_mul_cancel h,
  rw mul_one,
end


def of_scale (E : elliptic_curve k) (d : k) (hd : d ≠ 0) : points (scale E d hd) → points E
| 0 := 0
| (some P) :=
let ⟨⟨x, y⟩, h⟩ := P in
let F := (scale E d hd) in
some ⟨⟨d⁻¹ * d⁻¹ * x, d⁻¹ * d⁻¹ * d⁻¹ * y⟩, begin
  change y^2 + F.a1*x*y + F.a3*y = x^3 + F.a2*x^2 + F.a4*x + F.a6 at h,
  replace h := congr_arg (λ t, d⁻¹^6*t) h,
  dsimp at h,
  change _ = _,
  simp only [F, scale] at h,
  have hdd : d * d⁻¹ = 1,
    exact mul_inv_cancel hd,
  convert h,
  { ring_exp,
    rw (show d⁻¹ ^ 6 = d⁻¹ * (d⁻¹ * d⁻¹ * d⁻¹^3), by ring),
    repeat {rw ←mul_assoc},
    rw hdd,
    rw (show d ^ 3 * d⁻¹ * d⁻¹ * d⁻¹ = d * ( d * ( d * d⁻¹) * d⁻¹) * d⁻¹, by ring),
    rw [hdd, mul_one, hdd, mul_one, hdd],
    ring },
  { repeat {rw pow_succ},
    repeat {rw pow_zero},
    repeat {rw mul_one},
--    rw (show d⁻¹ ^ 6 = (d⁻¹ * d⁻¹ * d⁻¹ * d⁻¹ * d⁻¹ * d⁻¹), by ring),
    repeat {rw mul_add},
    repeat {rw ←mul_assoc},
    repeat {rw helper _ d hd},
    rw inv_mul_cancel hd,
    ring_exp}
end⟩.


def scale_points (E : elliptic_curve k) (d : k) (hd : d ≠ 0) :
  points E ≃ points (scale E d hd) :=
{ to_fun := to_scale E d hd,
  inv_fun := of_scale E d hd,
  left_inv := begin
    intro P,
    cases P,
      refl,
    rcases P with ⟨⟨x, y⟩, h⟩,
    simp only [to_scale, of_scale],
    congr',
    { repeat {rw ←mul_assoc},
      simp [hd] },
    { repeat {rw ←mul_assoc},
      simp [hd] },
  end,
  right_inv := begin
    intro P,
    cases P,
      refl,
    rcases P with ⟨⟨x, y⟩, h⟩,
    simp only [to_scale, of_scale],
    congr',
    { repeat {rw ←mul_assoc},
      simp [hd] },
    { repeat {rw ←mul_assoc},
      simp [hd] },    
  end }

def neg : points E → points E
| 0 := 0
| (some P) := 
  let ⟨⟨x, y⟩, hP⟩ := P in 
  some ⟨(x, -E.a1*x-E.a3-y), begin
    -- need to prove point is on the curve
    change y^2 + E.a1*x*y + E.a3*y = x^3 + E.a2*x^2 + E.a4*x + E.a6 at hP,
    change (-E.a1*x-E.a3-y)^2 + E.a1*x*(-E.a1*x-E.a3-y)+E.a3*(-E.a1*x-E.a3-y)
      = x^3 + E.a2*x^2 + E.a4*x + E.a6,
    -- our hypothesis is y^2+...=x^3+...
    -- want : (a₁x-a₃-y)^2+...=x^3+...
    -- I claim that our hypothesis equals what we want
    convert hP using 1,
    -- RHS's are equal, so it suffices to prove LHS's are equal
    ring,
  end⟩

theorem neg_to_scale (d : k) (hd : d ≠ 0) (P : points E) :
  (scale E d hd).neg (to_scale E d hd P) = to_scale E d hd (E.neg P) :=
begin
  cases P,
    refl,
  rcases P with ⟨⟨x, y⟩, h⟩,
  simp [scale, to_scale, neg],
  congr',
  ring,
end

theorem neg_of_scale (d : k) (hd : d ≠ 0) (P : points (scale E d hd)) :
  E.neg (of_scale E d hd P) = of_scale E d hd ((scale E d hd).neg P) :=
begin
  cases P,
    refl,
  rcases P with ⟨⟨x, y⟩, h⟩,
  simp [scale, of_scale, neg],
  congr',
  repeat {rw ←mul_assoc},
  simp [hd],
  repeat {rw mul_sub},
  rw neg_mul_eq_mul_neg,
  repeat {rw ←mul_assoc},
  simp [hd],
  repeat {rw ←mul_assoc},
  simp [hd],
  ring,
end

theorem neg_neg : function.involutive (neg E) :=
begin
  rintros (_|⟨⟨x, y⟩, h⟩),
  { refl },
  { simp only [elliptic_curve.neg],
    congr,
    ring }
end

example (a b : k) : a = b ↔ a - b = 0 := by library_search
#check sub_eq_zero

lemma pow_three {R : Type} [comm_ring R] (x : R) :
x^3=x*x*x := by ring

def double : points E → points E
| 0 := 0
| (some P) :=
let ⟨⟨x, y⟩, h⟩ := P in
if h2 : 2*y+E.a1*x+E.a3 = 0 then 0 else
  let d := 2*y+E.a1*x+E.a3 in
  let sd := (3*x^2+2*E.a2*x+E.a4-E.a1*y) in
  let td := y*d-sd*x in
  let x₂dd := sd^2+E.a1*sd*d-E.a2*d*d-2*x*d*d in
  let y₂ddd := sd*x₂dd+td*d*d in
  let P2d : points (scale E d h2) := some ⟨⟨x₂dd, y₂ddd⟩, begin
    unfold points._match_1,
    simp only [y₂ddd, x₂dd, td, sd, scale],
  change y^2 + E.a1*x*y + E.a3*y = x^3 + E.a2*x^2 + E.a4*x + E.a6 at h,
  rw ←sub_eq_zero at h ⊢,
  
    sorry
  end⟩ in

  sorry

  #exit 
  E.neg (some ⟨⟨x₂dd/d/d, y₂ddd/d/d/d⟩,begin
    change (y₂ddd/d/d/d)^2 + E.a1*(x₂dd/d/d)*(y₂ddd/d/d/d) + E.a3*(y₂ddd/d/d/d) =
      (x₂dd/d/d)^3 + E.a2*(x₂dd/d/d)^2 + E.a4*(x₂dd/d/d) + E.a6,
    have hd : d ≠ 0,
      exact h2,
    suffices : d^6*((y₂ddd/d/d/d)^2 + E.a1*(x₂dd/d/d)*(y₂ddd/d/d/d) + E.a3*(y₂ddd/d/d/d))
      = d^6*((x₂dd/d/d)^3 + E.a2*(x₂dd/d/d)^2 + E.a4*(x₂dd/d/d) + E.a6),
    have hd6 : d^6 ≠ 0,
      exact pow_ne_zero 6 hd,
    apply (mul_right_inj' hd6).1 this,
    repeat {rw pow_two},
    repeat {rw pow_three}, 
    repeat {rw mul_add},
    rw (show d^6=d*d*d*d*d*d, by ring),
    rw mul_assoc,
    field_simp [hd],
    -- simp only [x₂, y₂, s, t],

    sorry

    -- simp,
    -- field_simp [hd],
    -- ring,
  end⟩)

#exit
def double : points E → points E
| 0 := 0
| (some P) :=
let ⟨⟨x, y⟩, h⟩ := P in
if h2 : 2*y+E.a1*x+E.a3 = 0 then 0 else
some ⟨⟨(9*x^4 + (E.a1^2 + 12*E.a2)*x^3 + (-8*E.a1*y + (E.a2*E.a1^2 - E.a3*E.a1 
+ (4*E.a2^2 + 6*E.a4)))*x^2 + (-8*y^2 + (-E.a1^3 - 4*E.a2*E.a1 - 8*E.a3)*y + 
(E.a4*E.a1^2 + (4*E.a4*E.a2 - 2*E.a3^2)))*x + ((-E.a1^2 - 4*E.a2)*y^2 + 
(-E.a3*E.a1^2 - 4*E.a3*E.a2)*y + (E.a4*E.a3*E.a1 + (-E.a3^2*E.a2 + E.a4^2))))
/
(E.a1^2*x^2 + (4*E.a1*y + 2*E.a3*E.a1)*x + (4*y^2 + 4*E.a3*y + E.a3^2)), 
(-27*x^6 + (-9*E.a1^2 - 54*E.a2)*x^5 + (27*E.a1*y + (-E.a1^4 - 15*E.a2*E.a1^2 + 
(-36*E.a2^2 - 27*E.a4)))*x^4 + (36*y^2 + (8*E.a1^3 + 24*E.a2*E.a1 + 36*E.a3)*y + (-E.a2*E.a1^4 - E.a3*E.a1^3 + (-6*E.a2^2 - 9*E.a4)*E.a1^2 - 6*E.a3*E.a2*E.a1 + (-8*E.a2^3 - 36*E.a4*E.a2 + 9*E.a3^2)))*x^3 + ((9*E.a1^2 + 36*E.a2)*y^2 + (E.a1^5 + 5*E.a2*E.a1^3 + 9*E.a3*E.a1^2 + (4*E.a2^2 + 6*E.a4)*E.a1 + 36*E.a3*E.a2)*y + (-E.a4*E.a1^4 - E.a3*E.a2*E.a1^3 - 7*E.a4*E.a2*E.a1^2 + (-4*E.a3*E.a2^2 - 6*E.a4*E.a3)*E.a1 + (-12*E.a4*E.a2^2 + 9*E.a3^2*E.a2 - 9*E.a4^2)))*x^2 + (-8*E.a1*y^3 + (2*E.a1^4 + 10*E.a2*E.a1^2 - 12*E.a3*E.a1 + (8*E.a2^2 + 12*E.a4))*y^2 + (2*E.a3*E.a1^4 + 10*E.a3*E.a2*E.a1^2 - 6*E.a3^2*E.a1 + (8*E.a3*E.a2^2 + 12*E.a4*E.a3))*y + (-2*E.a4*E.a3*E.a1^3 + (E.a3^2*E.a2 - 2*E.a4^2)*E.a1^2 + (-6*E.a4*E.a3*E.a2 - E.a3^3)*E.a1 + (2*E.a3^2*E.a2^2 - 6*E.a4^2*E.a2 + 3*E.a4*E.a3^2)))*x + (-8*y^4 + (E.a1^3 + 4*E.a2*E.a1 - 20*E.a3)*y^3 + (2*E.a3*E.a1^3 + E.a4*E.a1^2 + 8*E.a3*E.a2*E.a1 + (4*E.a4*E.a2 - 18*E.a3^2))*y^2 + (E.a3^2*E.a1^3 + (5*E.a3^2*E.a2 - E.a4^2)*E.a1 + (4*E.a4*E.a3*E.a2 - 7*E.a3^3))*y + (-E.a4*E.a3^2*E.a1^2 + (E.a3^3*E.a2 - 2*E.a4^2*E.a3)*E.a1 + (E.a4*E.a3^2*E.a2 + (-E.a3^4 - E.a4^3)))))/(E.a1^3*x^3 + (6*E.a1^2*y + 3*E.a3*E.a1^2)*x^2 + (12*E.a1*y^2 + 12*E.a3*E.a1*y + 3*E.a3^2*E.a1)*x + (8*y^3 + 12*E.a3*y^2 + 6*E.a3^2*y + E.a3^3))



def add : points E → points E → points E
| 0 P := P
| P 0 := P
| (some P) (some Q) :=
let ⟨⟨x1, y1⟩, h1⟩ := P in
let ⟨⟨x2, y2⟩, h2⟩ := Q in
sorry

end elliptic_curve

