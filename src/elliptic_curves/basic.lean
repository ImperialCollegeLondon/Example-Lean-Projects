import tactic

open_locale classical -- assume the law of the excluded middle
noncomputable theory -- because Lean can't calculate with an arbitrary field

/-- An elliptic curve over a field -/
structure elliptic_curve (k : Type) [field k] :=
(a1 a2 a3 a4 a6 : k)

namespace elliptic_curve

-- "let k be a field"
variables {k : Type} [field k]

inductive with_zero' (X : Type)
| zero : with_zero'
| some (x : X) : with_zero'



/-- The set of points on an elliptic curve, considered as the affine
  solutions plus an extra term "none" -/
def points (E : elliptic_curve k) := with_zero {P : k × k // let ⟨x, y⟩ := P in 
  y^2 + E.a1*x*y + E.a3*y = x^3 + E.a2*x^2 + E.a4*x + E.a6}

def poss_invalid_points (E : elliptic_curve k) :=
with_zero (k × k)



#print prefix elliptic_curve.points


-- "let E be an elliptic curve over k"
variable (E : elliptic_curve k)


/-- notation 0 for the "extra point" we added -/
instance : has_zero (points E) := with_zero.has_zero

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

-- def is_on_curve (E : elliptic_curve k) (x y : k) : points E :=
-- if h : y^2+E.a1*x*y+E.a3*y = x^3 + E.a2*x^2 + E.a4*x + E.a6 then 
-- some ⟨⟨x,y⟩,h⟩ else 0

theorem neg_neg : function.involutive (neg E) :=
begin
  rintros (_|⟨⟨x, y⟩, h⟩),
  { refl },
  { simp only [elliptic_curve.neg],
    congr,
    ring }
end


end elliptic_curve

