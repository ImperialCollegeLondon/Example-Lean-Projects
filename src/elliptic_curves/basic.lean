import tactic

open_locale classical -- assume the law of the excluded middle
noncomputable theory -- 

/-- An elliptic curve over a field -/
structure elliptic_curve (k : Type) [field k] :=
(a1 a2 a3 a4 a6 : k)

namespace elliptic_curve

-- "let k be a field"
variables {k : Type} [field k]

/-- The set of points on an elliptic curve, considered as the affine
  solutions plus an extra term "none" -/
def points (E : elliptic_curve k) := with_zero {P : k × k // let ⟨x, y⟩ := P in 
  y^2 + E.a1*x*y + E.a3*y = x^3 + E.a2*x^2 + E.a4*x + E.a6}

-- "let E be an elliptic curve over k"

variable (E : elliptic_curve k)

/-- notation 0 for the "extra point" we added -/
instance : has_zero (points E) := ⟨none⟩

def neg (P : points E) : points E :=
if P = 0 then 0 else some ⟨(sorry, sorry), sorry⟩


end elliptic_curve

