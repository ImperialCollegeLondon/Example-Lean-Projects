import tactic

/-- An elliptic curve over a field -/
structure elliptic_curve (k : Type) [field k] :=
(a1 a2 a3 a4 a6 : k)

namespace elliptic_curve

variables {k : Type} [field k] (E : elliptic_curve k)

/-- The set of points on an elliptic curve, considered as the affine
  solutions plus an extra term "zero" -/
def points := with_zero {P : k × k // let ⟨x, y⟩ := P in 
  y^2 + E.a1*x*y + E.a3*y = x^3 + E.a2*x^2 + E.a4*x + E.a6}

end elliptic_curve

