import Proposal.PEllipticAmbientActualScalar

/-! # An unconditional rational physical field from the actual frozen scalar tuple

Polynomial evaluation is used only before entering the fraction field. No map
from an entire rational function field to a specialized point is asserted.
-/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart HodgeTestbed.Conic MvPolynomial

def actualSPoly : Poly 4 :=
  2*Cubic.G (pCoefficients (X 0) (X 1)) (qCoefficients (X 2) (X 3))

theorem actualS_embed : embed actualSPoly = actualS := by
  simp only [actualSPoly, actualS, pc, qc, pCoefficients, qCoefficients,
    Cubic.G, Cubic.H, Cubic.h4, Cubic.h6, Cubic.h0, Cubic.delta, Cubic.f,
    map_mul, map_add, map_sub, map_pow, map_ofNat, coord]

/-- The actual denominator is nonzero, checked at a rational point of its polynomial model. -/
theorem actualS_ne_zero : actualS ≠ 0 := by
  intro hz
  have hp : actualSPoly = 0 := embed_injective (by rw [actualS_embed, hz, map_zero])
  have he := congrArg (eval (fun _ : Fin 4 => (1 : ℚ))) hp
  norm_num [actualSPoly, pCoefficients, qCoefficients, Cubic.G, Cubic.H,
    Cubic.h4, Cubic.h6, Cubic.h0, Cubic.delta, Cubic.f, map_ofNat] at he

theorem actual_scalar_equation : fourLW (fun i => actualT i / actualS) = 1 :=
  (scalarNumerator_iff actualT actualS actualS_ne_zero).mp actual_scalar_identity

/-- The supplied explicit rational primitive, in the normalization of the ambient lift. -/
def actualPrimitive : Fin 4 → K4 := primitiveFromW (fun i => actualT i / actualS)
def actualPhysical : Fin 5 → K :=
  physicalField (liftBase (extendBase actualPrimitive)) (liftNormal (extendBase actualPrimitive))

/-- All scalar inputs have been discharged for the actual frozen coefficients.
This remains a rational ambient identity; polynomial certificate properties are downstream. -/
theorem actual_physical_equations :
    fieldAction physicalPartial actualPhysical (splitSubstitution Frozen.F) = splitSubstitution Frozen.A ∧
    fieldDivergence physicalPartial actualPhysical =
      -splitF * (1 + 6*q*dp (extendBase actualPrimitive)) / (3*p*q*lambda^5) :=
  physical_lift_of_scalarNumerator actualT actualS actualS_ne_zero actual_scalar_identity

end HodgeTestbed.EllipticAmbient
