import Proposal.PEllipticAmbientPhysical
import Proposal.PEllipticAmbientScalarNumerator

/-! # Supplied scalar numerator to the actual frozen physical ambient identities -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.Conic

/-- Undo W=18pq B0 inside the actual four-variable coefficient field. -/
def primitiveFromW (W : Fin 4 → K4) (i : Fin 4) : K4 := W i / (18 * fourP * fourQ)

theorem primitiveFromW_equation (W : Fin 4 → K4) (hW : fourLW W = 1) :
    fourL4 (primitiveFromW W) = 1 / (18 * fourP * fourQ) := by
  apply baseEmbedding.injective
  change baseEmbedding (fourL4 (primitiveFromW W)) = baseEmbedding (1 / (18 * fourP * fourQ))
  rw [baseEmbedding_L4]
  have he : (fun i => (18 * p * q) * extendBase (primitiveFromW W) i) = extendBase W := by
    funext i
    simp only [extendBase, primitiveFromW, map_div₀, map_mul, map_ofNat,
      baseEmbedding_p, baseEmbedding_q]
    field_simp [p_ne_zero, q_ne_zero]
  have hh : L4 (extendBase (primitiveFromW W)) = 1 / (18 * p * q) := by
    apply (primitive_iff_rescaled _).mpr
    rw [he, ← baseEmbedding_LW, hW, map_one]
  rw [hh]
  simp [map_ofNat]

/-- The complete conditional transfer accepts an explicit T,S and the exact cleared
scalar identity. It concludes a physical F-multiple, not a polynomial P0 certificate. -/
theorem physical_lift_of_scalarNumerator (T : Fin 4 → K4) (S : K4) (hS : S ≠ 0)
    (hscalar : scalarNumerator T S = 0) :
    let B := extendBase (primitiveFromW (fun i => T i / S))
    fieldAction physicalPartial (physicalField (liftBase B) (liftNormal B))
      (splitSubstitution Frozen.F) = splitSubstitution Frozen.A ∧
    fieldDivergence physicalPartial (physicalField (liftBase B) (liftNormal B)) =
      -splitF * (1 + 6 * q * dp B) / (3 * p * q * lambda ^ 5) := by
  dsimp only
  have hW := (scalarNumerator_iff T S hS).mp hscalar
  have hh := four_variable_lift (primitiveFromW (fun i => T i / S))
    (primitiveFromW_equation _ hW)
  constructor
  · rw [physical_action, frozen_F_split, frozen_A_split]
    exact hh.1
  · rw [physical_divergence]
    exact hh.2

end HodgeTestbed.EllipticAmbient
