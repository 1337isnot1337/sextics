import Proposal.PEllipticAmbientBaseEmbedding

/-! # The exact polynomial-style numerator of the supplied W = T/S equation

The input may be checked by polynomial arithmetic separately. This module proves
only its precise equivalence with the rational scalar equation, without producing T or S.
-/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart HodgeTestbed.Conic

def scalarNumerator (T : Fin 4 → K4) (S : K4) : K4 :=
  3 * fourP * fourQ * (S * fieldDivergence rationalPartial T - fieldAction rationalPartial T S) -
  4 * fourQ * S * fieldAction rationalPartial T fourP -
  2 * fourP * S * fieldAction rationalPartial T fourQ - 3 * fourP * fourQ * S ^ 2

/-- Full scalar defect, prior to assuming its numerator vanishes. -/
theorem scalarNumerator_full (T : Fin 4 → K4) (S : K4) (hS : S ≠ 0) :
    scalarNumerator T S = 3 * fourP * fourQ * S ^ 2 *
      (fourLW (fun i => T i / S) - 1) := by
  have hp : fourP ≠ 0 := fun hz => p_ne_zero (by rw [← baseEmbedding_p, hz, map_zero])
  have hq : fourQ ≠ 0 := fun hz => q_ne_zero (by rw [← baseEmbedding_q, hz, map_zero])
  have hv : (fun i => T i / S) = (fun i => S⁻¹ * T i) := by funext i; ring
  rw [hv, fourLW, fieldDivergence_scale, fieldAction_scale, fieldAction_scale]
  simp only [Derivation.leibniz_inv, smul_eq_mul, scalarNumerator]
  field_simp
  <;> ring

/-- Exact unit-conditioned bridge from a cleared numerator to the scalar primitive equation. -/
theorem scalarNumerator_iff (T : Fin 4 → K4) (S : K4) (hS : S ≠ 0) :
    scalarNumerator T S = 0 ↔ fourLW (fun i => T i / S) = 1 := by
  rw [scalarNumerator_full T S hS]
  have hp : fourP ≠ 0 := fun hz => p_ne_zero (by rw [← baseEmbedding_p, hz, map_zero])
  have hq : fourQ ≠ 0 := fun hz => q_ne_zero (by rw [← baseEmbedding_q, hz, map_zero])
  have hn : (3 : K4) * fourP * fourQ * S ^ 2 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp) hq) (pow_ne_zero _ hS)
  simp [hn, sub_eq_zero]

end HodgeTestbed.EllipticAmbient
