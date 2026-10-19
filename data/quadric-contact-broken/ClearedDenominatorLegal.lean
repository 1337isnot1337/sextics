import Proposal.GenericDenominatorLink
import Proposal.ClearedDenominatorFiber
import Proposal.ComplexTarget

noncomputable section
namespace QuadricContactClearedDenominator
open MvPolynomial QuadricContactClearing QuadricContactComplex
open QuadricContactGenericDenominator

/-- The denominator produced by simultaneous homogeneous clearing is legal for
the protected sextic. The profile hypothesis is supplied by the proved
coefficient-clearing existence theorem; every matrix and inverse used to
establish coprimality is the actual generic/numeric one. -/
theorem denominator_legal (Q : BasePoly) (n : ℕ) (κ : ℚ) (hκ : κ ≠ 0)
    (hprofile : ratioBase Q = C κ * ac ^ n *
      activeFibre activeVariables activeDenominator) :
    IsRelPrime QuadricContactDenominator.targetF
      (complexMap (QuadricContactLift.denominator Q)) := by
  apply QuadricContactGenericDenominator.denominator_legal_of_active_fiber
    (complexMap (QuadricContactLift.denominator Q)) (κ : ℂ)
    (by exact_mod_cast hκ)
  change (QuadricContactDenominator.toUni
    (MvPolynomial.map (Rat.castHom ℂ) (QuadricContactLift.denominator Q))).map
      QuadricContactDenominator.specialize = _
  rw [← fiber_eq_protected]
  change fiber ((X 1 ^ 2 * X 2 ^ 2) * Q) = _
  rw [fiber_final_denominator]
  have h := congrArg fiber hprofile
  rw [fiber_ratioBase, map_mul, map_mul, fiber_C, map_pow, fiber_ac,
    one_pow, mul_one, activeFibre_terminal] at h
  exact h

theorem denominator_ne_zero (Q : BasePoly) (n : ℕ) (κ : ℚ) (hκ : κ ≠ 0)
    (hprofile : ratioBase Q = C κ * ac ^ n *
      activeFibre activeVariables activeDenominator) :
    complexMap (QuadricContactLift.denominator Q) ≠ 0 :=
  QuadricContactDenominator.denominator_ne_zero_of_legal _
    (denominator_legal Q n κ hκ hprofile)

end QuadricContactClearedDenominator

#print axioms QuadricContactClearedDenominator.denominator_legal
