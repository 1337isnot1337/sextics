import Proposal.PExplicitWitnessGrading
import Proposal.PExplicitWitnessParity
import Proposal.PExplicitWitnessLegality
import Proposal.PEllipticAmbientActualEquations

/-! The complete, explicit certificate for the unchanged frozen P0 target.
The definitions match witness SHA256
2e2cccc705f3cc1ade70d8ebfad9ce7e6b573e7c2b77527550395f17404ad32a.
This theorem concerns one frozen sextic and one target polynomial.
-/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.ExplicitWitness

theorem certificate : Certificate Frozen.F Frozen.A degree D N C where
  toEquations := EllipticAmbient.actual_equations
  positive_degree := by norm_num [degree]
  denominator_ne_zero := denominator_ne_zero
  denominator_homogeneous := D_homogeneous
  numerator_homogeneous := numerator_homogeneous
  denominator_even := denominator_even
  numerator_parity := numerator_parity
  denominator_legal := denominator_legal

/-- An unconditional proof of the original existential goal, with explicit witnesses. -/
theorem frozenP0 : Frozen.P0 :=
  Frozen.p0_of_certificate degree D N C certificate

end HodgeTestbed.ExplicitWitness
