import HodgeTarget
import Proposal.ComplexTarget

noncomputable section
namespace Submission

theorem target_F : QuadricContactDenominator.targetF = HodgeSubmission.F := by
  simp only [QuadricContactDenominator.targetF, HodgeSubmission.F,
    show (5/7 : ℂ) = 5*(1/7) by ring, map_mul, map_ofNat]
  ring

theorem target_A : QuadricContactComplex.targetA = HodgeSubmission.A := by
  simp only [QuadricContactComplex.targetA, HodgeSubmission.A]
  ring

end Submission
