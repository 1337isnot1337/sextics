import Proposal.PExplicitWitnessDefinitions
import Mathlib.Tactic.FinCases

set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.ExplicitWitness
open MvPolynomial HodgeTestbed.Frozen

private theorem X0_reflect : reflectY X0 = X0 := by
  norm_num [reflectY, Frozen.X0]

private theorem X1_reflect : reflectY X1 = X1 := by
  norm_num [reflectY, Frozen.X1]

private theorem X2_reflect : reflectY X2 = X2 := by
  norm_num [reflectY, Frozen.X2]

private theorem Y0_reflect : reflectY Y0 = -Y0 := by
  norm_num [reflectY, Frozen.Y0]

private theorem Y1_reflect : reflectY Y1 = -Y1 := by
  norm_num [reflectY, Frozen.Y1]

private theorem Y2_reflect : reflectY Y2 = -Y2 := by
  norm_num [reflectY, Frozen.Y2]

theorem pA_reflect : reflectY pA = pA := by
  simp only [pA, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, ]
  <;> ring

theorem pB_reflect : reflectY pB = pB := by
  simp only [pB, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, X1_reflect, Y0_reflect]
  <;> ring

theorem pC_reflect : reflectY pC = pC := by
  simp only [pC, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, X1_reflect, Y0_reflect]
  <;> ring

theorem pD_reflect : reflectY pD = pD := by
  simp only [pD, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, X1_reflect, Y0_reflect]
  <;> ring

theorem qA_reflect : reflectY qA = qA := by
  simp only [qA, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, ]
  <;> ring

theorem qB_reflect : reflectY qB = qB := by
  simp only [qB, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, X2_reflect, Y2_reflect]
  <;> ring

theorem qC_reflect : reflectY qC = qC := by
  simp only [qC, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, X2_reflect, Y2_reflect]
  <;> ring

theorem qD_reflect : reflectY qD = qD := by
  simp only [qD, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, X2_reflect, Y2_reflect]
  <;> ring

theorem P_reflect : reflectY P = P := by
  simp only [P, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, X0_reflect, pA_reflect, pB_reflect, pC_reflect, pD_reflect]
  <;> ring

theorem Q_reflect : reflectY Q = Q := by
  simp only [Q, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, Y1_reflect, qA_reflect, qB_reflect, qC_reflect, qD_reflect]
  <;> ring

theorem fpP_reflect : reflectY fpP = fpP := by
  simp only [fpP, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, X0_reflect, pA_reflect, pB_reflect, pC_reflect]
  <;> ring

theorem fpQ_reflect : reflectY fpQ = fpQ := by
  simp only [fpQ, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, Y1_reflect, qA_reflect, qB_reflect, qC_reflect]
  <;> ring

theorem h0P_reflect : reflectY h0P = h0P := by
  simp only [h0P, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, pB_reflect, pC_reflect, pD_reflect]
  <;> ring

theorem HP_reflect : reflectY HP = HP := by
  simp only [HP, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, X0_reflect, h0P_reflect, pA_reflect, pB_reflect, pC_reflect, pD_reflect]
  <;> ring

theorem HQ_reflect : reflectY HQ = HQ := by
  simp only [HQ, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, Y1_reflect, qA_reflect, qB_reflect, qC_reflect, qD_reflect]
  <;> ring

theorem deltaP_reflect : reflectY deltaP = deltaP := by
  simp only [deltaP, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, pA_reflect, pB_reflect, pC_reflect, pD_reflect]
  <;> ring

theorem deltaQ_reflect : reflectY deltaQ = deltaQ := by
  simp only [deltaQ, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, qA_reflect, qB_reflect, qC_reflect, qD_reflect]
  <;> ring

theorem TQ_reflect : reflectY TQ = TQ := by
  simp only [TQ, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, HQ_reflect, Q_reflect, Y1_reflect, fpQ_reflect, qA_reflect, qB_reflect, qC_reflect, qD_reflect]
  <;> ring

theorem KP_reflect : reflectY KP = KP := by
  simp only [KP, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, X0_reflect, pA_reflect, pB_reflect, pC_reflect, pD_reflect]
  <;> ring

theorem LP_reflect : reflectY LP = LP := by
  simp only [LP, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, X0_reflect, pB_reflect, pC_reflect, pD_reflect]
  <;> ring

theorem G_reflect : reflectY G = G := by
  simp only [G, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, HP_reflect, HQ_reflect, P_reflect, Q_reflect, deltaP_reflect, deltaQ_reflect]
  <;> ring

theorem U1_reflect : reflectY U1 = U1 := by
  simp only [U1, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, HP_reflect, HQ_reflect, Q_reflect, TQ_reflect, h0P_reflect]
  <;> ring

theorem V_reflect : reflectY V = V := by
  simp only [V, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, HP_reflect, HQ_reflect, KP_reflect, LP_reflect, P_reflect, Q_reflect, deltaQ_reflect]
  <;> ring

theorem RP_reflect : reflectY RP = RP := by
  simp only [RP, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, P_reflect, X0_reflect, fpP_reflect]
  <;> ring

theorem RQ_reflect : reflectY RQ = RQ := by
  simp only [RQ, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, Q_reflect, Y1_reflect, fpQ_reflect]
  <;> ring

theorem R0_reflect : reflectY R0 = R0 := by
  simp only [R0, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, HP_reflect, HQ_reflect, KP_reflect, P_reflect, Q_reflect, RP_reflect, X0_reflect, deltaP_reflect, deltaQ_reflect, pC_reflect, pD_reflect]
  <;> ring

theorem R1_reflect : reflectY R1 = R1 := by
  simp only [R1, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, R0_reflect, U1_reflect, X0_reflect, fpQ_reflect]
  <;> ring

theorem D_reflect : reflectY D = D := by
  simp only [D, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, G_reflect, Q_reflect, X0_reflect]
  <;> ring

theorem nX1_reflect : reflectY nX1 = -nX1 := by
  simp only [nX1, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, Q_reflect, V_reflect, X1_reflect, Y1_reflect]
  <;> ring

theorem nX2_reflect : reflectY nX2 = -nX2 := by
  simp only [nX2, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, P_reflect, R1_reflect, X2_reflect, Y1_reflect]
  <;> ring

theorem nY0_reflect : reflectY nY0 = nY0 := by
  simp only [nY0, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, Q_reflect, V_reflect, Y0_reflect, Y1_reflect]
  <;> ring

theorem nY1_reflect : reflectY nY1 = nY1 := by
  simp only [nY1, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, P_reflect, R0_reflect, RQ_reflect, U1_reflect, X0_reflect, Y1_reflect]
  <;> ring

theorem nY2_reflect : reflectY nY2 = nY2 := by
  simp only [nY2, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, P_reflect, R1_reflect, Y1_reflect, Y2_reflect]
  <;> ring

theorem C_reflect : reflectY C = -C := by
  simp only [C, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, G_reflect, Q_reflect, R0_reflect, X0_reflect, Y1_reflect]
  <;> ring

theorem denominator_even : YEven D := D_reflect

theorem numerator_parity : ∀ i, if i.val < 3 then YOdd (N i) else YEven (N i) := by
  intro i
  fin_cases i
  · simp [N, YOdd]
  · simpa [N, YOdd, YEven] using nX1_reflect
  · simpa [N, YOdd, YEven] using nX2_reflect
  · simpa [N, YOdd, YEven] using nY0_reflect
  · simpa [N, YOdd, YEven] using nY1_reflect
  · simpa [N, YOdd, YEven] using nY2_reflect

end HodgeTestbed.ExplicitWitness
