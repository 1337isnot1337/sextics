import Proposal.PEllipticAmbientHomogeneousRules
import Proposal.PEllipticAmbientFactoredField
import Proposal.PExplicitWitnessDefinitions

/-! Exact covariant scaling from the frozen four-variable field to the shared polynomial witness. -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart

def homBase : K4 →ₐ[ℚ] K6 := homSplit.comp baseEmbedding
@[simp] theorem homBase_apply (f : K4) : homBase f = homSplit (baseEmbedding f) := rfl

theorem homBase_coord (i : Fin 4) : homBase (coord i) =
    (![coord 1/coord 0, coord 3/coord 0, coord 2/coord 4, coord 5/coord 4] : Fin 4 → K6) i := by
  fin_cases i <;> simp only [homBase_apply, baseEmbedding_coord, homSplit_coord, homCoordinates,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  all_goals rfl

theorem hom_pA : homBase pc.a = embed ExplicitWitness.pA := by
  simp only [pc, pCoefficients, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, homBase_coord, ExplicitWitness.pA,
    Frozen.X0, Frozen.X1, Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2, embed_X]
  all_goals norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_pB : homBase pc.b = embed ExplicitWitness.pB / coord (0 : Fin 6)^2 := by
  simp only [pc, pCoefficients, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, homBase_coord, ExplicitWitness.pB,
    Frozen.X0, Frozen.X1, Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2, embed_X]
  all_goals norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_pC : homBase pc.c = embed ExplicitWitness.pC / coord (0 : Fin 6)^4 := by
  simp only [pc, pCoefficients, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, homBase_coord, ExplicitWitness.pC,
    Frozen.X0, Frozen.X1, Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2, embed_X]
  all_goals norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_pD : homBase pc.d = embed ExplicitWitness.pD / coord (0 : Fin 6)^6 := by
  simp only [pc, pCoefficients, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, homBase_coord, ExplicitWitness.pD,
    Frozen.X0, Frozen.X1, Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2, embed_X]
  all_goals norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_qA : homBase qc.a = embed ExplicitWitness.qA := by
  simp only [qc, qCoefficients, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, homBase_coord, ExplicitWitness.qA,
    Frozen.X0, Frozen.X1, Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2, embed_X]
  all_goals norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_qB : homBase qc.b = embed ExplicitWitness.qB / coord (4 : Fin 6)^2 := by
  simp only [qc, qCoefficients, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, homBase_coord, ExplicitWitness.qB,
    Frozen.X0, Frozen.X1, Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2, embed_X]
  all_goals norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_qC : homBase qc.c = embed ExplicitWitness.qC / coord (4 : Fin 6)^4 := by
  simp only [qc, qCoefficients, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, homBase_coord, ExplicitWitness.qC,
    Frozen.X0, Frozen.X1, Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2, embed_X]
  all_goals norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_qD : homBase qc.d = embed ExplicitWitness.qD / coord (4 : Fin 6)^6 := by
  simp only [qc, qCoefficients, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, homBase_coord, ExplicitWitness.qD,
    Frozen.X0, Frozen.X1, Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2, embed_X]
  all_goals norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_P : homBase (Cubic.f pc) = embed ExplicitWitness.P / coord (0 : Fin 6)^6 := by
  simp only [Cubic.f, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, ExplicitWitness.P,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_Q : homBase (Cubic.f qc) = embed ExplicitWitness.Q / coord (4 : Fin 6)^6 := by
  simp only [Cubic.f, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, ExplicitWitness.Q,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_fpP : homBase (Cubic.fp pc) = embed ExplicitWitness.fpP / coord (0 : Fin 6)^4 := by
  simp only [Cubic.fp, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, ExplicitWitness.fpP,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_fpQ : homBase (Cubic.fp qc) = embed ExplicitWitness.fpQ / coord (4 : Fin 6)^4 := by
  simp only [Cubic.fp, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, ExplicitWitness.fpQ,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_h0P : homBase (Cubic.h0 pc) = embed ExplicitWitness.h0P / coord (0 : Fin 6)^8 := by
  simp only [Cubic.h0, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, ExplicitWitness.h0P,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_HP : homBase (Cubic.H pc) = embed ExplicitWitness.HP / coord (0 : Fin 6)^8 := by
  simp only [Cubic.H, Cubic.h4, Cubic.h6, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, ExplicitWitness.HP, ExplicitWitness.h0P,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_HQ : homBase (Cubic.H qc) = embed ExplicitWitness.HQ / coord (4 : Fin 6)^8 := by
  simp only [Cubic.H, Cubic.h4, Cubic.h6, Cubic.h0, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, hom_HP, ExplicitWitness.HQ,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_deltaP : homBase (Cubic.delta pc) = embed ExplicitWitness.deltaP / coord (0 : Fin 6)^12 := by
  simp only [Cubic.delta, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, hom_HP, hom_HQ, ExplicitWitness.deltaP,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_deltaQ : homBase (Cubic.delta qc) = embed ExplicitWitness.deltaQ / coord (4 : Fin 6)^12 := by
  simp only [Cubic.delta, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, hom_HP, hom_HQ, hom_deltaP, ExplicitWitness.deltaQ,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_TQ : homBase (Cubic.t qc) = embed ExplicitWitness.TQ / coord (4 : Fin 6)^12 := by
  simp only [Cubic.t, Cubic.Hp, Cubic.h4, Cubic.h6, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, hom_HP, hom_HQ, hom_deltaP, hom_deltaQ, ExplicitWitness.TQ,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_KP : homBase (Cubic.k pc) = embed ExplicitWitness.KP / coord (0 : Fin 6)^12 := by
  simp only [Cubic.k, Cubic.kp, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, hom_HP, hom_HQ, hom_deltaP, hom_deltaQ, hom_TQ, ExplicitWitness.KP,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_LP : homBase (Cubic.l pc) = embed ExplicitWitness.LP / coord (0 : Fin 6)^8 := by
  simp only [Cubic.l, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, hom_HP, hom_HQ, hom_deltaP, hom_deltaQ, hom_TQ, hom_KP, ExplicitWitness.LP,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_RP : homBase (Cubic.rf pc) = embed ExplicitWitness.RP / coord (0 : Fin 6)^6 := by
  simp only [Cubic.rf, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, hom_HP, hom_HQ, hom_deltaP, hom_deltaQ, hom_TQ, hom_KP, hom_LP, ExplicitWitness.RP,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_RQ : homBase (Cubic.rf qc) = embed ExplicitWitness.RQ / coord (4 : Fin 6)^6 := by
  simp only [Cubic.rf, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, hom_HP, hom_HQ, hom_deltaP, hom_deltaQ, hom_TQ, hom_KP, hom_LP, hom_RP, ExplicitWitness.RQ,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_G : homBase (Cubic.G pc qc) = embed ExplicitWitness.G / (coord (0 : Fin 6)^24*coord (4 : Fin 6)^24) := by
  simp only [Cubic.G, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, hom_HP, hom_HQ, hom_deltaP, hom_deltaQ, hom_TQ, hom_KP, hom_LP, hom_RP, hom_RQ, ExplicitWitness.G,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_U1 : homBase (Cubic.U1 pc qc) = embed ExplicitWitness.U1 / (coord (0 : Fin 6)^16*coord (4 : Fin 6)^26) := by
  simp only [Cubic.U1, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, hom_HP, hom_HQ, hom_deltaP, hom_deltaQ, hom_TQ, hom_KP, hom_LP, hom_RP, hom_RQ, hom_G, ExplicitWitness.U1,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_V : homBase (Cubic.V pc qc) = embed ExplicitWitness.V / (coord (0 : Fin 6)^24*coord (4 : Fin 6)^24) := by
  simp only [Cubic.V, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, hom_HP, hom_HQ, hom_deltaP, hom_deltaQ, hom_TQ, hom_KP, hom_LP, hom_RP, hom_RQ, hom_G, hom_U1, ExplicitWitness.V,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

theorem hom_R0 : homBase (Cubic.R0 pc qc) = embed ExplicitWitness.R0 / (coord (0 : Fin 6)^24*coord (4 : Fin 6)^24) := by
  simp only [Cubic.R0, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, hom_pA, hom_pB, hom_pC, hom_pD, hom_qA, hom_qB, hom_qC, hom_qD, hom_P, hom_Q, hom_fpP, hom_fpQ, hom_h0P, hom_HP, hom_HQ, hom_deltaP, hom_deltaQ, hom_TQ, hom_KP, hom_LP, hom_RP, hom_RQ, hom_G, hom_U1, hom_V, ExplicitWitness.R0,
    Frozen.X0, Frozen.Y1, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  <;> ring

end HodgeTestbed.EllipticAmbient
