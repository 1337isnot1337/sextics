import Proposal.PExplicitWitnessDefinitions
import Mathlib.Tactic.FinCases

set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.ExplicitWitness
open MvPolynomial HodgeTestbed.Frozen

private theorem X0_homogeneous : (X0 : SexticPoly).IsHomogeneous 1 := by
  exact isHomogeneous_X ℚ (0 : Fin 6)

private theorem X1_homogeneous : (X1 : SexticPoly).IsHomogeneous 1 := by
  exact isHomogeneous_X ℚ (1 : Fin 6)

private theorem X2_homogeneous : (X2 : SexticPoly).IsHomogeneous 1 := by
  exact isHomogeneous_X ℚ (2 : Fin 6)

private theorem Y0_homogeneous : (Y0 : SexticPoly).IsHomogeneous 1 := by
  exact isHomogeneous_X ℚ (3 : Fin 6)

private theorem Y1_homogeneous : (Y1 : SexticPoly).IsHomogeneous 1 := by
  exact isHomogeneous_X ℚ (4 : Fin 6)

private theorem Y2_homogeneous : (Y2 : SexticPoly).IsHomogeneous 1 := by
  exact isHomogeneous_X ℚ (5 : Fin 6)

theorem pA_homogeneous : pA.IsHomogeneous 0 := by
  simpa only [pA, map_ofNat] using ((show (14 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (14 : ℚ))))

theorem pB_homogeneous : pB.IsHomogeneous 2 := by
  simpa only [pB, map_ofNat] using ((((show (7 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (7 : ℚ)))).mul ((X1_homogeneous).pow 2)).add (((show (21 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (21 : ℚ)))).mul ((Y0_homogeneous).pow 2)))

theorem pC_homogeneous : pC.IsHomogeneous 4 := by
  simpa only [pC, map_ofNat] using (((((show (23 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (23 : ℚ)))).mul ((X1_homogeneous).pow 4)).add ((((show (12 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (12 : ℚ)))).mul ((X1_homogeneous).pow 2)).mul ((Y0_homogeneous).pow 2))).add (((show (23 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (23 : ℚ)))).mul ((Y0_homogeneous).pow 4)))

theorem pD_homogeneous : pD.IsHomogeneous 6 := by
  simpa only [pD, map_ofNat] using ((((((show (4 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (4 : ℚ)))).mul ((X1_homogeneous).pow 6)).add ((((show (39 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (39 : ℚ)))).mul ((X1_homogeneous).pow 4)).mul ((Y0_homogeneous).pow 2))).add ((((show (73 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (73 : ℚ)))).mul ((X1_homogeneous).pow 2)).mul ((Y0_homogeneous).pow 4))).add (((show (8 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (8 : ℚ)))).mul ((Y0_homogeneous).pow 6)))

theorem qA_homogeneous : qA.IsHomogeneous 0 := by
  simpa only [qA, map_ofNat] using ((show (59 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (59 : ℚ))))

theorem qB_homogeneous : qB.IsHomogeneous 2 := by
  simpa only [qB, map_ofNat] using ((((show (43 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (43 : ℚ)))).mul ((X2_homogeneous).pow 2)).add (((show (61 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (61 : ℚ)))).mul ((Y2_homogeneous).pow 2)))

theorem qC_homogeneous : qC.IsHomogeneous 4 := by
  simpa only [qC, map_ofNat] using (((((show (37 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (37 : ℚ)))).mul ((X2_homogeneous).pow 4)).add ((((show (47 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (47 : ℚ)))).mul ((X2_homogeneous).pow 2)).mul ((Y2_homogeneous).pow 2))).add (((show (67 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (67 : ℚ)))).mul ((Y2_homogeneous).pow 4)))

theorem qD_homogeneous : qD.IsHomogeneous 6 := by
  simpa only [qD, map_ofNat] using ((((((show (31 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (31 : ℚ)))).mul ((X2_homogeneous).pow 6)).add ((((show (41 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (41 : ℚ)))).mul ((X2_homogeneous).pow 4)).mul ((Y2_homogeneous).pow 2))).add ((((show (53 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (53 : ℚ)))).mul ((X2_homogeneous).pow 2)).mul ((Y2_homogeneous).pow 4))).add (((show (71 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (71 : ℚ)))).mul ((Y2_homogeneous).pow 6)))

theorem P_homogeneous : P.IsHomogeneous 6 := by
  simpa only [P, map_ofNat] using (((((pA_homogeneous).mul ((X0_homogeneous).pow 6)).add ((pB_homogeneous).mul ((X0_homogeneous).pow 4))).add ((pC_homogeneous).mul ((X0_homogeneous).pow 2))).add (pD_homogeneous))

theorem Q_homogeneous : Q.IsHomogeneous 6 := by
  simpa only [Q, map_ofNat] using (((((qA_homogeneous).mul ((Y1_homogeneous).pow 6)).add ((qB_homogeneous).mul ((Y1_homogeneous).pow 4))).add ((qC_homogeneous).mul ((Y1_homogeneous).pow 2))).add (qD_homogeneous))

theorem fpP_homogeneous : fpP.IsHomogeneous 4 := by
  simpa only [fpP, map_ofNat] using ((((((show (3 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (3 : ℚ)))).mul (pA_homogeneous)).mul ((X0_homogeneous).pow 4)).add ((((show (2 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (2 : ℚ)))).mul (pB_homogeneous)).mul ((X0_homogeneous).pow 2))).add (pC_homogeneous))

theorem fpQ_homogeneous : fpQ.IsHomogeneous 4 := by
  simpa only [fpQ, map_ofNat] using ((((((show (3 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (3 : ℚ)))).mul (qA_homogeneous)).mul ((Y1_homogeneous).pow 4)).add ((((show (2 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (2 : ℚ)))).mul (qB_homogeneous)).mul ((Y1_homogeneous).pow 2))).add (qC_homogeneous))

theorem h0P_homogeneous : h0P.IsHomogeneous 8 := by
  simpa only [h0P, map_ofNat] using (((pC_homogeneous).pow 2).sub ((((show (3 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (3 : ℚ)))).mul (pB_homogeneous)).mul (pD_homogeneous)))

theorem HP_homogeneous : HP.IsHomogeneous 8 := by
  simpa only [HP, map_ofNat] using ((((((pB_homogeneous).pow 2).sub ((((show (3 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (3 : ℚ)))).mul (pA_homogeneous)).mul (pC_homogeneous))).mul ((X0_homogeneous).pow 4)).add ((((pB_homogeneous).mul (pC_homogeneous)).sub ((((show (9 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (9 : ℚ)))).mul (pA_homogeneous)).mul (pD_homogeneous))).mul ((X0_homogeneous).pow 2))).add (h0P_homogeneous))

theorem HQ_homogeneous : HQ.IsHomogeneous 8 := by
  simpa only [HQ, map_ofNat] using (((((((qB_homogeneous).pow 2).sub ((((show (3 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (3 : ℚ)))).mul (qA_homogeneous)).mul (qC_homogeneous))).mul ((Y1_homogeneous).pow 4)).add ((((qB_homogeneous).mul (qC_homogeneous)).sub ((((show (9 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (9 : ℚ)))).mul (qA_homogeneous)).mul (qD_homogeneous))).mul ((Y1_homogeneous).pow 2))).add ((qC_homogeneous).pow 2)).sub ((((show (3 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (3 : ℚ)))).mul (qB_homogeneous)).mul (qD_homogeneous)))

theorem deltaP_homogeneous : deltaP.IsHomogeneous 12 := by
  simpa only [deltaP, map_ofNat] using (((((((pB_homogeneous).pow 2).mul ((pC_homogeneous).pow 2)).sub ((((show (4 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (4 : ℚ)))).mul (pA_homogeneous)).mul ((pC_homogeneous).pow 3))).sub ((((show (4 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (4 : ℚ)))).mul ((pB_homogeneous).pow 3)).mul (pD_homogeneous))).sub ((((show (27 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (27 : ℚ)))).mul ((pA_homogeneous).pow 2)).mul ((pD_homogeneous).pow 2))).add ((((((show (18 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (18 : ℚ)))).mul (pA_homogeneous)).mul (pB_homogeneous)).mul (pC_homogeneous)).mul (pD_homogeneous)))

theorem deltaQ_homogeneous : deltaQ.IsHomogeneous 12 := by
  simpa only [deltaQ, map_ofNat] using (((((((qB_homogeneous).pow 2).mul ((qC_homogeneous).pow 2)).sub ((((show (4 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (4 : ℚ)))).mul (qA_homogeneous)).mul ((qC_homogeneous).pow 3))).sub ((((show (4 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (4 : ℚ)))).mul ((qB_homogeneous).pow 3)).mul (qD_homogeneous))).sub ((((show (27 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (27 : ℚ)))).mul ((qA_homogeneous).pow 2)).mul ((qD_homogeneous).pow 2))).add ((((((show (18 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (18 : ℚ)))).mul (qA_homogeneous)).mul (qB_homogeneous)).mul (qC_homogeneous)).mul (qD_homogeneous)))

theorem TQ_homogeneous : TQ.IsHomogeneous 12 := by
  simpa only [TQ, map_ofNat] using (((((show (3 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (3 : ℚ)))).mul (((((show (2 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (2 : ℚ)))).mul (((qB_homogeneous).pow 2).sub ((((show (3 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (3 : ℚ)))).mul (qA_homogeneous)).mul (qC_homogeneous)))).mul ((Y1_homogeneous).pow 2)).add (((qB_homogeneous).mul (qC_homogeneous)).sub ((((show (9 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (9 : ℚ)))).mul (qA_homogeneous)).mul (qD_homogeneous))))).mul (Q_homogeneous)).sub ((((show (2 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (2 : ℚ)))).mul (HQ_homogeneous)).mul (fpQ_homogeneous)))

theorem KP_homogeneous : KP.IsHomogeneous 12 := by
  simpa only [KP, map_ofNat] using ((((((((pB_homogeneous).mul ((pC_homogeneous).pow 2)).sub ((((show (6 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (6 : ℚ)))).mul ((pB_homogeneous).pow 2)).mul (pD_homogeneous))).add (((((show (9 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (9 : ℚ)))).mul (pA_homogeneous)).mul (pC_homogeneous)).mul (pD_homogeneous))).mul ((X0_homogeneous).pow 2)).add (((show (2 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (2 : ℚ)))).mul ((pC_homogeneous).pow 3))).sub (((((show (9 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (9 : ℚ)))).mul (pB_homogeneous)).mul (pC_homogeneous)).mul (pD_homogeneous))).add ((((show (27 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (27 : ℚ)))).mul (pA_homogeneous)).mul ((pD_homogeneous).pow 2)))

theorem LP_homogeneous : LP.IsHomogeneous 8 := by
  simpa only [LP, map_ofNat] using (((X0_homogeneous).pow 2).mul ((((pB_homogeneous).mul ((X0_homogeneous).pow 4)).add ((((show (2 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (2 : ℚ)))).mul (pC_homogeneous)).mul ((X0_homogeneous).pow 2))).add (((show (3 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (3 : ℚ)))).mul (pD_homogeneous))))

theorem G_homogeneous : G.IsHomogeneous 48 := by
  simpa only [G, map_ofNat] using (((((HP_homogeneous).pow 3).mul (deltaQ_homogeneous)).mul ((Q_homogeneous).pow 2)).sub ((((HQ_homogeneous).pow 3).mul (deltaP_homogeneous)).mul ((P_homogeneous).pow 2)))

theorem U1_homogeneous : U1.IsHomogeneous 42 := by
  simpa only [U1, map_ofNat] using (((((h0P_homogeneous).mul (HP_homogeneous)).mul (HQ_homogeneous)).mul (TQ_homogeneous)).mul (Q_homogeneous))

theorem V_homogeneous : V.IsHomogeneous 48 := by
  simpa only [V, map_ofNat] using ((((KP_homogeneous).mul ((HQ_homogeneous).pow 3)).mul ((P_homogeneous).pow 2)).sub ((((((show (3 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (3 : ℚ)))).mul (deltaQ_homogeneous)).mul ((Q_homogeneous).pow 2)).mul ((HP_homogeneous).pow 2)).mul (LP_homogeneous)))

theorem RP_homogeneous : RP.IsHomogeneous 6 := by
  simpa only [RP, map_ofNat] using ((((show (6 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (6 : ℚ)))).mul (P_homogeneous)).sub ((((show (2 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (2 : ℚ)))).mul ((X0_homogeneous).pow 2)).mul (fpP_homogeneous)))

theorem RQ_homogeneous : RQ.IsHomogeneous 6 := by
  simpa only [RQ, map_ofNat] using ((((show (6 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (6 : ℚ)))).mul (Q_homogeneous)).sub ((((show (2 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (2 : ℚ)))).mul ((Y1_homogeneous).pow 2)).mul (fpQ_homogeneous)))

theorem R0_homogeneous : R0.IsHomogeneous 48 := by
  simpa only [R0, map_ofNat] using ((((P_homogeneous).mul ((HQ_homogeneous).pow 3)).mul (((RP_homogeneous).mul (KP_homogeneous)).sub ((((show (6 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (6 : ℚ)))).mul ((X0_homogeneous).pow 6)).mul (deltaP_homogeneous)))).sub (((((((show (18 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (18 : ℚ)))).mul ((X0_homogeneous).pow 2)).mul (deltaQ_homogeneous)).mul ((Q_homogeneous).pow 2)).mul ((HP_homogeneous).pow 2)).mul ((((X0_homogeneous).pow 2).mul (pC_homogeneous)).add (((show (3 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (3 : ℚ)))).mul (pD_homogeneous)))))

theorem R1_homogeneous : R1.IsHomogeneous 48 := by
  simpa only [R1, map_ofNat] using ((R0_homogeneous).add (((((show (2 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (2 : ℚ)))).mul ((X0_homogeneous).pow 2)).mul (fpQ_homogeneous)).mul (U1_homogeneous)))

theorem D_homogeneous : D.IsHomogeneous 55 := by
  simpa only [D, map_ofNat] using (((((show (36 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (36 : ℚ)))).mul (X0_homogeneous)).mul (Q_homogeneous)).mul (G_homogeneous))

theorem nX1_homogeneous : nX1.IsHomogeneous 56 := by
  simpa only [nX1, map_ofNat] using (((((((show (6 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (6 : ℚ)))).neg).mul (X1_homogeneous)).mul (Y1_homogeneous)).mul (Q_homogeneous)).mul (V_homogeneous))

theorem nX2_homogeneous : nX2.IsHomogeneous 56 := by
  simpa only [nX2, map_ofNat] using ((((X2_homogeneous).mul (Y1_homogeneous)).mul (P_homogeneous)).mul (R1_homogeneous))

theorem nY0_homogeneous : nY0.IsHomogeneous 56 := by
  simpa only [nY0, map_ofNat] using (((((((show (6 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (6 : ℚ)))).neg).mul (Y0_homogeneous)).mul (Y1_homogeneous)).mul (Q_homogeneous)).mul (V_homogeneous))

theorem nY1_homogeneous : nY1.IsHomogeneous 56 := by
  simpa only [nY1, map_ofNat] using ((P_homogeneous).mul ((((Y1_homogeneous).pow 2).mul (R0_homogeneous)).sub ((((X0_homogeneous).pow 2).mul (RQ_homogeneous)).mul (U1_homogeneous))))

theorem nY2_homogeneous : nY2.IsHomogeneous 56 := by
  simpa only [nY2, map_ofNat] using ((((Y2_homogeneous).mul (Y1_homogeneous)).mul (P_homogeneous)).mul (R1_homogeneous))

theorem C_homogeneous : C.IsHomogeneous 104 := by
  simpa only [C, map_ofNat] using ((((((((show (72 : SexticPoly).IsHomogeneous 0 from by simpa only [map_ofNat] using (isHomogeneous_C (σ := Fin 6) (72 : ℚ)))).neg).mul (X0_homogeneous)).mul (Y1_homogeneous)).mul (Q_homogeneous)).mul (G_homogeneous)).mul (R0_homogeneous))

theorem numerator_homogeneous : ∀ i, (N i).IsHomogeneous 56 := by
  intro i
  fin_cases i
  · simpa [N] using (isHomogeneous_zero ℚ (σ := Fin 6) 56)
  · simpa [N] using (nX1_homogeneous)
  · simpa [N] using (nX2_homogeneous)
  · simpa [N] using (nY0_homogeneous)
  · simpa [N] using (nY1_homogeneous)
  · simpa [N] using (nY2_homogeneous)

end HodgeTestbed.ExplicitWitness
