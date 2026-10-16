import Proposal.PEllipticAmbientCovariantScaling
import Proposal.PEllipticAmbientCompactPhysical
import Proposal.PEllipticAmbientPolynomialBridge

/-! The two protected equations for the exact published degree55 polynomial tuple. -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart HodgeTestbed.Conic

theorem homSplit_lambda : homSplit lambda = coord (4 : Fin 6)/coord 0 := by
  simp only [lambda, homSplit_coord, homCoordinates, Matrix.cons_val_four]
  rfl
theorem homSplit_p : homSplit p = embed ExplicitWitness.P/coord (0 : Fin 6)^6 := by
  rw [← baseEmbedding_p, fourP_cubic, ← homBase_apply, hom_P]
theorem homSplit_q : homSplit q = embed ExplicitWitness.Q/coord (4 : Fin 6)^6 := by
  rw [← baseEmbedding_q, fourQ_cubic, ← homBase_apply, hom_Q]

theorem embedded_Q_ne_zero : embed ExplicitWitness.Q ≠ 0 := by
  have hh : homBase (Cubic.f qc) ≠ 0 := (map_ne_zero homBase).mpr actualQ_ne_zero
  rw [hom_Q] at hh
  intro hz
  simp [hz] at hh
theorem embedded_G_ne_zero : embed ExplicitWitness.G ≠ 0 := by
  have hh : homBase (Cubic.G pc qc) ≠ 0 := (map_ne_zero homBase).mpr actualG_ne_zero
  rw [hom_G] at hh
  intro hz
  simp [hz] at hh

theorem actual_polynomial_denominator_ne_zero : ExplicitWitness.D ≠ 0 := by
  intro hz
  have hh := congrArg (embed (n := 6)) hz
  simp only [ExplicitWitness.D, map_mul, map_ofNat, Frozen.X0, embed_X, map_zero] at hh
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (coord_ne_zero 0))
    embedded_Q_ne_zero) embedded_G_ne_zero) hh

def actualHomogeneous : Fin 6 → K6 :=
  homogenizedField homSplit.toRingHom (coord 0) actualPhysical

theorem actualHomogeneous_ratios_succ (i : Fin 5) :
    coord (0 : Fin 6)*homSplit (actualPhysical i) = embed (ExplicitWitness.N i.succ)/embed ExplicitWitness.D := by
  fin_cases i <;>
    norm_num [actualPhysical_compact, compactNormal, compactQfactor,
      map_mul, map_add, map_sub, map_pow, map_div₀, map_neg, map_ofNat,
      ← homBase_apply, hom_P, hom_G, hom_R0, hom_U1, hom_RQ, hom_fpQ, hom_V,
      homSplit_lambda, homSplit_q, homSplit_coord,
      ExplicitWitness.N, ExplicitWitness.D, ExplicitWitness.nX1, ExplicitWitness.nX2,
      ExplicitWitness.nY0, ExplicitWitness.nY1, ExplicitWitness.nY2, ExplicitWitness.R1,
      Frozen.X0, Frozen.X1, Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2, embed_X,
      homCoordinates, Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  all_goals norm_num [homCoordinates, Matrix.cons_val_succ, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6),
    embedded_Q_ne_zero, embedded_G_ne_zero]
  all_goals ring

theorem actualHomogeneous_ratios (i : Fin 6) :
    actualHomogeneous i = embed (ExplicitWitness.N i)/embed ExplicitWitness.D := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [actualHomogeneous, homogenizedField, ExplicitWitness.N]
  · exact actualHomogeneous_ratios_succ j

theorem actualHomogeneous_first :
    fieldAction rationalPartial actualHomogeneous (embed Frozen.F) = embed Frozen.A := by
  rw [frozen_F_homSplit, frozen_A_homSplit]
  change fieldAction rationalPartial
    (homogenizedField homSplit.toRingHom (coord 0) actualPhysical)
    (coord (0 : Fin 6)^6*homSplit splitF) = _
  have hh := actual_physical_equations.1
  rw [frozen_F_split, frozen_A_split] at hh
  calc
    _ = coord (0 : Fin 6)^6*homSplit (fieldAction physicalPartial actualPhysical splitF) :=
      homogenizedField_contraction physicalPartial rationalPartial homSplit.toRingHom
        (coord 0) physicalCoordinates actualPhysical actual_split_homogeneousChart splitF
    _ = _ := by rw [hh]

theorem actualHomogeneous_divergence :
    fieldDivergence rationalPartial actualHomogeneous =
      embed Frozen.F*embed ExplicitWitness.C/(embed ExplicitWitness.D)^2 := by
  rw [actualHomogeneous, homogenizedField_divergence physicalPartial rationalPartial homSplit.toRingHom
    (coord 0) physicalCoordinates actualPhysical actual_split_homogeneousChart,
    actual_divergence_compact]
  change homSplit (-splitF*baseEmbedding (Cubic.R0 pc qc)/
    (18*q*lambda^5*baseEmbedding (Cubic.G pc qc))) = _
  have hf : homSplit splitF = embed Frozen.F/coord (0 : Fin 6)^6 := by
    rw [frozen_F_homSplit]
    field_simp [coord_ne_zero (0 : Fin 6)]
  simp only [map_div₀, map_mul, map_neg, map_pow, map_ofNat, ← homBase_apply,
    hom_R0, hom_G, homSplit_q, homSplit_lambda, hf, ExplicitWitness.C, ExplicitWitness.D,
    Frozen.X0, Frozen.Y1, embed_X]
  field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6),
    embedded_Q_ne_zero, embedded_G_ne_zero]
  <;> ring

/-- Exact E1 and E2 for the same compact polynomial tuple as the accepted sparse packet.
Every scalar, coordinate and derivative premise has been discharged above. -/
theorem actual_equations :
    Equations Frozen.F Frozen.A ExplicitWitness.D ExplicitWitness.N ExplicitWitness.C :=
  equations_of_rational_field ExplicitWitness.D Frozen.F ExplicitWitness.N Frozen.A ExplicitWitness.C
    actual_polynomial_denominator_ne_zero actualHomogeneous actualHomogeneous_ratios
    actualHomogeneous_first actualHomogeneous_divergence

end HodgeTestbed.EllipticAmbient
