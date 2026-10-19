import Proposal.HorizontalFractionDerivation
import Proposal.RationalTarget
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace QuadricContactFractionLift
open MvPolynomial QuadricContactClearing QuadricContactHorizontal

abbrev AP := MvPolynomial (Fin 4) Coeff

/-- Clearing a common denominator cancels its derivative from each cross term. -/
theorem clearing_cross (Δ : Derivation ℚ FunctionField FunctionField)
    (u q n : FunctionField) :
    (u*q)*Δ (u*n)-(u*n)*Δ (u*q) = u^2*(q*Δ n-n*Δ q) := by
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

theorem homogeneous_clearing_divergence
    (D : AP) (N : Fin 4 → AP) (u Q : BasePoly) (P : Fin 4 → BasePoly)
    (hQ : baseMap Q = baseMap u * activeMap D)
    (hP : ∀ i, baseMap (P i) = baseMap u * activeMap (N i))
    (hdiv : D * (∑ i, pderiv i (N i)) = ∑ i, N i * pderiv i D) :
    QuadricContactLift.divergenceCondition Q (P 0) (P 1) (P 2) (P 3) = 0 := by
  let t : Fin 4 → FunctionField := fun i =>
    activeMap D * activeMap (pderiv i (N i)) - activeMap (N i) * activeMap (pderiv i D)
  have ht : ∑ i, t i = 0 := by
    have hh := congrArg activeMap hdiv
    simp only [map_mul, map_sum] at hh
    simp only [t, Finset.sum_sub_distrib, ← Finset.mul_sum, hh, sub_self]
  have hc (i : Fin 4) :
      baseMap Q * horizontal i (baseMap (P i)) -
        baseMap (P i) * horizontal i (baseMap Q) =
      baseMap u^2 * scale i * t i := by
    rw [hQ, hP, clearing_cross, horizontal_activeMap, horizontal_activeMap]
    dsimp [t]
    ring
  apply IsFractionRing.injective BasePoly FunctionField
  rw [map_zero]
  simp only [QuadricContactLift.divergenceCondition, map_add, map_sub, map_mul,
    map_pow, map_ofNat, ← horizontal_map_S, ← horizontal_map_T,
    ← horizontal_map_B, ← horizontal_map_C]
  rw [show baseMap Q * horizontal 0 (baseMap (P 0)) -
      baseMap (P 0) * horizontal 0 (baseMap Q) +
      baseMap Q * horizontal 1 (baseMap (P 1)) -
      baseMap (P 1) * horizontal 1 (baseMap Q) =
      (baseMap Q * horizontal 0 (baseMap (P 0)) -
      baseMap (P 0) * horizontal 0 (baseMap Q)) +
      (baseMap Q * horizontal 1 (baseMap (P 1)) -
      baseMap (P 1) * horizontal 1 (baseMap Q)) by ring]
  rw [hc 0, hc 1, hc 2, hc 3]
  have ht' : t 0 + t 1 + t 2 + t 3 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using ht
  simp only [scale, Matrix.cons_val, QuadricContactLift.clearing, QuadricContactLift.delta,
    map_mul, map_pow, map_sub, coordinate]
  linear_combination
    4 * (baseMap (X 0)^2-baseMap (X 3)^2) * baseMap (X 1)^2 * baseMap (X 2)^2 * baseMap u^2 * ht'

theorem homogeneous_clearing_source
    (D : AP) (N : Fin 4 → AP) (u Q : BasePoly) (P : Fin 4 → BasePoly)
    (hQ : baseMap Q = baseMap u * activeMap D)
    (hP : ∀ i, baseMap (P i) = baseMap u * activeMap (N i))
    (hsrc : (∑ i, N i * pderiv i QuadricContactTarget.cubic) = D * (X 1 * X 2)) :
    QuadricContactLift.source QuadricContactTarget.F (P 0) (P 1) (P 2) (P 3) =
      QuadricContactTarget.A * QuadricContactLift.denominator Q := by
  letI : CharZero FunctionField := Algebra.charZero_of_charZero ℚ FunctionField
  have hd (i : Fin 4) :
      16 * baseMap (polynomialHorizontal i QuadricContactTarget.F) =
        scale i * activeMap (pderiv i QuadricContactTarget.cubic) := by
    have hh := congrArg (horizontal i) QuadricContactTarget.pullback_cubic
    change horizontal i (activeMap QuadricContactTarget.cubic) =
      horizontal i (16 * baseMap QuadricContactTarget.F) at hh
    rw [horizontal_activeMap, Derivation.leibniz, horizontal_map] at hh
    have h16 : horizontal i (16 : FunctionField) = 0 := (horizontal i).map_natCast 16
    simpa only [smul_eq_mul, h16, mul_zero, add_zero] using hh.symm
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  have hd3 := hd 3
  change 16 * baseMap (QuadricContactLift.horizontalS QuadricContactTarget.F) = _ at hd0
  change 16 * baseMap (QuadricContactLift.horizontalT QuadricContactTarget.F) = _ at hd1
  change 16 * baseMap (QuadricContactLift.horizontalB QuadricContactTarget.F) = _ at hd2
  change 16 * baseMap (QuadricContactLift.horizontalC QuadricContactTarget.F) = _ at hd3
  have hs := congrArg activeMap hsrc
  simp only [map_sum, map_mul] at hs
  have hbt : activeMap (X 1) * activeMap (X 2) =
      4 * coordinate 1^2 * coordinate 0 * coordinate 3 := by
    rw [show activeMap = QuadricContactTarget.pullback by rfl]
    simpa only [map_mul] using QuadricContactTarget.pullback_source
  rw [hbt] at hs
  simp [Fin.sum_univ_succ] at hs
  apply IsFractionRing.injective BasePoly FunctionField
  apply (mul_left_cancel₀ (show (16 : FunctionField) ≠ 0 by norm_num))
  simp only [QuadricContactLift.source, QuadricContactLift.denominator,
    QuadricContactLift.clearing, QuadricContactLift.delta, QuadricContactTarget.A,
    map_add, map_sub, map_mul, map_pow, map_ofNat, hQ, hP]
  simp only [scale, Matrix.cons_val, coordinate] at hd0 hd1 hd2 hd3 hs
  linear_combination
    baseMap (X 1)^2 * baseMap (X 2)^2 * baseMap u * activeMap (N 0) * hd0 +
    baseMap (X 1)^2 * baseMap (X 2)^2 * baseMap u * activeMap (N 1) * hd1 +
    2 * (baseMap (X 0)^2-baseMap (X 3)^2) * baseMap (X 2)^2 * baseMap u * activeMap (N 2) * hd2 +
    2 * (baseMap (X 0)^2-baseMap (X 3)^2) * baseMap (X 1)^2 * baseMap u * activeMap (N 3) * hd3 +
    4 * (baseMap (X 0)^2-baseMap (X 3)^2) * baseMap (X 1)^2 * baseMap (X 2)^2 * baseMap u * hs

end QuadricContactFractionLift

#print axioms QuadricContactFractionLift.homogeneous_clearing_divergence
#print axioms QuadricContactFractionLift.homogeneous_clearing_source
