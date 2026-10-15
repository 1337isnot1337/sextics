import Proposal.PEllipticAmbientAmbient
import Proposal.PIncidenceBlocks
import Proposal.PFrozenChartCompatibility
import Mathlib.Tactic.LinearCombination

/-! # The actual frozen split chart (x,y,r,z,λ)

P and Q below are the pinned cubic blocks in squared variables. No additional
squaring of a sextic block occurs. All partials are the previously constructed
rational partial derivations on QQ(x,y,r,z,λ).
-/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart HodgeTestbed.Incidence
open MvPolynomial

abbrev K := RatFun 5
abbrev basePartial (i : Fin 4) : Derivation ℚ K K := rationalPartial i.castSucc
abbrev normalPartial : Derivation ℚ K K := rationalPartial 4

def lambda : K := coord 4
def pPoly : Poly 5 := P 1 (X 0 ^ 2) (X 1 ^ 2)
def qPoly : Poly 5 := Q (X 2 ^ 2) 1 (X 3 ^ 2)
def p : K := embed pPoly
def q : K := embed qPoly
def splitF : K := p + lambda ^ 6 * q
def h : K := 6 * lambda ^ 5 * q
def density : K := lambda ^ 2

/-- Exact p, with the first frozen cubic block evaluated at (1,x²,y²). -/
theorem p_formula : p = P 1 (coord 0 ^ 2) (coord 1 ^ 2) := by
  simp only [p, pPoly, P, map_add, map_mul, map_pow, map_ofNat, map_one, coord]
theorem q_formula : q = Q (coord 2 ^ 2) 1 (coord 3 ^ 2) := by
  simp only [q, qPoly, Q, map_add, map_mul, map_pow, map_ofNat, map_one, coord]

theorem lambda_ne_zero : lambda ≠ 0 := by
  intro hz
  have hx : (X (4 : Fin 5) : Poly 5) = 0 := (IsFractionRing.injective (Poly 5) K) (hz.trans (map_zero _).symm)
  exact X_ne_zero 4 hx

theorem p_ne_zero : p ≠ 0 := by
  intro hz
  have hp : pPoly = 0 := (IsFractionRing.injective (Poly 5) K) (hz.trans (map_zero _).symm)
  have he := congrArg (eval (fun _ : Fin 5 => (0 : ℚ))) hp
  norm_num [pPoly, P] at he
  have hc : constantCoeff (14 : Poly 5) = (14 : ℚ) := map_natCast constantCoeff 14
  rw [hc] at he
  norm_num at he

theorem q_ne_zero : q ≠ 0 := by
  intro hz
  have hq : qPoly = 0 := (IsFractionRing.injective (Poly 5) K) (hz.trans (map_zero _).symm)
  have he := congrArg (eval (fun _ : Fin 5 => (0 : ℚ))) hq
  norm_num [qPoly, Q] at he
  have hc : constantCoeff (59 : Poly 5) = (59 : ℚ) := map_natCast constantCoeff 59
  rw [hc] at he
  norm_num at he

@[simp] theorem normal_lambda : normalPartial lambda = 1 := by simp [lambda]
@[simp] theorem base_lambda (i : Fin 4) : basePartial i lambda = 0 := by
  simp only [lambda, partial_coord]
  split_ifs with he
  · have : i.val = 4 := congrArg Fin.val he
    omega
  · rfl

/-- The two frozen blocks are independent of the normal coordinate. -/
@[simp] theorem normal_p : normalPartial p = 0 := by
  rw [p, partial_embed]
  have c14 : pderiv (4 : Fin 5) (14 : Poly 5) = 0 := (pderiv 4).map_natCast 14
  have c7 : pderiv (4 : Fin 5) (7 : Poly 5) = 0 := (pderiv 4).map_natCast 7
  have c21 : pderiv (4 : Fin 5) (21 : Poly 5) = 0 := (pderiv 4).map_natCast 21
  have c23 : pderiv (4 : Fin 5) (23 : Poly 5) = 0 := (pderiv 4).map_natCast 23
  have c12 : pderiv (4 : Fin 5) (12 : Poly 5) = 0 := (pderiv 4).map_natCast 12
  have c4 : pderiv (4 : Fin 5) (4 : Poly 5) = 0 := (pderiv 4).map_natCast 4
  have c39 : pderiv (4 : Fin 5) (39 : Poly 5) = 0 := (pderiv 4).map_natCast 39
  have c73 : pderiv (4 : Fin 5) (73 : Poly 5) = 0 := (pderiv 4).map_natCast 73
  have c8 : pderiv (4 : Fin 5) (8 : Poly 5) = 0 := (pderiv 4).map_natCast 8
  simp [pPoly, P, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    Pi.single_apply, Fin.ext_iff, c14, c7, c21, c23, c12, c4, c39, c73, c8]
@[simp] theorem normal_q : normalPartial q = 0 := by
  rw [q, partial_embed]
  have c31 : pderiv (4 : Fin 5) (31 : Poly 5) = 0 := (pderiv 4).map_natCast 31
  have c37 : pderiv (4 : Fin 5) (37 : Poly 5) = 0 := (pderiv 4).map_natCast 37
  have c41 : pderiv (4 : Fin 5) (41 : Poly 5) = 0 := (pderiv 4).map_natCast 41
  have c43 : pderiv (4 : Fin 5) (43 : Poly 5) = 0 := (pderiv 4).map_natCast 43
  have c47 : pderiv (4 : Fin 5) (47 : Poly 5) = 0 := (pderiv 4).map_natCast 47
  have c53 : pderiv (4 : Fin 5) (53 : Poly 5) = 0 := (pderiv 4).map_natCast 53
  have c59 : pderiv (4 : Fin 5) (59 : Poly 5) = 0 := (pderiv 4).map_natCast 59
  have c61 : pderiv (4 : Fin 5) (61 : Poly 5) = 0 := (pderiv 4).map_natCast 61
  have c67 : pderiv (4 : Fin 5) (67 : Poly 5) = 0 := (pderiv 4).map_natCast 67
  have c71 : pderiv (4 : Fin 5) (71 : Poly 5) = 0 := (pderiv 4).map_natCast 71
  simp [qPoly, Q, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    Pi.single_apply, Fin.ext_iff, c31, c37, c41, c43, c47, c53, c59, c61, c67, c71]

@[simp] theorem normal_splitF : normalPartial splitF = h := by
  simp [splitF, h, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul]
  ring

theorem base_splitF (i : Fin 4) : basePartial i splitF =
    basePartial i p + lambda ^ 6 * basePartial i q := by
  simp [splitF, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul]

theorem h_ne_zero : h ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ lambda_ne_zero)) q_ne_zero
theorem density_ne_zero : density ≠ 0 := pow_ne_zero _ lambda_ne_zero

/-- Substitution from homogeneous frozen variables in their protected order:
(X0,X1,X2,Y0,Y1,Y2) ↦ (1,x,λr,y,λ,λz). -/
def splitSubstitution : Poly 6 →ₐ[ℚ] K :=
  aeval ![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3]

theorem frozen_F_split : splitSubstitution Frozen.F = splitF := by
  have hv0 : (![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3] : Fin 6 → K) 0 = 1 := rfl
  have hv1 : (![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3] : Fin 6 → K) 1 = coord 0 := rfl
  have hv2 : (![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3] : Fin 6 → K) 2 = lambda * coord 2 := rfl
  have hv3 : (![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3] : Fin 6 → K) 3 = coord 1 := rfl
  have hv4 : (![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3] : Fin 6 → K) 4 = lambda := rfl
  have hv5 : (![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3] : Fin 6 → K) 5 = lambda * coord 3 := rfl
  rw [splitF, p_formula, q_formula]
  norm_num [splitSubstitution, Frozen.F, Frozen.X0, Frozen.X1, Frozen.X2,
    Frozen.Y0, Frozen.Y1, Frozen.Y2, P, Q, Matrix.cons_val_succ, hv0, hv1, hv2, hv3, hv4, hv5]
  ring

theorem frozen_A_split : splitSubstitution Frozen.A = lambda := by
  have hv0 : (![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3] : Fin 6 → K) 0 = 1 := rfl
  have hv1 : (![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3] : Fin 6 → K) 1 = coord 0 := rfl
  have hv2 : (![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3] : Fin 6 → K) 2 = lambda * coord 2 := rfl
  have hv3 : (![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3] : Fin 6 → K) 3 = coord 1 := rfl
  have hv4 : (![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3] : Fin 6 → K) 4 = lambda := rfl
  have hv5 : (![1, coord 0, lambda * coord 2, coord 1, lambda, lambda * coord 3] : Fin 6 → K) 5 = lambda * coord 3 := rfl
  norm_num [splitSubstitution, Frozen.A, Frozen.X0, Frozen.Y1, Matrix.cons_val_succ, hv0, hv1, hv2, hv3, hv4, hv5]

/-- The residue density in this actual split chart. -/
theorem residue_density : normalPartial (density * lambda / h) / h =
    -1 / (18 * lambda ^ 8 * q ^ 2) := by
  have c6 : normalPartial (6 : K) = 0 := normalPartial.map_natCast 6
  simp only [density, h, Derivation.leibniz_div, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, normal_lambda, normal_q, c6]
  norm_num
  field_simp [lambda_ne_zero, q_ne_zero]
  <;> ring

end HodgeTestbed.EllipticAmbient
