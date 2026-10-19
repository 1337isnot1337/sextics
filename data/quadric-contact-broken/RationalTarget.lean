import Proposal.HomogeneousSubstitution
import Proposal.ParameterSpecialization
import Proposal.ConcreteLine
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace QuadricContactTarget
open MvPolynomial QuadricContactClearing

def F : BasePoly :=
  X 0 ^ 6 + X 3 ^ 6 + 5 * X 0 ^ 4 * X 3 ^ 2 + 5 * X 0 ^ 2 * X 3 ^ 4 +
  5 * (X 0 ^ 2 + X 3 ^ 2) *
    (X 1 ^ 2 * X 4 ^ 2 + X 1 * X 2 * X 4 * X 5 + X 2 ^ 2 * X 5 ^ 2) +
  X 1 ^ 6 + X 4 ^ 6 + X 2 ^ 6 + X 5 ^ 6 +
  C (5 / 7 : ℚ) * X 0 * X 3 * X 1 * X 4 * (X 2 ^ 2 + 2 * X 5 ^ 2)

def A : BasePoly := X 1^2 * X 0 * X 3 * (X 0^2-X 3^2)

def activeCoordinates : Fin 4 → FunctionField :=
  ![2*(coordinate 0^2+coordinate 3^2), 4*coordinate 0*coordinate 3,
    coordinate 1^2, coordinate 2^2]

def pullback : MvPolynomial (Fin 4) ParameterSpecialization.Coefficients →+* FunctionField :=
  eval₂Hom regularParameterMap activeCoordinates

@[simp] theorem pullback_C (r : ParameterSpecialization.Coefficients) :
    pullback (C r) = regularParameterMap r := by
  exact eval₂_C _ _ r

@[simp] theorem pullback_X (i : Fin 4) : pullback (X i) = activeCoordinates i := by
  exact eval₂_X _ _ i

def cubic : MvPolynomial (Fin 4) ParameterSpecialization.Coefficients :=
  QuadricContact.ConcreteLine.cubic ParameterSpecialization.p ParameterSpecialization.q
    ParameterSpecialization.s ParameterSpecialization.k ParameterSpecialization.u
    ParameterSpecialization.v

@[simp] theorem parameter_alpha : regularParameterMap ParameterSpecialization.alpha =
    coordinate 4 / coordinate 1 := by
  change regularParameterMap (algebraMap Parameters _ (X 0)) = _
  rw [regularParameterMap_algebraMap]
  simp [parameterMap]

@[simp] theorem parameter_beta : regularParameterMap ParameterSpecialization.beta =
    coordinate 5 / coordinate 2 := by
  change regularParameterMap (algebraMap Parameters _ (X 1)) = _
  rw [regularParameterMap_algebraMap]
  simp [parameterMap]

@[simp] theorem parameter_scalar (r : ℚ) :
    regularParameterMap (ParameterSpecialization.scalar r) = algebraMap ℚ FunctionField r := by
  change regularParameterMap (algebraMap Parameters _ (C r)) = _
  rw [regularParameterMap_algebraMap]
  simp [parameterMap]

@[simp] theorem baseMap_C (r : ℚ) :
    baseMap (C r) = algebraMap ℚ FunctionField r := by
  change algebraMap BasePoly FunctionField (C r) = _
  rw [MvPolynomial.C_eq_algebraMap]
  exact (IsScalarTower.algebraMap_apply ℚ BasePoly FunctionField r).symm

/-- Exact composition with the protected six-variable sextic. -/
theorem pullback_cubic : pullback cubic = 16 * baseMap F := by
  simp only [cubic, QuadricContact.ConcreteLine.cubic,
    pullback_C, pullback_X, map_add, map_mul, map_pow,
    ParameterSpecialization.p, ParameterSpecialization.q, ParameterSpecialization.s,
    ParameterSpecialization.k, ParameterSpecialization.u, ParameterSpecialization.v,
    map_ofNat, map_one, parameter_alpha, parameter_beta, parameter_scalar]
  simp only [activeCoordinates, Matrix.cons_val_zero, Matrix.cons_val_succ,
    F, map_add, map_mul, map_pow, map_ofNat, baseMap_C]
  norm_num [Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at ⊢
  change _ = 16 * (coordinate 0^6+coordinate 3^6+
    5*coordinate 0^4*coordinate 3^2+5*coordinate 0^2*coordinate 3^4+
    5*(coordinate 0^2+coordinate 3^2)*
      (coordinate 1^2*coordinate 4^2+coordinate 1*coordinate 2*coordinate 4*coordinate 5+
        coordinate 2^2*coordinate 5^2)+
    coordinate 1^6+coordinate 4^6+coordinate 2^6+coordinate 5^6+
    (5/7)*coordinate 0*coordinate 3*coordinate 1*coordinate 4*
      (coordinate 2^2+2*coordinate 5^2))
  norm_num
  field_simp [coordinate_ne_zero 1, coordinate_ne_zero 2]
  <;> ring

theorem pullback_source :
    pullback (X 1 * X 2) = 4 * coordinate 1^2 * coordinate 0 * coordinate 3 := by
  simp only [map_mul, pullback_X, activeCoordinates,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num [Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

end QuadricContactTarget

#print axioms QuadricContactTarget.pullback_cubic
