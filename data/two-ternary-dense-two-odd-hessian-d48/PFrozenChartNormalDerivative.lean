import Proposal.PFrozenChartSquareCover

/-! # Exact frozen normal derivative and its weighted identity -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.FrozenChart
open MvPolynomial

/-- All derivatives of the exact H_u, in quotient order (x,r,y,u,z). -/
theorem pderiv_Hu_all (i : Fin 5) : pderiv i (pderiv 3 H) =
    (if i = 1 then 148 * X 1 ^ 3 + 172 * X 1 * X 3 + 94 * X 1 * X 4 ^ 2 else 0) +
    (if i = 3 then 86 * X 1 ^ 2 + 354 * X 3 + 122 * X 4 ^ 2 else 0) +
    (if i = 4 then 94 * X 1 ^ 2 * X 4 + 244 * X 3 * X 4 + 268 * X 4 ^ 3 else 0) := by
  have c37 (i : Fin 5) : pderiv i (37 : Poly 5) = 0 := (pderiv i).map_natCast 37
  have c86 (i : Fin 5) : pderiv i (86 : Poly 5) = 0 := (pderiv i).map_natCast 86
  have c47 (i : Fin 5) : pderiv i (47 : Poly 5) = 0 := (pderiv i).map_natCast 47
  have c177 (i : Fin 5) : pderiv i (177 : Poly 5) = 0 := (pderiv i).map_natCast 177
  have c122 (i : Fin 5) : pderiv i (122 : Poly 5) = 0 := (pderiv i).map_natCast 122
  have c67 (i : Fin 5) : pderiv i (67 : Poly 5) = 0 := (pderiv i).map_natCast 67
  fin_cases i <;>
    norm_num [pderiv_H_u, Derivation.leibniz, Derivation.leibniz_pow,
      smul_eq_mul, Pi.single_apply, Fin.ext_iff, c37, c86, c47, c177, c122, c67] <;> ring

/-- The reviewed weighted degree-four identity for the actual frozen H_u. -/
theorem pderiv_Hu_weighted :
    X 1 * pderiv 1 (pderiv 3 H) + 2 * X 3 * pderiv 3 (pderiv 3 H) +
      X 4 * pderiv 4 (pderiv 3 H) = 4 * pderiv 3 H := by
  rw [pderiv_Hu_all 1, pderiv_Hu_all 3, pderiv_Hu_all 4, pderiv_H_u]
  norm_num [Fin.ext_iff]
  ring

def quotientH : RatFun 5 := embed H
def normalDerivative : RatFun 5 := rationalPartial 3 quotientH

theorem normalDerivative_eq : normalDerivative = embed (pderiv 3 H) := partial_embed 3 H

theorem normalDerivative_ne_zero : normalDerivative ≠ 0 := by
  rw [normalDerivative_eq]
  intro hh
  exact pderiv_H_u_ne_zero (embed_injective (by simpa using hh))

theorem normalDerivative_x : rationalPartial 0 normalDerivative = 0 := by
  rw [normalDerivative_eq, partial_embed]
  norm_num [pderiv_Hu_all, Fin.ext_iff]

theorem normalDerivative_y : rationalPartial 2 normalDerivative = 0 := by
  rw [normalDerivative_eq, partial_embed]
  norm_num [pderiv_Hu_all, Fin.ext_iff]

theorem normalDerivative_weighted :
    coord 1 * rationalPartial 1 normalDerivative +
      2 * coord 3 * rationalPartial 3 normalDerivative +
      coord 4 * rationalPartial 4 normalDerivative = 4 * normalDerivative := by
  have hh := congrArg (embed (n := 5)) pderiv_Hu_weighted
  simpa only [map_add, map_mul, map_ofNat, normalDerivative_eq, partial_embed, coord] using hh

end HodgeTestbed.FrozenChart
