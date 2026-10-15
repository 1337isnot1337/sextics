import Proposal.PFrozenChartNormalDerivative

/-! # The two exact frozen cubic blocks and rational base scalars -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.Incidence

/-- Exact frozen first block in the squared variables (X0²,X1²,Y0²). -/
def P {A : Type*} [CommRing A] (U V W : A) : A :=
  14*U^3 + 7*U^2*V + 21*U^2*W + 23*U*V^2 + 12*U*V*W +
  23*U*W^2 + 4*V^3 + 39*V^2*W + 73*V*W^2 + 8*W^3

/-- Exact frozen second block in (X2²,Y1²,Y2²). -/
def Q {A : Type*} [CommRing A] (U V W : A) : A :=
  31*U^3 + 37*U^2*V + 41*U^2*W + 43*U*V^2 + 47*U*V*W +
  53*U*W^2 + 59*V^3 + 61*V^2*W + 67*V*W^2 + 71*W^3

abbrev K := FrozenChart.RatFun 5
/-- Direction variables have the circuit order (s,i,f,k). The path parameter is separate. -/
abbrev Directions := MvPolynomial (Fin 4) K

def base (j : Fin 5) : Directions := MvPolynomial.C (FrozenChart.coord j)
def baseH : Directions := MvPolynomial.C FrozenChart.quotientH
def Hu : Directions := MvPolynomial.C FrozenChart.normalDerivative
def HuInv : Directions := MvPolynomial.C FrozenChart.normalDerivative⁻¹

theorem Hu_mul_inv : Hu * HuInv = 1 := by
  rw [Hu, HuInv, ← map_mul, mul_inv_cancel₀ FrozenChart.normalDerivative_ne_zero, map_one]

theorem Hu_isUnit : IsUnit Hu := by
  exact isUnit_iff_exists_inv.mpr ⟨HuInv, Hu_mul_inv⟩

/-- The concrete normal derivative in coefficient-ring coordinates. -/
theorem Hu_formula : Hu =
    37 * base 1 ^ 4 + 86 * base 1 ^ 2 * base 3 + 47 * base 1 ^ 2 * base 4 ^ 2 +
    177 * base 3 ^ 2 + 122 * base 3 * base 4 ^ 2 + 67 * base 4 ^ 4 := by
  simp only [Hu, FrozenChart.normalDerivative_eq, FrozenChart.pderiv_H_u,
    map_add, map_mul, map_pow, map_ofNat, base, FrozenChart.coord]

/-- This is the actual frozen quotient, not a free cubic-pair assumption. -/
theorem baseH_formula : baseH = P 1 (base 0 ^ 2) (base 2 ^ 2) +
    Q (base 1 ^ 2) (base 3) (base 4 ^ 2) := by
  simp only [baseH, FrozenChart.quotientH, FrozenChart.H, P, Q, base, FrozenChart.coord,
    map_add, map_mul, map_pow, map_ofNat]
  ring

end HodgeTestbed.Incidence
