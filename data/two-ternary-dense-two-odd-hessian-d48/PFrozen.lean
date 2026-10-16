import Proposal.PCertificate
import Mathlib.Tactic.NormNum

/-!
# Frozen dense sextic and the exact P0 endpoint

Source: `research/mission/pilot-instance.json`, whose variable order is
`X0 X1 X2 Y0 Y1 Y2`. All twenty terms are displayed; coefficients lie in ℚ.
A future witness module can import this file and prove `P0` by explicit data.
No existence theorem for P0 is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeTestbed.Frozen

open MvPolynomial

abbrev X0 : SexticPoly := X 0
abbrev X1 : SexticPoly := X 1
abbrev X2 : SexticPoly := X 2
abbrev Y0 : SexticPoly := X 3
abbrev Y1 : SexticPoly := X 4
abbrev Y2 : SexticPoly := X 5

/-- Exactly the frozen twenty-term sextic, with the monomial order of the instance JSON. -/
def F : SexticPoly :=
  14 * X0^6 +
  7 * X0^4 * X1^2 +
  21 * X0^4 * Y0^2 +
  23 * X0^2 * X1^4 +
  12 * X0^2 * X1^2 * Y0^2 +
  23 * X0^2 * Y0^4 +
  4 * X1^6 +
  39 * X1^4 * Y0^2 +
  73 * X1^2 * Y0^4 +
  31 * X2^6 +
  37 * X2^4 * Y1^2 +
  41 * X2^4 * Y2^2 +
  43 * X2^2 * Y1^4 +
  47 * X2^2 * Y1^2 * Y2^2 +
  53 * X2^2 * Y2^4 +
  8 * Y0^6 +
  59 * Y1^6 +
  61 * Y1^4 * Y2^2 +
  67 * Y1^2 * Y2^4 +
  71 * Y2^6

/-- The selected target, distinct from the elementary Jacobian control. -/
def A : SexticPoly := X0^5 * Y1

/-- The displayed polynomial is a homogeneous sextic. -/
theorem F_homogeneous : F.IsHomogeneous 6 := by
  simpa [F, X0, X1, X2, Y0, Y1, Y2, map_ofNat] using ((((((((((((((((((((((isHomogeneous_X ℚ (0 : Fin 6)).pow 6).C_mul (14 : ℚ)).add
    ((((isHomogeneous_X ℚ (0 : Fin 6)).pow 4).C_mul (7 : ℚ)).mul ((isHomogeneous_X ℚ (1 : Fin 6)).pow 2))).add
    ((((isHomogeneous_X ℚ (0 : Fin 6)).pow 4).C_mul (21 : ℚ)).mul ((isHomogeneous_X ℚ (3 : Fin 6)).pow 2))).add
    ((((isHomogeneous_X ℚ (0 : Fin 6)).pow 2).C_mul (23 : ℚ)).mul ((isHomogeneous_X ℚ (1 : Fin 6)).pow 4))).add
    (((((isHomogeneous_X ℚ (0 : Fin 6)).pow 2).C_mul (12 : ℚ)).mul ((isHomogeneous_X ℚ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℚ (3 : Fin 6)).pow 2))).add
    ((((isHomogeneous_X ℚ (0 : Fin 6)).pow 2).C_mul (23 : ℚ)).mul ((isHomogeneous_X ℚ (3 : Fin 6)).pow 4))).add
    (((isHomogeneous_X ℚ (1 : Fin 6)).pow 6).C_mul (4 : ℚ))).add
    ((((isHomogeneous_X ℚ (1 : Fin 6)).pow 4).C_mul (39 : ℚ)).mul ((isHomogeneous_X ℚ (3 : Fin 6)).pow 2))).add
    ((((isHomogeneous_X ℚ (1 : Fin 6)).pow 2).C_mul (73 : ℚ)).mul ((isHomogeneous_X ℚ (3 : Fin 6)).pow 4))).add
    (((isHomogeneous_X ℚ (2 : Fin 6)).pow 6).C_mul (31 : ℚ))).add
    ((((isHomogeneous_X ℚ (2 : Fin 6)).pow 4).C_mul (37 : ℚ)).mul ((isHomogeneous_X ℚ (4 : Fin 6)).pow 2))).add
    ((((isHomogeneous_X ℚ (2 : Fin 6)).pow 4).C_mul (41 : ℚ)).mul ((isHomogeneous_X ℚ (5 : Fin 6)).pow 2))).add
    ((((isHomogeneous_X ℚ (2 : Fin 6)).pow 2).C_mul (43 : ℚ)).mul ((isHomogeneous_X ℚ (4 : Fin 6)).pow 4))).add
    (((((isHomogeneous_X ℚ (2 : Fin 6)).pow 2).C_mul (47 : ℚ)).mul ((isHomogeneous_X ℚ (4 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℚ (5 : Fin 6)).pow 2))).add
    ((((isHomogeneous_X ℚ (2 : Fin 6)).pow 2).C_mul (53 : ℚ)).mul ((isHomogeneous_X ℚ (5 : Fin 6)).pow 4))).add
    (((isHomogeneous_X ℚ (3 : Fin 6)).pow 6).C_mul (8 : ℚ))).add
    (((isHomogeneous_X ℚ (4 : Fin 6)).pow 6).C_mul (59 : ℚ))).add
    ((((isHomogeneous_X ℚ (4 : Fin 6)).pow 4).C_mul (61 : ℚ)).mul ((isHomogeneous_X ℚ (5 : Fin 6)).pow 2))).add
    ((((isHomogeneous_X ℚ (4 : Fin 6)).pow 2).C_mul (67 : ℚ)).mul ((isHomogeneous_X ℚ (5 : Fin 6)).pow 4))).add
    (((isHomogeneous_X ℚ (5 : Fin 6)).pow 6).C_mul (71 : ℚ)))

theorem A_homogeneous : A.IsHomogeneous 6 := by
  simpa [A, X0, Y1] using
    ((isHomogeneous_X ℚ (0 : Fin 6)).pow 5).mul (isHomogeneous_X ℚ (4 : Fin 6))

theorem F_even : YEven F := by
  norm_num [YEven, reflectY, F, X0, X1, X2, Y0, Y1, Y2]
  ring

theorem A_odd : YOdd A := by
  norm_num [YOdd, reflectY, A, X0, Y1]

/-- The unweakened algebraic endpoint: a positive degree and actual rational polynomial
witnesses satisfying every certificate field. Construction remains open. -/
def P0 : Prop := HasCertificate F A

/-- An explicit witness file may use this introduction theorem without redefining P0. -/
theorem p0_of_certificate (d : ℕ) (D : SexticPoly) (N : Fin 6 → SexticPoly)
    (C : SexticPoly) (h : Certificate F A d D N C) : P0 := ⟨d, D, N, C, h⟩

end HodgeTestbed.Frozen
