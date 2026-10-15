import Proposal.PFrozen
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! # Actual frozen quotient polynomial and square cover -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.FrozenChart
open MvPolynomial

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℚ

/-- Quotient coordinates are (x,r,y,u,z), with u replacing Y1² on X0=1. -/
def H : Poly 5 :=
  14 + 7 * X 0 ^ 2 + 21 * X 2 ^ 2 + 23 * X 0 ^ 4 +
  12 * X 0 ^ 2 * X 2 ^ 2 + 23 * X 2 ^ 4 + 4 * X 0 ^ 6 +
  39 * X 0 ^ 4 * X 2 ^ 2 + 73 * X 0 ^ 2 * X 2 ^ 4 +
  31 * X 1 ^ 6 + 37 * X 1 ^ 4 * X 3 + 41 * X 1 ^ 4 * X 4 ^ 2 +
  43 * X 1 ^ 2 * X 3 ^ 2 + 47 * X 1 ^ 2 * X 3 * X 4 ^ 2 +
  53 * X 1 ^ 2 * X 4 ^ 4 + 8 * X 2 ^ 6 + 59 * X 3 ^ 3 +
  61 * X 3 ^ 2 * X 4 ^ 2 + 67 * X 3 * X 4 ^ 4 + 71 * X 4 ^ 6

/-- Actual polynomial square-cover substitution u=t². -/
def squareCoverPoly : Poly 5 →ₐ[ℚ] Poly 5 :=
  aeval (fun i => if i = 3 then X 3 ^ 2 else X i)

/-- Set X0=1 with affine order (X1,X2,Y0,Y1,Y2). -/
def dehomogenize : Poly 6 →ₐ[ℚ] Poly 5 := aeval (Fin.cases 1 X)

/-- The quotient polynomial really is the square-cover quotient of frozen F. -/
theorem dehomogenize_F : dehomogenize Frozen.F = squareCoverPoly H := by
  have h1 : Fin.cases (1 : Poly 5) X (1 : Fin 6) = X (0 : Fin 5) := rfl
  have h2 : Fin.cases (1 : Poly 5) X (2 : Fin 6) = X (1 : Fin 5) := rfl
  have h3 : Fin.cases (1 : Poly 5) X (3 : Fin 6) = X (2 : Fin 5) := rfl
  have h4 : Fin.cases (1 : Poly 5) X (4 : Fin 6) = X (3 : Fin 5) := rfl
  have h5 : Fin.cases (1 : Poly 5) X (5 : Fin 6) = X (4 : Fin 5) := rfl

  norm_num [dehomogenize, squareCoverPoly, Frozen.F, Frozen.X0, Frozen.X1,
    Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2, H, Fin.ext_iff, h1, h2, h3, h4, h5]
  ring

/-- The actual selected frozen target becomes the cover coordinate t. -/
theorem dehomogenize_A : dehomogenize Frozen.A = X 3 := by
  have h1 : Fin.cases (1 : Poly 5) X (1 : Fin 6) = X (0 : Fin 5) := rfl
  have h2 : Fin.cases (1 : Poly 5) X (2 : Fin 6) = X (1 : Fin 5) := rfl
  have h3 : Fin.cases (1 : Poly 5) X (3 : Fin 6) = X (2 : Fin 5) := rfl
  have h4 : Fin.cases (1 : Poly 5) X (4 : Fin 6) = X (3 : Fin 5) := rfl
  have h5 : Fin.cases (1 : Poly 5) X (5 : Fin 6) = X (4 : Fin 5) := rfl

  norm_num [dehomogenize, Frozen.A, Frozen.X0, Frozen.Y1, h4]

/-- The exact normal derivative, including every mixed term. -/
theorem pderiv_H_u : pderiv 3 H =
    37 * X 1 ^ 4 + 86 * X 1 ^ 2 * X 3 + 47 * X 1 ^ 2 * X 4 ^ 2 +
    177 * X 3 ^ 2 + 122 * X 3 * X 4 ^ 2 + 67 * X 4 ^ 4 := by
  have c14 : pderiv (3 : Fin 5) (14 : Poly 5) = 0 := (pderiv 3).map_natCast 14
  have c7 : pderiv (3 : Fin 5) (7 : Poly 5) = 0 := (pderiv 3).map_natCast 7
  have c21 : pderiv (3 : Fin 5) (21 : Poly 5) = 0 := (pderiv 3).map_natCast 21
  have c23 : pderiv (3 : Fin 5) (23 : Poly 5) = 0 := (pderiv 3).map_natCast 23
  have c12 : pderiv (3 : Fin 5) (12 : Poly 5) = 0 := (pderiv 3).map_natCast 12
  have c4 : pderiv (3 : Fin 5) (4 : Poly 5) = 0 := (pderiv 3).map_natCast 4
  have c39 : pderiv (3 : Fin 5) (39 : Poly 5) = 0 := (pderiv 3).map_natCast 39
  have c73 : pderiv (3 : Fin 5) (73 : Poly 5) = 0 := (pderiv 3).map_natCast 73
  have c31 : pderiv (3 : Fin 5) (31 : Poly 5) = 0 := (pderiv 3).map_natCast 31
  have c37 : pderiv (3 : Fin 5) (37 : Poly 5) = 0 := (pderiv 3).map_natCast 37
  have c41 : pderiv (3 : Fin 5) (41 : Poly 5) = 0 := (pderiv 3).map_natCast 41
  have c43 : pderiv (3 : Fin 5) (43 : Poly 5) = 0 := (pderiv 3).map_natCast 43
  have c47 : pderiv (3 : Fin 5) (47 : Poly 5) = 0 := (pderiv 3).map_natCast 47
  have c53 : pderiv (3 : Fin 5) (53 : Poly 5) = 0 := (pderiv 3).map_natCast 53
  have c8 : pderiv (3 : Fin 5) (8 : Poly 5) = 0 := (pderiv 3).map_natCast 8
  have c59 : pderiv (3 : Fin 5) (59 : Poly 5) = 0 := (pderiv 3).map_natCast 59
  have c61 : pderiv (3 : Fin 5) (61 : Poly 5) = 0 := (pderiv 3).map_natCast 61
  have c67 : pderiv (3 : Fin 5) (67 : Poly 5) = 0 := (pderiv 3).map_natCast 67
  have c71 : pderiv (3 : Fin 5) (71 : Poly 5) = 0 := (pderiv 3).map_natCast 71
  norm_num [H, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, Pi.single_apply, Fin.ext_iff, c14, c7, c21, c23, c12, c4, c39, c73, c31, c37, c41, c43, c47, c53, c8, c59, c61, c67, c71]
  ring

/-- H_u is nonzero over QQ, proved at the rational point (0,0,0,1,0). -/
theorem pderiv_H_u_ne_zero : pderiv 3 H ≠ 0 := by
  intro hh
  have he := congrArg (eval (fun i : Fin 5 => if i = 3 then (1 : ℚ) else 0)) hh
  rw [pderiv_H_u] at he
  norm_num [Fin.ext_iff] at he

end HodgeTestbed.FrozenChart
