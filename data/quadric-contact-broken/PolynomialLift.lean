import HodgeTestbed.Algebra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
The actual polynomial lift of a four-component cubic field.

All derivatives below are `MvPolynomial.pderiv` in the original six variables.
The theorem `lift_strict_equations` performs all derivative calculations, including
the cancellation introduced by clearing a²c². It deliberately leaves the two
downstairs source and divergence equations explicit; these must be supplied by
the generic cubic construction.
-/

noncomputable section
namespace QuadricContactLift
open MvPolynomial HodgeTestbed

variable {R : Type*} [CommRing R]
abbrev Poly := MvPolynomial (Fin 6) R

def delta : Poly (R := R) := X 0 ^ 2 - X 3 ^ 2
def clearing : Poly (R := R) := X 1 ^ 2 * X 2 ^ 2

def horizontalS (P : Poly (R := R)) : Poly (R := R) :=
  X 0 * pderiv 0 P - X 3 * pderiv 3 P
def horizontalT (P : Poly (R := R)) : Poly (R := R) :=
  -X 3 * pderiv 0 P + X 0 * pderiv 3 P
def horizontalB (P : Poly (R := R)) : Poly (R := R) :=
  X 1 * pderiv 1 P + X 4 * pderiv 4 P
def horizontalC (P : Poly (R := R)) : Poly (R := R) :=
  X 2 * pderiv 2 P + X 5 * pderiv 5 P

def denominator (Q : Poly (R := R)) : Poly (R := R) := clearing * Q

def numerators (PS PT PB PC : Poly (R := R)) : Fin 6 → Poly (R := R) :=
  ![clearing * (X 0 * PS - X 3 * PT),
    2 * delta * X 1 * X 2 ^ 2 * PB,
    2 * delta * X 2 * X 1 ^ 2 * PC,
    clearing * (-X 3 * PS + X 0 * PT),
    2 * delta * X 4 * X 2 ^ 2 * PB,
    2 * delta * X 5 * X 1 ^ 2 * PC]

def source (F PS PT PB PC : Poly (R := R)) : Poly (R := R) :=
  clearing * (PS * horizontalS F + PT * horizontalT F) +
    2 * delta * X 2 ^ 2 * PB * horizontalB F +
    2 * delta * X 1 ^ 2 * PC * horizontalC F

def divergenceCondition (Q PS PT PB PC : Poly (R := R)) : Poly (R := R) :=
  clearing * (Q * horizontalS PS - PS * horizontalS Q +
    Q * horizontalT PT - PT * horizontalT Q) +
    2 * delta * X 2 ^ 2 * (Q * horizontalB PB - PB * horizontalB Q) +
    2 * delta * X 1 ^ 2 * (Q * horizontalC PC - PC * horizontalC Q)

theorem lift_directional (F PS PT PB PC : Poly (R := R)) :
    directional F (numerators PS PT PB PC) = source F PS PT PB PC := by
  simp only [directional, Fin.sum_univ_six, numerators, Matrix.cons_val,
    source, horizontalS, horizontalT, horizontalB, horizontalC]
  ring

theorem lift_divergence_numerator (Q PS PT PB PC : Poly (R := R)) :
    divergenceNumerator (denominator Q) (numerators PS PT PB PC) =
      clearing * divergenceCondition Q PS PT PB PC := by
  have htwo (i : Fin 6) : pderiv i (2 : Poly (R := R)) = 0 :=
    (pderiv i).map_natCast 2
  simp only [divergenceNumerator, divergence, directional, Fin.sum_univ_six,
    numerators, Matrix.cons_val, denominator, clearing, delta,
    divergenceCondition, horizontalS, horizontalT, horizontalB, horizontalC]
  simp only [map_add, map_sub, map_neg, pderiv_mul, pderiv_pow,
    pderiv_X, Pi.single_apply, htwo, Fin.isValue]
  norm_num [Fin.ext_iff]
  ring

/-- A complete polynomial-calculus bridge. No scalar symbols stand in for
derivatives: the source and divergence assumptions use actual pderiv expressions. -/
theorem lift_strict_equations
    (F A Q PS PT PB PC : Poly (R := R))
    (hsource : source F PS PT PB PC = A * denominator Q)
    (hdiv : divergenceCondition Q PS PT PB PC = 0) :
    Equations F A (denominator Q) (numerators PS PT PB PC) 0 := by
  apply strict_to_equations
  · exact (lift_directional F PS PT PB PC).trans hsource
  · rw [lift_divergence_numerator, hdiv, mul_zero]

theorem lift_cleared_defect
    (F A Q PS PT PB PC : Poly (R := R))
    (hsource : source F PS PT PB PC = A * denominator Q)
    (hdiv : divergenceCondition Q PS PT PB PC = 0) :
    clearedDefect F A (denominator Q) (numerators PS PT PB PC) = 0 := by
  simpa using (lift_strict_equations F A Q PS PT PB PC hsource hdiv).clearedDefect_eq

theorem delta_homogeneous : (delta (R := R)).IsHomogeneous 2 := by
  exact (isHomogeneous_X_pow 0 2).sub (isHomogeneous_X_pow 3 2)

theorem clearing_homogeneous : (clearing (R := R)).IsHomogeneous 4 := by
  exact (isHomogeneous_X_pow 1 2).mul (isHomogeneous_X_pow 2 2)

theorem denominator_homogeneous {Q : Poly (R := R)} {h : ℕ}
    (hQ : Q.IsHomogeneous h) : (denominator Q).IsHomogeneous (h + 4) := by
  simpa only [denominator, Nat.add_comm] using clearing_homogeneous.mul hQ

theorem numerators_homogeneous {PS PT PB PC : Poly (R := R)} {h : ℕ}
    (hS : PS.IsHomogeneous h) (hT : PT.IsHomogeneous h)
    (hB : PB.IsHomogeneous h) (hC : PC.IsHomogeneous h) :
    ∀ i, (numerators PS PT PB PC i).IsHomogeneous (h + 5) := by
  have hs := clearing_homogeneous.mul
    (((isHomogeneous_X R 0).mul hS).sub ((isHomogeneous_X R 3).mul hT))
  have ht := clearing_homogeneous.mul
    ((((isHomogeneous_X R 3).neg).mul hS).add ((isHomogeneous_X R 0).mul hT))
  have hb (i : Fin 6) :=
    (((delta_homogeneous.C_mul (2 : R)).mul (isHomogeneous_X R i)).mul
      (isHomogeneous_X_pow 2 2)).mul hB
  have hc (i : Fin 6) :=
    (((delta_homogeneous.C_mul (2 : R)).mul (isHomogeneous_X R i)).mul
      (isHomogeneous_X_pow 1 2)).mul hC
  intro i
  fin_cases i
  · simpa [numerators, map_ofNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs
  · simpa [numerators, map_ofNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hb 1
  · simpa [numerators, map_ofNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc 2
  · simpa [numerators, map_ofNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
  · simpa [numerators, map_ofNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hb 4
  · simpa [numerators, map_ofNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc 5

end QuadricContactLift

#print axioms QuadricContactLift.lift_strict_equations
