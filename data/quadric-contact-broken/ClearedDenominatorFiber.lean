import Proposal.TerminalFibre

noncomputable section
namespace QuadricContactClearedDenominator
open MvPolynomial QuadricContactClearing

/-- The actual quadratic substitution, in protected coordinate order. This is
definitionally the same tuple as QuadricContactAssembly.activeVariables. -/
def activeVariables : Fin 4 → BasePoly :=
  ![C (2 : ℚ) * (X 0 ^ 2 + X 3 ^ 2), C (4 : ℚ) * X 0 * X 3,
    X 1 ^ 2, X 2 ^ 2]

theorem fiber_activeVariables : (fun j => fiber (activeVariables j)) =
    (![(2 : Polynomial ℂ) * Polynomial.X ^ 2, 0, 1, 1] : Fin 4 → Polynomial ℂ) := by
  funext j
  fin_cases j <;>
    norm_num [activeVariables, fiber, fiberValues, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Polynomial.C_ofNat]

theorem activeFibre_terminal (P : ActivePoly) :
    fiber (activeFibre activeVariables P) =
      MvPolynomial.eval₂Hom (Polynomial.C.comp ((Rat.castHom ℂ).comp ParameterSpecialization.specialize))
        ![(2 : Polynomial ℂ) * Polynomial.X ^ 2, 0, 1, 1] P := by
  rw [fiber_activeFibre, fiber_activeVariables]
  rfl

end QuadricContactClearedDenominator

#print axioms QuadricContactClearedDenominator.activeFibre_terminal
