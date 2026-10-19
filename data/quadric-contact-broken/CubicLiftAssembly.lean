import Proposal.ActiveHomogeneousClearing
import Proposal.FractionLift
import Proposal.RationalTarget

noncomputable section
namespace QuadricContactAssembly
open MvPolynomial QuadricContactClearing QuadricContactHorizontal

def activeVariables : Fin 4 → BasePoly :=
  ![C (2:ℚ) * (X 0^2+X 3^2), C (4:ℚ)*X 0*X 3, X 1^2, X 2^2]

theorem activeVariables_homogeneous (i : Fin 4) : (activeVariables i).IsHomogeneous 2 := by
  fin_cases i
  · exact ((isHomogeneous_X_pow 0 2).add (isHomogeneous_X_pow 3 2)).C_mul 2
  · exact ((isHomogeneous_X ℚ 0).C_mul 4).mul (isHomogeneous_X ℚ 3)
  · exact isHomogeneous_X_pow 1 2
  · exact isHomogeneous_X_pow 2 2

theorem activeVariables_map (i : Fin 4) : baseMap (activeVariables i) = active i := by
  fin_cases i <;> simp [activeVariables, active, coordinate, QuadricContactTarget.baseMap_C]

theorem activeImage_eq : activeImage activeVariables = activeMap := by
  unfold activeImage activeMap
  exact congrArg (eval₂Hom regularParameterMap) (funext activeVariables_map)

/-- The four-variable strict certificate supplies homogeneous polynomial data
for the sextic, with an exact good-fibre denominator profile. -/
theorem exists_cleared_cubic
    (D : ActivePoly) (N : Fin 4 → ActivePoly) (h : ℕ)
    (hD : D.IsHomogeneous h) (hN : ∀ i, (N i).IsHomogeneous h)
    (hsrc : (∑ i, N i * pderiv i QuadricContactTarget.cubic) = D * (X 1 * X 2))
    (hdiv : D * (∑ i, pderiv i (N i)) = ∑ i, N i * pderiv i D) :
    ∃ (n : ℕ) (κ : ℚ) (Q : BasePoly) (P : Fin 4 → BasePoly),
      κ ≠ 0 ∧ Q.IsHomogeneous (2*(n+h)) ∧
      (∀ i, (P i).IsHomogeneous (2*(n+h))) ∧
      QuadricContactLift.source QuadricContactTarget.F (P 0) (P 1) (P 2) (P 3) =
        QuadricContactTarget.A * QuadricContactLift.denominator Q ∧
      QuadricContactLift.divergenceCondition Q (P 0) (P 1) (P 2) (P 3) = 0 ∧
      ratioBase Q = C κ * ac^n * activeFibre activeVariables D := by
  let family : Option (Fin 4) → ActivePoly := fun i => i.elim D N
  have hfamily : ∀ i, (family i).IsHomogeneous h := by
    intro i
    cases i with
    | none => exact hD
    | some j => exact hN j
  obtain ⟨n,q,u,P,hdatum,hq,hPh,hrep,hfiber⟩ :=
    exists_active_representatives_with_fibre family h hfamily activeVariables activeVariables_homogeneous
  have hQrep : baseMap (P none) = baseMap u * activeMap D := by
    simpa only [family, Option.elim_none, activeImage_eq] using hrep none
  have hPrep : ∀ i, baseMap (P (some i)) = baseMap u * activeMap (N i) := by
    intro i
    simpa only [family, Option.elim_some, activeImage_eq] using hrep (some i)
  refine ⟨n,goodParameters q,P none,fun i => P (some i),hq,hPh none,
    fun i => hPh (some i),?_,?_,?_⟩
  · exact QuadricContactFractionLift.homogeneous_clearing_source D N u (P none)
      (fun i => P (some i)) hQrep hPrep hsrc
  · exact QuadricContactFractionLift.homogeneous_clearing_divergence D N u (P none)
      (fun i => P (some i)) hQrep hPrep hdiv
  · simpa only [family, Option.elim_none] using hfiber none

end QuadricContactAssembly

#print axioms QuadricContactAssembly.exists_cleared_cubic
