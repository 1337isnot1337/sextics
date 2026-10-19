import Proposal.HomogeneousSubstitution

noncomputable section
namespace QuadricContactClearing
open MvPolynomial

def ratioValues : Fin 6 → BasePoly := ![X 0, X 1, X 2, X 3, X 1, 2 * X 2]
def ratioBase : BasePoly →+* BasePoly := eval₂Hom C ratioValues

theorem baseMap_ratioBase (H : BasePoly) :
    baseMap (ratioBase H) =
      eval₂ (algebraMap ℚ FunctionField) (fun i => baseMap (ratioValues i)) H := by
  induction H using MvPolynomial.induction_on with
  | C r => simp only [ratioBase, coe_eval₂Hom, eval₂_C]; rfl
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, ratioBase, coe_eval₂Hom, eval₂_mul, eval₂_X] at hp ⊢
      rw [hp]

theorem goodParameters_map (p : Parameters) :
    eval₂ (algebraMap ℚ FunctionField) ![1,2] p =
      algebraMap ℚ FunctionField (goodParameters p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [goodParameters, ParameterSpecialization.point]
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | mul_X p j hp =>
      simp only [eval₂_mul, eval₂_X, map_mul, hp]
      congr 1
      simp only [goodParameters, ParameterSpecialization.point, coe_eval₂Hom, eval₂_X]
      fin_cases j <;> norm_num [Matrix.cons_val, Fin.isValue, map_ofNat]

theorem HomogeneousDatum.ratioBase {p : Parameters} {n : ℕ} {H : BasePoly}
    (hp : HomogeneousDatum p n H) :
    ratioBase H = C (goodParameters p) * ac^n := by
  apply IsFractionRing.injective BasePoly FunctionField
  rw [baseMap_ratioBase]
  have ha : baseMap (ratioValues 1) ≠ 0 := coordinate_ne_zero 1
  have hc : baseMap (ratioValues 2) ≠ 0 := coordinate_ne_zero 2
  rw [hp.evaluation (fun i => baseMap (ratioValues i)) ha hc]
  have hval :
      ![baseMap (ratioValues 4) / baseMap (ratioValues 1),
        baseMap (ratioValues 5) / baseMap (ratioValues 2)] =
      (![1,2] : Fin 2 → FunctionField) := by
    funext j
    fin_cases j
    · change baseMap (X 1) / baseMap (X 1) = 1
      exact div_self (coordinate_ne_zero 1)
    · change baseMap (2 * X 2) / baseMap (X 2) = 2
      rw [map_mul, map_ofNat]
      exact mul_div_cancel_right₀ 2 (coordinate_ne_zero 2)
  rw [hval, goodParameters_map]
  simp only [map_mul, map_pow, ratioValues, Matrix.cons_val, ac]
  change (baseMap (X 1) * baseMap (X 2))^n *
      algebraMap ℚ FunctionField (goodParameters p) =
    algebraMap ℚ FunctionField (goodParameters p) * (baseMap (X 1) * baseMap (X 2))^n
  ring

/-- Coefficient clearing with its exact good-fibre profile retained. -/
theorem exists_regular_representatives_with_fibre {ι : Type*} [Fintype ι]
    (z : ι → RegularSpecialization.Coefficients goodParameters) :
    ∃ (n : ℕ) (q : Parameters) (D : BasePoly) (N : ι → BasePoly),
      HomogeneousDatum q n D ∧ goodParameters q ≠ 0 ∧
      (∀ i, (N i).IsHomogeneous (2*n)) ∧
      (∀ i, ratioBase (N i) =
        C (goodParameters q * RegularSpecialization.specialize goodParameters (z i)) * ac^n) ∧
      (∀ i, baseMap (N i) = baseMap D * regularParameterMap (z i)) := by
  obtain ⟨n, q, p, D, N, hD, hD0, hN, hrep⟩ :=
    regular_uniform_homogeneous_clearing z
  refine ⟨n,q,D,N,hD,?_,fun i => (hN i).homogeneous,?_,?_⟩
  · rwa [hD.goodBase] at hD0
  · intro i
    rw [(hN i).ratioBase]
    have hi := congrArg (RegularSpecialization.specialize goodParameters) (hrep i)
    simp only [map_mul, RegularSpecialization.specialize_algebraMap] at hi
    rw [hi]
  · intro i
    have hi := congrArg regularParameterMap (hrep i)
    simp only [map_mul, regularParameterMap_algebraMap] at hi
    rw [(hN i).fraction_evaluation, hD.fraction_evaluation, hi]
    ring

end QuadricContactClearing

#print axioms QuadricContactClearing.HomogeneousDatum.ratioBase
