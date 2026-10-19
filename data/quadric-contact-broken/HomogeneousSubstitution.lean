import Proposal.HomogeneousClearing

noncomputable section
namespace QuadricContactClearing
open MvPolynomial

abbrev FunctionField := FractionRing BasePoly
abbrev baseMap : BasePoly →+* FunctionField := algebraMap BasePoly FunctionField

def coordinate (i : Fin 6) : FunctionField := baseMap (X i)

def parameterMap : Parameters →+* FunctionField :=
  eval₂Hom (algebraMap ℚ FunctionField)
    ![coordinate 4 / coordinate 1, coordinate 5 / coordinate 2]

theorem coordinate_ne_zero (i : Fin 6) : coordinate i ≠ 0 := by
  exact fun h => X_ne_zero i ((IsFractionRing.injective BasePoly FunctionField)
    (by simpa [coordinate] using h))

theorem eval_coordinates (H : BasePoly) :
    eval₂ (algebraMap ℚ FunctionField) coordinate H = baseMap H := by
  induction H using MvPolynomial.induction_on with
  | C r => simp only [eval₂_C]; rfl
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | mul_X p j hp => simp only [eval₂_mul, eval₂_X, map_mul, hp, coordinate]

theorem HomogeneousDatum.fraction_evaluation {p : Parameters} {n : ℕ} {H : BasePoly}
    (hp : HomogeneousDatum p n H) :
    baseMap H = baseMap ac ^ n * parameterMap p := by
  have he := hp.evaluation coordinate (coordinate_ne_zero 1) (coordinate_ne_zero 2)
  rw [eval_coordinates] at he
  simpa only [ac, map_mul, coordinate, parameterMap, coe_eval₂Hom] using he

theorem parameterMap_ne_zero_of_good {p : Parameters} (hp : goodParameters p ≠ 0) :
    parameterMap p ≠ 0 := by
  obtain ⟨n, H, hH⟩ := exists_homogeneousDatum p
  have hH0 : H ≠ 0 := by
    intro hz
    have hg := hH.goodBase
    rw [hz, map_zero] at hg
    exact hp hg.symm
  intro hz
  have he := hH.fraction_evaluation
  rw [hz, mul_zero] at he
  exact hH0 ((IsFractionRing.injective BasePoly FunctionField) (by simpa using he))

/-- Actual substitution of every regular coefficient at alpha=b/a,beta=d/c. -/
noncomputable def regularParameterMap :
    RegularSpecialization.Coefficients goodParameters →+* FunctionField :=
  IsLocalization.lift (fun s : RegularSpecialization.denominators goodParameters =>
    isUnit_iff_ne_zero.mpr (parameterMap_ne_zero_of_good s.property))

@[simp] theorem regularParameterMap_algebraMap (p : Parameters) :
    regularParameterMap
      (algebraMap Parameters (RegularSpecialization.Coefficients goodParameters) p) =
      parameterMap p := IsLocalization.lift_eq _ p

/-- Every finite family has one homogeneous denominator in the original variables,
with nonzero good specialization, and actual fraction-field equalities. -/
theorem exists_regular_homogeneous_representatives {ι : Type*} [Fintype ι]
    (z : ι → RegularSpecialization.Coefficients goodParameters) :
    ∃ (n : ℕ) (D : BasePoly) (N : ι → BasePoly),
      D.IsHomogeneous (2*n) ∧ goodBase D ≠ 0 ∧
      (∀ i, (N i).IsHomogeneous (2*n)) ∧
      (∀ i, baseMap (N i) = baseMap D * regularParameterMap (z i)) := by
  obtain ⟨n, q, p, D, N, hD, hD0, hN, hrep⟩ :=
    regular_uniform_homogeneous_clearing z
  refine ⟨n, D, N, hD.homogeneous, hD0, fun i => (hN i).homogeneous, ?_⟩
  intro i
  have hi := congrArg regularParameterMap (hrep i)
  simp only [map_mul, regularParameterMap_algebraMap] at hi
  rw [(hN i).fraction_evaluation, hD.fraction_evaluation, hi]
  ring

end QuadricContactClearing

#print axioms QuadricContactClearing.exists_regular_homogeneous_representatives
