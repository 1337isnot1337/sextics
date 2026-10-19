import Proposal.HoldoutClearing

noncomputable section
namespace HoldoutQ2.Clearing
open MvPolynomial
variable {k : ℂ}

abbrev FunctionField := FractionRing BasePoly
abbrev baseMap : BasePoly →+* FunctionField := algebraMap BasePoly FunctionField

def coordinate (i : Fin 6) : FunctionField := baseMap (X i)

def parameterMap : Parameters →+* FunctionField :=
  eval₂Hom (algebraMap ℂ FunctionField)
    ![coordinate 3 / coordinate 0, coordinate 4 / coordinate 1]

theorem coordinate_ne_zero (i : Fin 6) : coordinate i ≠ 0 := by
  exact fun h => X_ne_zero i ((IsFractionRing.injective BasePoly FunctionField)
    (by simpa [coordinate] using h))

theorem eval_coordinates (H : BasePoly) :
    eval₂ (algebraMap ℂ FunctionField) coordinate H = baseMap H := by
  induction H using MvPolynomial.induction_on with
  | C r => simp only [eval₂_C]; rfl
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | mul_X p j hp => simp only [eval₂_mul, eval₂_X, map_mul, hp, coordinate]

theorem HomogeneousDatum.fraction_evaluation {p : Parameters} {n : ℕ} {H : BasePoly}
    (hp : HomogeneousDatum p n H) :
    baseMap H = baseMap xa ^ n * parameterMap p := by
  have he := hp.evaluation coordinate (coordinate_ne_zero 0) (coordinate_ne_zero 1)
  rw [eval_coordinates] at he
  simpa only [xa, map_mul, coordinate, parameterMap, coe_eval₂Hom] using he

theorem parameterMap_ne_zero_of_good {p : Parameters} (hp : goodParameters k p ≠ 0) :
    parameterMap p ≠ 0 := by
  obtain ⟨n, H, hH⟩ := exists_homogeneousDatum p
  have hH0 : H ≠ 0 := by
    intro hz
    have hg := hH.goodBase (k := k)
    rw [hz, map_zero] at hg
    exact hp hg.symm
  intro hz
  have he := hH.fraction_evaluation
  rw [hz, mul_zero] at he
  exact hH0 ((IsFractionRing.injective BasePoly FunctionField) (by simpa using he))

/-- Actual substitution of every regular coefficient at alpha=y/x,beta=b/a. -/
noncomputable def regularParameterMap (k : ℂ) :
    RegularSpecialization.Coefficients (goodParameters k) →+* FunctionField :=
  IsLocalization.lift (fun s : RegularSpecialization.denominators (goodParameters k) =>
    isUnit_iff_ne_zero.mpr (parameterMap_ne_zero_of_good s.property))

@[simp] theorem regularParameterMap_algebraMap (p : Parameters) :
    regularParameterMap k
      (algebraMap Parameters (RegularSpecialization.Coefficients (goodParameters k)) p) =
      parameterMap p := IsLocalization.lift_eq _ p

/-- Every finite family has one homogeneous denominator in the original variables,
with nonzero good specialization, and actual fraction-field equalities. -/
theorem exists_regular_homogeneous_representatives {ι : Type*} [Fintype ι]
    (z : ι → RegularSpecialization.Coefficients (goodParameters k)) :
    ∃ (n : ℕ) (D : BasePoly) (N : ι → BasePoly),
      D.IsHomogeneous (2*n) ∧ goodBase k D ≠ 0 ∧
      (∀ i, (N i).IsHomogeneous (2*n)) ∧
      (∀ i, baseMap (N i) = baseMap D * regularParameterMap k (z i)) := by
  obtain ⟨n, q, p, D, N, hD, hD0, hN, hrep⟩ :=
    regular_uniform_homogeneous_clearing z
  refine ⟨n, D, N, hD.homogeneous, hD0, fun i => (hN i).homogeneous, ?_⟩
  intro i
  have hi := congrArg (regularParameterMap k) (hrep i)
  simp only [map_mul, regularParameterMap_algebraMap] at hi
  rw [(hN i).fraction_evaluation, hD.fraction_evaluation, hi]
  ring

def ratioValues (k : ℂ) : Fin 6 → BasePoly := ![X 0,X 1,X 2,C (k^2)*X 0,C k*X 1,X 5]
def ratioBase (k : ℂ) : BasePoly →+* BasePoly := eval₂Hom C (ratioValues k)

theorem baseMap_ratioBase (H : BasePoly) :
    baseMap (ratioBase k H) =
      eval₂ (algebraMap ℂ FunctionField) (fun i => baseMap (ratioValues k i)) H := by
  induction H using MvPolynomial.induction_on with
  | C r => simp only [ratioBase, coe_eval₂Hom, eval₂_C]; rfl
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, ratioBase, coe_eval₂Hom, eval₂_mul, eval₂_X] at hp ⊢
      rw [hp]

theorem goodParameters_map (p : Parameters) :
    eval₂ (algebraMap ℂ FunctionField) ![algebraMap ℂ FunctionField (k^2),algebraMap ℂ FunctionField k] p =
      algebraMap ℂ FunctionField (goodParameters k p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [goodParameters]
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | mul_X p j hp =>
      simp only [eval₂_mul, eval₂_X, map_mul, hp]
      congr 1
      simp only [goodParameters, coe_eval₂Hom, eval₂_X]
      fin_cases j <;> norm_num [Matrix.cons_val, Fin.isValue, map_ofNat]

theorem HomogeneousDatum.ratioBase {p : Parameters} {n : ℕ} {H : BasePoly}
    (hp : HomogeneousDatum p n H) :
    ratioBase k H = C (goodParameters k p) * xa^n := by
  apply IsFractionRing.injective BasePoly FunctionField
  rw [baseMap_ratioBase]
  have hx : baseMap (ratioValues k 0) ≠ 0 := coordinate_ne_zero 0
  have ha : baseMap (ratioValues k 1) ≠ 0 := coordinate_ne_zero 1
  rw [hp.evaluation (fun i => baseMap (ratioValues k i)) hx ha]
  have hval :
      ![baseMap (ratioValues k 3) / baseMap (ratioValues k 0),
        baseMap (ratioValues k 4) / baseMap (ratioValues k 1)] =
      (![algebraMap ℂ FunctionField (k^2),algebraMap ℂ FunctionField k] : Fin 2 → FunctionField) := by
    funext j
    fin_cases j
    · change baseMap (C (k^2) * X 0) / baseMap (X 0) = _
      rw [map_mul]
      exact mul_div_cancel_right₀ _ (coordinate_ne_zero 0)
    · change baseMap (C k * X 1) / baseMap (X 1) = _
      rw [map_mul]
      exact mul_div_cancel_right₀ _ (coordinate_ne_zero 1)
  rw [hval, goodParameters_map]
  simp only [map_mul, map_pow, ratioValues, Matrix.cons_val, xa]
  change (baseMap (X 0) * baseMap (X 1))^n *
      algebraMap ℂ FunctionField (goodParameters k p) =
    algebraMap ℂ FunctionField (goodParameters k p) * (baseMap (X 0) * baseMap (X 1))^n
  ring

/-- Coefficient clearing with its exact good-fibre profile retained. -/
theorem exists_regular_representatives_with_fibre {ι : Type*} [Fintype ι]
    (z : ι → RegularSpecialization.Coefficients (goodParameters k)) :
    ∃ (n : ℕ) (q : Parameters) (D : BasePoly) (N : ι → BasePoly),
      HomogeneousDatum q n D ∧ goodParameters k q ≠ 0 ∧
      (∀ i, (N i).IsHomogeneous (2*n)) ∧
      (∀ i, ratioBase k (N i) =
        C (goodParameters k q * RegularSpecialization.specialize (goodParameters k) (z i)) * xa^n) ∧
      (∀ i, baseMap (N i) = baseMap D * regularParameterMap k (z i)) := by
  obtain ⟨n, q, p, D, N, hD, hD0, hN, hrep⟩ :=
    regular_uniform_homogeneous_clearing z
  refine ⟨n,q,D,N,hD,?_,fun i => (hN i).homogeneous,?_,?_⟩
  · rwa [hD.goodBase] at hD0
  · intro i
    rw [(hN i).ratioBase]
    have hi := congrArg (RegularSpecialization.specialize (goodParameters k)) (hrep i)
    simp only [map_mul, RegularSpecialization.specialize_algebraMap] at hi
    rw [hi]
  · intro i
    have hi := congrArg (regularParameterMap k) (hrep i)
    simp only [map_mul, regularParameterMap_algebraMap] at hi
    rw [(hN i).fraction_evaluation, hD.fraction_evaluation, hi]
    ring

end HoldoutQ2.Clearing

#print axioms HoldoutQ2.Clearing.exists_regular_representatives_with_fibre
