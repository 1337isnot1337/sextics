import Proposal.HoldoutActiveClearing
import Proposal.HoldoutAlgebra
import Proposal.NewLineAlgebra

/-! Actual substitution of the four cubic coefficients into the two passive
parameters. The source localization is definitionally the coefficient ring of
NewLineAlgebra. No unspecified coefficient homomorphism is assumed. -/

noncomputable section
namespace HoldoutQ2.CoefficientMap
open MvPolynomial Clearing

abbrev SourcePolynomial := MvPolynomial (Fin 4) ℚ
def sourcePoint : SourcePolynomial →+* ℚ :=
  eval₂Hom (RingHom.id ℚ) ![2,2,1,1]
abbrev SourceCoefficients := RegularSpecialization.Coefficients sourcePoint

def sourceSpecialize : SourceCoefficients →+* ℚ :=
  RegularSpecialization.specialize sourcePoint

def parameterValues (k : ℂ) : Fin 4 → Parameters :=
  ![1+X 0^6, 1+X 1^6, X 0*X 1, X 1*C (k^2)]

def polynomialMap (k : ℂ) : SourcePolynomial →+* Parameters :=
  eval₂Hom (C.comp (Rat.castHom ℂ)) (parameterValues k)

def polynomialMapRegular (k : ℂ) : SourcePolynomial →+* Regular k :=
  (algebraMap Parameters (Regular k)).comp (polynomialMap k)

def alpha (k : ℂ) : Regular k := algebraMap Parameters (Regular k) (X 0)
def beta (k : ℂ) : Regular k := algebraMap Parameters (Regular k) (X 1)
def constant (k z : ℂ) : Regular k := algebraMap Parameters (Regular k) (C z)

theorem parameters_specialize (k : ℂ) (hk : k^2+k+1=0) (i : Fin 4) :
    goodParameters k (parameterValues k i) = (sourcePoint (X i) : ℂ) := by
  have h3 := HoldoutAlgebra.cube_eq_one hk
  have h6 := HoldoutAlgebra.sixth_eq_one hk
  have h12 : (k^2)^6=1 := by
    calc (k^2)^6=(k^6)^2 := by ring
         _=1 := by rw [h6]; ring
  have h21 : k^2*k=1 := by
    calc k^2*k=k^3 := by ring
         _=1 := h3
  have h12' : k*k^2=1 := by rw [mul_comm]; exact h21
  fin_cases i <;>
    norm_num [goodParameters, parameterValues, sourcePoint, h12, h6, h21, h12']

/-- The coefficient substitution really passes through the certified good point. -/
theorem polynomial_specialization (k : ℂ) (hk : k^2+k+1=0) :
    (goodParameters k).comp (polynomialMap k) =
      (Rat.castHom ℂ).comp sourcePoint := by
  apply MvPolynomial.ringHom_ext
  · intro q
    simp [polynomialMap, goodParameters, sourcePoint]
  · intro i
    simpa only [RingHom.comp_apply, polynomialMap, eval₂Hom_X', Rat.coe_castHom] using
      parameters_specialize k hk i

@[simp] theorem polynomialMapRegular_specialize (k : ℂ) (hk : k^2+k+1=0)
    (p : SourcePolynomial) :
    RegularSpecialization.specialize (goodParameters k) (polynomialMapRegular k p) =
      (sourcePoint p : ℂ) := by
  simp only [polynomialMapRegular, RingHom.comp_apply,
    RegularSpecialization.specialize_algebraMap]
  exact DFunLike.congr_fun (polynomial_specialization k hk) p

theorem polynomialMapRegular_unit (k : ℂ) (hk : k^2+k+1=0)
    (s : RegularSpecialization.denominators sourcePoint) :
    IsUnit (polynomialMapRegular k s) := by
  apply (RegularSpecialization.isUnit_iff_specialize_ne_zero (goodParameters k) _).mpr
  rw [polynomialMapRegular_specialize k hk]
  exact_mod_cast s.property

/-- The actual four-coefficient localization map. -/
def coefficientMap (k : ℂ) (hk : k^2+k+1=0) : SourceCoefficients →+* Regular k :=
  IsLocalization.lift (polynomialMapRegular_unit k hk)

@[simp] theorem coefficientMap_algebraMap (k : ℂ) (hk : k^2+k+1=0)
    (p : SourcePolynomial) :
    coefficientMap k hk (algebraMap SourcePolynomial SourceCoefficients p) =
      polynomialMapRegular k p := IsLocalization.lift_eq _ p

/-- Compatibility for arbitrary regular rational coefficients, not only generators. -/
theorem coefficientMap_specialization (k : ℂ) (hk : k^2+k+1=0) :
    (RegularSpecialization.specialize (goodParameters k)).comp (coefficientMap k hk) =
      (Rat.castHom ℂ).comp sourceSpecialize := by
  apply IsLocalization.ringHom_ext (RegularSpecialization.denominators sourcePoint)
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply, coefficientMap_algebraMap,
    polynomialMapRegular_specialize k hk, sourceSpecialize,
    RegularSpecialization.specialize_algebraMap, Rat.coe_castHom]

@[simp] theorem coefficientMap_a (k : ℂ) (hk : k^2+k+1=0) :
    coefficientMap k hk (algebraMap SourcePolynomial SourceCoefficients (X 0)) =
      1+alpha k^6 := by
  simp [polynomialMapRegular, polynomialMap, parameterValues, alpha]

@[simp] theorem coefficientMap_b (k : ℂ) (hk : k^2+k+1=0) :
    coefficientMap k hk (algebraMap SourcePolynomial SourceCoefficients (X 1)) =
      1+beta k^6 := by
  simp [polynomialMapRegular, polynomialMap, parameterValues, beta]

@[simp] theorem coefficientMap_c (k : ℂ) (hk : k^2+k+1=0) :
    coefficientMap k hk (algebraMap SourcePolynomial SourceCoefficients (X 2)) =
      alpha k*beta k := by
  simp [polynomialMapRegular, polynomialMap, parameterValues, alpha, beta]

@[simp] theorem coefficientMap_d (k : ℂ) (hk : k^2+k+1=0) :
    coefficientMap k hk (algebraMap SourcePolynomial SourceCoefficients (X 3)) =
      beta k*constant k (k^2) := by
  simp [polynomialMapRegular, polynomialMap, parameterValues, beta, constant]

@[simp] theorem specialize_alpha (k : ℂ) :
    RegularSpecialization.specialize (goodParameters k) (alpha k) = k^2 := by
  unfold alpha
  rw [RegularSpecialization.specialize_algebraMap]
  simp [goodParameters]

@[simp] theorem specialize_beta (k : ℂ) :
    RegularSpecialization.specialize (goodParameters k) (beta k) = k := by
  unfold beta
  rw [RegularSpecialization.specialize_algebraMap]
  simp [goodParameters]

@[simp] theorem specialize_constant (k z : ℂ) :
    RegularSpecialization.specialize (goodParameters k) (constant k z) = z := by
  unfold constant
  rw [RegularSpecialization.specialize_algebraMap]
  simp [goodParameters]

/-- Same map with the source type bound explicitly to the constructed line algebra. -/
def lineCoefficientMap (k : ℂ) (hk : k^2+k+1=0) :
    NewLineAlgebra.Coefficients →+* Regular k := coefficientMap k hk

@[simp] theorem lineCoefficientMap_a (k : ℂ) (hk : k^2+k+1=0) :
    lineCoefficientMap k hk NewLineAlgebra.a = 1+alpha k^6 :=
  coefficientMap_a k hk

@[simp] theorem lineCoefficientMap_b (k : ℂ) (hk : k^2+k+1=0) :
    lineCoefficientMap k hk NewLineAlgebra.b = 1+beta k^6 :=
  coefficientMap_b k hk

@[simp] theorem lineCoefficientMap_c (k : ℂ) (hk : k^2+k+1=0) :
    lineCoefficientMap k hk NewLineAlgebra.c = alpha k*beta k :=
  coefficientMap_c k hk

@[simp] theorem lineCoefficientMap_d (k : ℂ) (hk : k^2+k+1=0) :
    lineCoefficientMap k hk NewLineAlgebra.d = beta k*constant k (k^2) :=
  coefficientMap_d k hk

theorem lineCoefficientMap_specialization (k : ℂ) (hk : k^2+k+1=0)
    (x : NewLineAlgebra.Coefficients) :
    RegularSpecialization.specialize (goodParameters k) (lineCoefficientMap k hk x) =
      (NewLineAlgebra.specialize x : ℂ) :=
  DFunLike.congr_fun (coefficientMap_specialization k hk) x

end HoldoutQ2.CoefficientMap
