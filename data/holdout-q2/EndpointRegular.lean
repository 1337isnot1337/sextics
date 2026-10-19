import Proposal.EndpointTarget
import Proposal.HoldoutSubstitution

noncomputable section
namespace HoldoutEndpointRegular
open MvPolynomial HoldoutEndpointHorizontal

theorem parameterMap_eq :
    HoldoutEndpointTarget.parameterMap=HoldoutQ2.Clearing.parameterMap := by
  rfl

theorem horizontal_parameterMap (k : ℂ) (i : Fin 4)
    (P : HoldoutQ2.Clearing.Parameters) :
    horizontal k i (HoldoutQ2.Clearing.parameterMap P)=0 := by
  rw [← parameterMap_eq]
  exact HoldoutEndpointTarget.horizontal_parameterMap k i P

/-- Every regular coefficient stays constant under the actual horizontal
derivations, including denominators introduced by the matrix inverses. -/
theorem horizontal_regularParameterMap (k : ℂ) (i : Fin 4)
    (r : RegularSpecialization.Coefficients (HoldoutQ2.Clearing.goodParameters k)) :
    horizontal k i (HoldoutQ2.Clearing.regularParameterMap k r)=0 := by
  obtain ⟨⟨p,q⟩,he⟩ :=
    IsLocalization.surj (RegularSpecialization.denominators (HoldoutQ2.Clearing.goodParameters k)) r
  have hm := congrArg (HoldoutQ2.Clearing.regularParameterMap k) he
  simp only [map_mul,HoldoutQ2.Clearing.regularParameterMap_algebraMap] at hm
  have hd := congrArg (horizontal k i) hm
  simp only [Derivation.leibniz,horizontal_parameterMap,smul_eq_mul,mul_zero,zero_add] at hd
  exact (mul_eq_zero.mp hd).resolve_left
    (HoldoutQ2.Clearing.parameterMap_ne_zero_of_good q.property)

end HoldoutEndpointRegular

#print axioms HoldoutEndpointRegular.horizontal_regularParameterMap
