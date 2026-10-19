import Proposal.EndpointHorizontal

noncomputable section
namespace HoldoutEndpointFractionLift
open MvPolynomial HoldoutEndpointHorizontal

variable {O : Type*} [CommRing O]
abbrev AP := MvPolynomial (Fin 4) O

theorem clearing_cross (Δ : Derivation ℚ FunctionField FunctionField)
    (u q n : FunctionField) :
    (u*q)*Δ (u*n)-(u*n)*Δ (u*q)=u^2*(q*Δ n-n*Δ q) := by
  simp only [Derivation.leibniz,smul_eq_mul]
  ring

theorem homogeneous_clearing_divergence
    (f : O →+* FunctionField) (k : ℂ) (hk : k^2+k+1=0)
    (hc : ∀ i r, horizontal k i (f r)=0)
    (D : AP (O := O)) (N : Fin 4 → AP (O := O))
    (u Q : BasePoly) (P : Fin 4 → BasePoly)
    (hQ : baseMap Q=baseMap u*activeMap f k D)
    (hP : ∀ i, baseMap (P i)=baseMap u*activeMap f k (N i))
    (hdiv : D*(∑ i, pderiv i (N i))=∑ i, N i*pderiv i D) :
    HoldoutEndpointLift.divergenceCondition k Q (P 0) (P 1) (P 2) (P 3)=0 := by
  let t : Fin 4 → FunctionField := fun i =>
    activeMap f k D*activeMap f k (pderiv i (N i))-
      activeMap f k (N i)*activeMap f k (pderiv i D)
  have ht : ∑ i, t i=0 := by
    have hh := congrArg (activeMap f k) hdiv
    simp only [map_mul,map_sum] at hh
    simp only [t,Finset.sum_sub_distrib,← Finset.mul_sum,hh,sub_self]
  have hx (i : Fin 4) :
      baseMap Q*horizontal k i (baseMap (P i))-
        baseMap (P i)*horizontal k i (baseMap Q)=
      baseMap u^2*scale k i*t i := by
    rw [hQ,hP,clearing_cross,horizontal_activeMap f k hk hc,
      horizontal_activeMap f k hk hc]
    dsimp [t]
    ring
  apply IsFractionRing.injective BasePoly FunctionField
  rw [map_zero]
  simp only [HoldoutEndpointLift.divergenceCondition,map_add,map_sub,map_mul,
    map_pow,map_ofNat,← horizontal_map_U k,← horizontal_map_V k,
    ← horizontal_map_S k,← horizontal_map_T k]
  rw [show baseMap Q*horizontal k 2 (baseMap (P 2))-
      baseMap (P 2)*horizontal k 2 (baseMap Q)+
      baseMap Q*horizontal k 3 (baseMap (P 3))-
      baseMap (P 3)*horizontal k 3 (baseMap Q)=
      (baseMap Q*horizontal k 2 (baseMap (P 2))-
      baseMap (P 2)*horizontal k 2 (baseMap Q))+
      (baseMap Q*horizontal k 3 (baseMap (P 3))-
      baseMap (P 3)*horizontal k 3 (baseMap Q)) by ring]
  rw [hx 0,hx 1,hx 2,hx 3]
  have ht' : t 0+t 1+t 2+t 3=0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using ht
  simp only [scale,Matrix.cons_val,HoldoutEndpointLift.clearing,
    HoldoutEndpointLift.delta,map_mul,map_pow,map_sub,coordinate,constant]
  linear_combination
    2*(baseMap (X 2)^2-baseMap (C k)^2*baseMap (X 5)^2)*
      baseMap (X 0)^2*baseMap (X 1)^2*baseMap u^2*ht'

/-- A source identity over the active cubic descends through the actual
fraction-field substitution. The target hypothesis is the exact determinant
density `2*delta*B`; no derivative or coefficient is treated as a formal scalar. -/
theorem homogeneous_clearing_source
    (f : O →+* FunctionField) (k : ℂ) (hk : k^2+k+1=0)
    (hc : ∀ i r, horizontal k i (f r)=0)
    (G B D : AP (O := O)) (N : Fin 4 → AP (O := O))
    (F A u Q : BasePoly) (P : Fin 4 → BasePoly)
    (hF : activeMap f k G=baseMap F)
    (hA : 2*baseMap (HoldoutEndpointLift.delta k)*activeMap f k B=baseMap A)
    (hQ : baseMap Q=baseMap u*activeMap f k D)
    (hP : ∀ i, baseMap (P i)=baseMap u*activeMap f k (N i))
    (hsrc : 2*(∑ i, N i*pderiv i G)=D*B) :
    2*HoldoutEndpointLift.source k F (P 0) (P 1) (P 2) (P 3)=
      A*HoldoutEndpointLift.denominator Q := by
  have hd (i : Fin 4) :
      baseMap (polynomialHorizontal k i F)=scale k i*activeMap f k (pderiv i G) := by
    have hh := congrArg (horizontal k i) hF
    rw [horizontal_activeMap f k hk hc,horizontal_map] at hh
    exact hh.symm
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  have hd3 := hd 3
  change baseMap (HoldoutEndpointLift.horizontalU F)=_ at hd0
  change baseMap (HoldoutEndpointLift.horizontalV F)=_ at hd1
  change baseMap (HoldoutEndpointLift.horizontalS F)=_ at hd2
  change baseMap (HoldoutEndpointLift.horizontalT k F)=_ at hd3
  have hs := congrArg (activeMap f k) hsrc
  simp only [map_sum,map_mul,map_ofNat] at hs
  simp [Fin.sum_univ_succ] at hs
  apply IsFractionRing.injective BasePoly FunctionField
  simp only [HoldoutEndpointLift.source,HoldoutEndpointLift.denominator,
    HoldoutEndpointLift.clearing,HoldoutEndpointLift.delta,
    map_add,map_sub,map_mul,map_pow,map_ofNat,hQ,hP,← hA]
  simp only [scale,Matrix.cons_val,coordinate,constant] at hd0 hd1 hd2 hd3
  simp only [HoldoutEndpointLift.delta,map_sub,map_mul,map_pow] at hA
  linear_combination
    2*(baseMap (X 2)^2-baseMap (C k)^2*baseMap (X 5)^2)*baseMap (X 1)^2*
      baseMap u*activeMap f k (N 0)*hd0+
    2*(baseMap (X 2)^2-baseMap (C k)^2*baseMap (X 5)^2)*baseMap (X 0)^2*
      baseMap u*activeMap f k (N 1)*hd1+
    2*baseMap (X 0)^2*baseMap (X 1)^2*baseMap u*activeMap f k (N 2)*hd2+
    2*baseMap (X 0)^2*baseMap (X 1)^2*baseMap u*activeMap f k (N 3)*hd3+
    2*(baseMap (X 2)^2-baseMap (C k)^2*baseMap (X 5)^2)*
      baseMap (X 0)^2*baseMap (X 1)^2*baseMap u*hs

end HoldoutEndpointFractionLift

#print axioms HoldoutEndpointFractionLift.homogeneous_clearing_divergence
#print axioms HoldoutEndpointFractionLift.homogeneous_clearing_source
