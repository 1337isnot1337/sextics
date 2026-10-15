import Proposal.PEllipticAmbientActualField

/-! Exact compact forms of the already proved rational field. -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart HodgeTestbed.Conic
open scoped BigOperators

namespace Cubic
variable {R : Type*} [CommRing R]
def U1 (v w : Data R) : R := h0 v*H v*H w*t w*f w
def R0 (v w : Data R) : R :=
  f v*H w^3*(rf v*k v-6*delta v)-18*delta w*f w^2*H v^2*(v.c+3*v.d)
theorem l_radial (v : Data R) : l v*rf v-6*f v*(v.c+3*v.d)=2*H v := by
  simp only [l, rf, f, fp, H, h4, h6, h0]
  ring
theorem R0_bridge (v w : Data R) : f v*R0 v w-V v w*rf v=6*G v w := by
  have hh := l_radial v
  calc
    f v*R0 v w-V v w*rf v =
        3*delta w*f w^2*H v^2*(l v*rf v-6*f v*(v.c+3*v.d))-
        6*H w^3*delta v*f v^2 := by simp only [R0, V]; ring
    _ = 6*G v w := by rw [hh]; simp only [G]; ring
end Cubic

theorem actualG_ne_zero : Cubic.G pc qc ≠ 0 := by
  intro hh
  apply actualS_ne_zero
  simp [actualS, hh]
theorem actualP_ne_zero : Cubic.f pc ≠ 0 := by
  intro hh
  apply p_ne_zero
  rw [← baseEmbedding_p, fourP_cubic, hh, map_zero]
theorem actualQ_ne_zero : Cubic.f qc ≠ 0 := by
  intro hh
  apply q_ne_zero
  rw [← baseEmbedding_q, fourQ_cubic, hh, map_zero]

theorem actualPrimitive_action (f : K4) :
    fieldAction rationalPartial actualPrimitive f =
      fieldAction rationalPartial actualT f / (36*Cubic.f pc*Cubic.f qc*Cubic.G pc qc) := by
  simp only [fieldAction_apply]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [actualPrimitive, primitiveFromW, actualS, fourP_cubic, fourQ_cubic]
  field_simp [actualP_ne_zero, actualQ_ne_zero, actualG_ne_zero]
  <;> ring

theorem actualPrimitive_dp : fieldAction rationalPartial actualPrimitive fourP =
    Cubic.V pc qc*Cubic.rf pc/(36*Cubic.f qc*Cubic.G pc qc) := by
  rw [actualPrimitive_action, fourP_cubic, actualT_action,
    actual_radial_derivatives.2.2.2.2.1, actual_radial_derivatives.2.2.2.2.2.1]
  simp only [actualNP, actualNQ]
  field_simp [actualP_ne_zero, actualQ_ne_zero, actualG_ne_zero]
  <;> ring

theorem actualPrimitive_dq : fieldAction rationalPartial actualPrimitive fourQ =
    -Cubic.f pc*Cubic.U1 pc qc*Cubic.rf qc/(36*Cubic.f qc*Cubic.G pc qc) := by
  rw [actualPrimitive_action, fourQ_cubic, actualT_action,
    actual_radial_derivatives.2.2.2.2.2.2.1, actual_radial_derivatives.2.2.2.2.2.2.2]
  simp only [actualNP, actualNQ, Cubic.U, Cubic.U1]
  field_simp [actualP_ne_zero, actualQ_ne_zero, actualG_ne_zero]
  <;> ring

theorem extendBase_action (B : Fin 4 → K4) (f : K4) :
    fieldAction basePartial (extendBase B) (baseEmbedding f) =
      baseEmbedding (fieldAction rationalPartial B f) := by
  simp only [fieldAction_apply, extendBase, baseEmbedding_partial, map_sum, map_mul]

theorem actual_dp : dp (extendBase actualPrimitive) =
    baseEmbedding (Cubic.V pc qc*Cubic.rf pc/(36*Cubic.f qc*Cubic.G pc qc)) := by
  rw [dp, ← baseEmbedding_p, extendBase_action, actualPrimitive_dp]
theorem actual_dq : dq (extendBase actualPrimitive) =
    baseEmbedding (-Cubic.f pc*Cubic.U1 pc qc*Cubic.rf qc/(36*Cubic.f qc*Cubic.G pc qc)) := by
  rw [dq, ← baseEmbedding_q, extendBase_action, actualPrimitive_dq]

theorem actual_liftNormal : liftNormal (extendBase actualPrimitive) =
    baseEmbedding (Cubic.f pc)*
      (baseEmbedding (Cubic.R0 pc qc)-lambda^6*baseEmbedding (Cubic.U1 pc qc*Cubic.rf qc))/
      (36*q*lambda^4*baseEmbedding (Cubic.G pc qc)) := by
  have hg : baseEmbedding (Cubic.G pc qc) ≠ 0 := (map_ne_zero baseEmbedding).mpr actualG_ne_zero
  have bridge := congrArg baseEmbedding (Cubic.R0_bridge pc qc)
  simp only [map_sub, map_mul, map_ofNat] at bridge
  change lambda/h + fieldAction basePartial (scaledB (extendBase actualPrimitive)) splitF/density = _
  have hs : fieldAction basePartial (scaledB (extendBase actualPrimitive)) splitF =
      (dp (extendBase actualPrimitive)+lambda^6*dq (extendBase actualPrimitive))/lambda^2 := by
    simp only [fieldAction_apply, scaledB, base_splitF, dp, dq, Fin.sum_univ_succ]
    norm_num
    ring
  rw [hs, actual_dp, actual_dq]
  simp only [map_mul, map_div₀, map_neg, map_ofNat]
  have hq : baseEmbedding (Cubic.f qc) = q := by rw [← fourQ_cubic, baseEmbedding_q]
  rw [hq]
  unfold h density
  field_simp [lambda_ne_zero, q_ne_zero, hg]
  linear_combination -6*bridge

theorem actual_divergence_compact : fieldDivergence physicalPartial actualPhysical =
    -splitF*baseEmbedding (Cubic.R0 pc qc)/(18*q*lambda^5*baseEmbedding (Cubic.G pc qc)) := by
  have hg : baseEmbedding (Cubic.G pc qc) ≠ 0 := (map_ne_zero baseEmbedding).mpr actualG_ne_zero
  have bridge := congrArg baseEmbedding (Cubic.R0_bridge pc qc)
  simp only [map_sub, map_mul, map_ofNat] at bridge
  rw [actual_physical_equations.2, actual_dp]
  simp only [map_mul, map_div₀, map_ofNat]
  have hp : baseEmbedding (Cubic.f pc) = p := by rw [← fourP_cubic, baseEmbedding_p]
  have hq : baseEmbedding (Cubic.f qc) = q := by rw [← fourQ_cubic, baseEmbedding_q]
  rw [hp] at bridge
  rw [hq]
  field_simp [lambda_ne_zero, p_ne_zero, q_ne_zero, hg]
  linear_combination 108*splitF*bridge

end HodgeTestbed.EllipticAmbient
