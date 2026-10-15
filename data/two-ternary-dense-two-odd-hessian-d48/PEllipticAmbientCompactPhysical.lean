import Proposal.PEllipticAmbientFactoredField

/-! Componentwise normalization of the actual physical field. -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart HodgeTestbed.Conic

theorem actual_liftBase (i : Fin 4) : liftBase (extendBase actualPrimitive) i =
    (![ -lambda*coord 0*baseEmbedding (Cubic.V pc qc)/(6*baseEmbedding (Cubic.G pc qc)),
        -lambda*coord 1*baseEmbedding (Cubic.V pc qc)/(6*baseEmbedding (Cubic.G pc qc)),
        lambda*coord 2*baseEmbedding (Cubic.f pc*Cubic.U1 pc qc)/(6*baseEmbedding (Cubic.G pc qc)),
        lambda*coord 3*baseEmbedding (Cubic.f pc*Cubic.U1 pc qc)/(6*baseEmbedding (Cubic.G pc qc))] : Fin 4 → K) i := by
  have hg : baseEmbedding (Cubic.G pc qc) ≠ 0 := (map_ne_zero baseEmbedding).mpr actualG_ne_zero
  have hp : baseEmbedding (Cubic.f pc) = p := by rw [← fourP_cubic, baseEmbedding_p]
  have hq : baseEmbedding (Cubic.f qc) = q := by rw [← fourQ_cubic, baseEmbedding_q]
  fin_cases i <;>
    norm_num [liftBase, baseField, scaledB, h, density, extendBase, actualPrimitive,
      primitiveFromW, actualT, actualS, actualNP, actualNQ, Cubic.U, Cubic.U1,
      fourP_cubic, fourQ_cubic, map_div₀, map_mul, map_neg, map_ofNat, baseEmbedding_coord,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  all_goals rw [hp, hq]
  all_goals try simp only [show Fin.castSucc (2 : Fin 4) = (2 : Fin 5) from rfl,
    show Fin.castSucc (3 : Fin 4) = (3 : Fin 5) from rfl]
  all_goals field_simp [lambda_ne_zero, p_ne_zero, q_ne_zero, hg]
  all_goals ring

def compactNormal : K := baseEmbedding (Cubic.f pc)*
    (baseEmbedding (Cubic.R0 pc qc)-lambda^6*baseEmbedding (Cubic.U1 pc qc*Cubic.rf qc))/
    (36*q*lambda^4*baseEmbedding (Cubic.G pc qc))
def compactQfactor : K := baseEmbedding (Cubic.f pc)*
    (baseEmbedding (Cubic.R0 pc qc)+2*lambda^6*baseEmbedding (Cubic.fp qc*Cubic.U1 pc qc))/
    (36*q*lambda^4*baseEmbedding (Cubic.G pc qc))

theorem actualPhysical_compact (i : Fin 5) : actualPhysical i =
    (![ -lambda*coord 0*baseEmbedding (Cubic.V pc qc)/(6*baseEmbedding (Cubic.G pc qc)),
         coord 2*compactQfactor,
        -lambda*coord 1*baseEmbedding (Cubic.V pc qc)/(6*baseEmbedding (Cubic.G pc qc)),
         compactNormal, coord 3*compactQfactor] : Fin 5 → K) i := by
  have hg : baseEmbedding (Cubic.G pc qc) ≠ 0 := (map_ne_zero baseEmbedding).mpr actualG_ne_zero
  have hq : baseEmbedding (Cubic.f qc) = q := by rw [← fourQ_cubic, baseEmbedding_q]
  fin_cases i <;>
    norm_num [actualPhysical, physicalField, actual_liftBase, actual_liftNormal,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  all_goals simp only [compactNormal, compactQfactor, Cubic.rf, map_mul, map_sub, map_ofNat, hq]
  all_goals field_simp [lambda_ne_zero, q_ne_zero, hg]
  all_goals ring

end HodgeTestbed.EllipticAmbient
