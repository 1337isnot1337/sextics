import Proposal.PEllipticAmbientFourVariable
import Proposal.PFrozenChartSquareCover

/-! # Genuine extension from the four-variable rational coefficient field -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart HodgeTestbed.Conic HodgeTestbed.Incidence
open MvPolynomial

abbrev K4 := RatFun 4
/-- The first four variables are preserved; the fifth variable is transcendental. -/
def baseEmbedding : K4 →ₐ[ℚ] K :=
  IsFractionRing.liftAlgHom (g := embed.comp (rename Fin.castSucc))
    (embed_injective.comp (rename_injective _ (Fin.castSucc_injective 4)))

@[simp] theorem baseEmbedding_embed (f : Poly 4) :
    baseEmbedding (embed f) = embed (rename Fin.castSucc f) := IsLocalization.lift_eq _ f
@[simp] theorem baseEmbedding_coord (j : Fin 4) :
    baseEmbedding (coord j) = coord j.castSucc := by simp [coord]

/-- The four-variable extension commutes with genuine rational partial derivatives. -/
theorem baseEmbedding_partial (i : Fin 4) (f : K4) :
    basePartial i (baseEmbedding f) = baseEmbedding (rationalPartial i f) := by
  simpa using compatibility_of_coordinates baseEmbedding (basePartial i) (rationalPartial i)
    1 (fun j => by simp [partial_coord]) f

/-- Every extended four-variable rational function is independent of λ. -/
theorem baseEmbedding_normal (f : K4) : normalPartial (baseEmbedding f) = 0 := by
  have hh := compatibility_of_coordinates baseEmbedding normalPartial
    (0 : Derivation ℚ K4 K4) 0 (fun j => by
      simp only [baseEmbedding_coord, partial_coord, zero_mul]
      split_ifs with hj
      · have he : j.val = 4 := (congrArg Fin.val hj).symm
        omega
      · rfl) f
  simpa using hh

def fourP : K4 := P 1 (coord 0 ^ 2) (coord 1 ^ 2)
def fourQ : K4 := Q (coord 2 ^ 2) 1 (coord 3 ^ 2)
def fourL4 (B : Fin 4 → K4) : K4 :=
  fieldDivergence rationalPartial B - fieldAction rationalPartial B fourP / (3 * fourP) +
    fieldAction rationalPartial B fourQ / (3 * fourQ)
def fourLW (W : Fin 4 → K4) : K4 :=
  fieldDivergence rationalPartial W - 4 * fieldAction rationalPartial W fourP / (3 * fourP) -
    2 * fieldAction rationalPartial W fourQ / (3 * fourQ)
def extendBase (B : Fin 4 → K4) (i : Fin 4) : K := baseEmbedding (B i)

@[simp] theorem baseEmbedding_p : baseEmbedding fourP = p := by
  rw [p_formula]
  simp [fourP, P, baseEmbedding_coord, map_ofNat]
@[simp] theorem baseEmbedding_q : baseEmbedding fourQ = q := by
  rw [q_formula]
  simp [fourQ, Q, baseEmbedding_coord, map_ofNat]

/-- Both the coefficients and the derivatives transfer from the actual four-variable field. -/
theorem baseEmbedding_L4 (B : Fin 4 → K4) : baseEmbedding (fourL4 B) = L4 (extendBase B) := by
  have haction (f : K4) : baseEmbedding (fieldAction rationalPartial B f) =
      fieldAction basePartial (extendBase B) (baseEmbedding f) := by
    simp only [fieldAction_apply, map_sum, map_mul, extendBase, baseEmbedding_partial]
  simp only [fourL4, map_add, map_sub, map_div₀, map_mul, map_ofNat,
    haction, baseEmbedding_p, baseEmbedding_q, L4, dp, dq]
  congr 2
  simp only [fieldDivergence, map_sum, extendBase, baseEmbedding_partial]

theorem baseEmbedding_LW (B : Fin 4 → K4) : baseEmbedding (fourLW B) = LW (extendBase B) := by
  simp only [fourLW, LW, dp, dq, fieldAction_apply, fieldDivergence, map_sub, map_div₀,
    map_mul, map_ofNat, map_sum, extendBase, ← baseEmbedding_p, ← baseEmbedding_q,
    baseEmbedding_partial]

/-- A supplied four-variable scalar primitive yields the full frozen split-chart identity.
The conclusion retains its explicit F-multiple rather than claiming divergence zero. -/
theorem four_variable_lift (B : Fin 4 → K4)
    (hprimitive : fourL4 B = 1 / (18 * fourP * fourQ)) :
    ambientAction basePartial normalPartial (liftBase (extendBase B))
      (liftNormal (extendBase B)) splitF = lambda ∧
    liftDivergence (extendBase B) =
      -splitF * (1 + 6 * q * dp (extendBase B)) / (3 * p * q * lambda ^ 5) := by
  refine ⟨lifted_first _, lifted_divergence_of_primitive _ (fun i => baseEmbedding_normal _) ?_⟩
  rw [← baseEmbedding_L4, hprimitive]
  simp [map_ofNat]

end HodgeTestbed.EllipticAmbient
