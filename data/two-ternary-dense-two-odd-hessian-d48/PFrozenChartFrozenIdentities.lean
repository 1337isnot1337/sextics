import Proposal.PFrozenChartChartRules
import Proposal.PFrozenChartNormalDerivative

/-! # Frozen F and A in the genuine square cover and X0 fraction-field chart -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.FrozenChart
open MvPolynomial

@[simp] theorem embed_X {n : ℕ} (i : Fin n) : embed (X i) = coord i := rfl

@[simp] theorem squareCoverPoly_X (i : Fin 5) :
    squareCoverPoly (X i) = if i = 3 then X 3 ^ 2 else X i := aeval_X _ _

@[simp] theorem chartPoly_X (i : Fin 5) :
    chartPoly (X i) = coord i.succ / coord (0 : Fin 6) :=
  (chart_embed (X i)).symm.trans (chart_coord i)

/-- The exact frozen twenty-term F, with no polynomial-identity hypothesis. -/
theorem frozen_F_chart : embed Frozen.F =
    coord (0 : Fin 6) ^ 6 * chart (squareCover quotientH) := by
  rw [quotientH, squareCover_embed, chart_embed]
  simp only [Frozen.F, Frozen.X0, Frozen.X1, Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2,
    H, map_add, map_mul, map_pow, map_ofNat, squareCoverPoly_X, embed_X]
  have hs0 : (0 : Fin 5).succ = (1 : Fin 6) := rfl
  have hs1 : (1 : Fin 5).succ = (2 : Fin 6) := rfl
  have hs2 : (2 : Fin 5).succ = (3 : Fin 6) := rfl
  have hs3 : (3 : Fin 5).succ = (4 : Fin 6) := rfl
  have hs4 : (4 : Fin 5).succ = (5 : Fin 6) := rfl
  norm_num [Fin.ext_iff, hs0, hs1, hs2, hs3, hs4]
  field_simp [coord_ne_zero (0 : Fin 6)]

/-- The actual selected A=X0^5*Y1 is precisely the transported target. -/
theorem frozen_A_chart : embed Frozen.A = coord (0 : Fin 6) ^ 6 * chart (coord (3 : Fin 5)) := by
  simp only [Frozen.A, Frozen.X0, Frozen.Y1, map_mul, map_pow, embed_X, chart_coord]
  field_simp [coord_ne_zero (0 : Fin 6)]
  rfl

end HodgeTestbed.FrozenChart
