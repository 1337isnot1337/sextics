import Proposal.PFrozenChartSquareCover
import Mathlib.RingTheory.Localization.Away.Basic

/-! # The actual injective rational chart Xi/X0 -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.FrozenChart
open MvPolynomial

abbrev ChartRing := Localization.Away (X (0 : Fin 6) : Poly 6)

def awayEmbed : Poly 6 →ₐ[ℚ] ChartRing := IsScalarTower.toAlgHom ℚ (Poly 6) ChartRing

def awayEval : ChartRing →ₐ[ℚ] Poly 5 :=
  IsLocalization.Away.liftAlgHom (X (0 : Fin 6)) (f := dehomogenize) (by
    have hx : dehomogenize (X (0 : Fin 6)) = 1 := aeval_X _ _
    rw [hx]
    exact isUnit_one)

def awayFrac : ChartRing →ₐ[ℚ] RatFun 6 :=
  IsLocalization.Away.liftAlgHom (X (0 : Fin 6)) (f := embed)
    (isUnit_iff_ne_zero.mpr (coord_ne_zero 0))

@[simp] theorem awayEval_embed (p : Poly 6) : awayEval (awayEmbed p) = dehomogenize p :=
  IsLocalization.lift_eq _ p
@[simp] theorem awayFrac_embed (p : Poly 6) : awayFrac (awayEmbed p) = embed p :=
  IsLocalization.lift_eq _ p

def inverseScale : ChartRing := IsLocalization.Away.invSelf (S := ChartRing) (X (0 : Fin 6) : Poly 6)

theorem scale_mul_inverseScale : awayEmbed (X (0 : Fin 6)) * inverseScale = 1 :=
  IsLocalization.Away.mul_invSelf (S := ChartRing) (X (0 : Fin 6) : Poly 6)

@[simp] theorem awayEval_inverseScale : awayEval inverseScale = 1 := by
  have hh := congrArg awayEval scale_mul_inverseScale
  have hx : dehomogenize (X (0 : Fin 6)) = 1 := aeval_X _ _
  simpa only [map_mul, awayEval_embed, hx, one_mul, map_one] using hh

@[simp] theorem awayFrac_inverseScale : awayFrac inverseScale = (coord (0 : Fin 6))⁻¹ := by
  have hh := congrArg awayFrac scale_mul_inverseScale
  apply mul_left_cancel₀ (coord_ne_zero (0 : Fin 6))
  rw [mul_inv_cancel₀ (coord_ne_zero (0 : Fin 6))]
  exact (by simpa only [coord, map_mul, awayFrac_embed, map_one] using hh)

theorem awayFrac_injective : Function.Injective awayFrac := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers (X (0 : Fin 6) : Poly 6)) ChartRing awayFrac.toRingHom
  intro p hp
  change awayFrac (awayEmbed p) = 0 at hp
  rw [awayFrac_embed] at hp
  have hh := hp
  have hz : p = 0 := embed_injective (by simpa using hh)
  simp [hz]

def awayChart : Poly 5 →ₐ[ℚ] ChartRing :=
  aeval (fun i : Fin 5 => awayEmbed (X i.succ) * inverseScale)

theorem awayChart_leftInverse : awayEval.comp awayChart = AlgHom.id ℚ (Poly 5) := by
  ext1 i
  change awayEval (awayChart (X i)) = X i
  have hc : awayChart (X i) = awayEmbed (X i.succ) * inverseScale := aeval_X _ _
  have hd : dehomogenize (X i.succ) = X i := aeval_X _ _
  rw [hc, map_mul, awayEval_embed, hd, awayEval_inverseScale, mul_one]

def chartPoly : Poly 5 →ₐ[ℚ] RatFun 6 := awayFrac.comp awayChart

theorem chartPoly_injective : Function.Injective chartPoly := by
  apply awayFrac_injective.comp
  intro p q hpq
  have hh := congrArg awayEval hpq
  have hp := AlgHom.congr_fun awayChart_leftInverse p
  have hq := AlgHom.congr_fun awayChart_leftInverse q
  exact hp.symm.trans (hh.trans hq)

/-- The actual X0 rational chart; injection is proved using localization away from X0. -/
def chart : RatFun 5 →ₐ[ℚ] RatFun 6 :=
  IsFractionRing.liftAlgHom (g := chartPoly) chartPoly_injective

@[simp] theorem chart_embed (p : Poly 5) : chart (embed p) = chartPoly p :=
  IsLocalization.lift_eq _ p

@[simp] theorem chart_coord (i : Fin 5) : chart (coord i) = coord i.succ / coord (0 : Fin 6) := by
  rw [coord, chart_embed]
  change awayFrac (awayChart (X i)) = _
  have hc : awayChart (X i) = awayEmbed (X i.succ) * inverseScale := aeval_X _ _
  rw [hc, map_mul, awayFrac_embed, awayFrac_inverseScale]
  rfl

end HodgeTestbed.FrozenChart
