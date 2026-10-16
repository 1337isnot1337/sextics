import Proposal.PEllipticAmbientPhysical
import Proposal.PFrozenChartFrozenIdentities

/-! # Genuine rational split-to-homogeneous chart

The five independent split variables map to X1/X0,Y0/X0,X2/Y1,Y2/Y1,Y1/X0.
Injectivity is proved in the localization at X0*Y1, using a left inverse.
-/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart MvPolynomial

@[simp] theorem splitX0 : splitSubstitution (X (0 : Fin 6)) = 1 := by
  rw [splitSubstitution, aeval_X]
  rfl
@[simp] theorem splitX1 : splitSubstitution (X (1 : Fin 6)) = coord (0 : Fin 5) := by
  rw [splitSubstitution, aeval_X]
  rfl
@[simp] theorem splitX2 : splitSubstitution (X (2 : Fin 6)) = lambda * coord (2 : Fin 5) := by
  rw [splitSubstitution, aeval_X]
  rfl
@[simp] theorem splitX3 : splitSubstitution (X (3 : Fin 6)) = coord (1 : Fin 5) := by
  rw [splitSubstitution, aeval_X]
  rfl
@[simp] theorem splitX4 : splitSubstitution (X (4 : Fin 6)) = lambda := by
  rw [splitSubstitution, aeval_X]
  rfl
@[simp] theorem splitX5 : splitSubstitution (X (5 : Fin 6)) = lambda * coord (3 : Fin 5) := by
  rw [splitSubstitution, aeval_X]
  rfl

abbrev K6 := RatFun 6
def chartProduct : Poly 6 := X 0 * X 4
abbrev SplitAway := Localization.Away chartProduct
def splitAwayEmbed : Poly 6 →ₐ[ℚ] SplitAway := IsScalarTower.toAlgHom ℚ (Poly 6) SplitAway
def productInverse : SplitAway := IsLocalization.Away.invSelf (S := SplitAway) chartProduct

theorem product_mul_inverse : splitAwayEmbed chartProduct * productInverse = 1 :=
  IsLocalization.Away.mul_invSelf (S := SplitAway) chartProduct

def splitAwayFrac : SplitAway →ₐ[ℚ] K6 :=
  IsLocalization.Away.liftAlgHom chartProduct (f := embed) (by
    apply isUnit_iff_ne_zero.mpr
    simpa only [chartProduct, map_mul, embed_X] using mul_ne_zero (coord_ne_zero (0 : Fin 6)) (coord_ne_zero (4 : Fin 6)))
def splitAwayBack : SplitAway →ₐ[ℚ] K :=
  IsLocalization.Away.liftAlgHom chartProduct (f := splitSubstitution) (by
    apply isUnit_iff_ne_zero.mpr
    have hx : splitSubstitution (X (0 : Fin 6)) = 1 := splitX0
    have hy : splitSubstitution (X (4 : Fin 6)) = lambda := splitX4
    simpa only [chartProduct, map_mul, hx, hy, one_mul] using lambda_ne_zero)

@[simp] theorem splitAwayFrac_embed (f : Poly 6) : splitAwayFrac (splitAwayEmbed f) = embed f := IsLocalization.lift_eq _ f
@[simp] theorem splitAwayBack_embed (f : Poly 6) : splitAwayBack (splitAwayEmbed f) = splitSubstitution f := IsLocalization.lift_eq _ f

theorem splitAwayFrac_inverse : splitAwayFrac productInverse = (coord (0 : Fin 6)*coord 4)⁻¹ := by
  have hh := congrArg splitAwayFrac product_mul_inverse
  apply mul_left_cancel₀ (mul_ne_zero (coord_ne_zero (0 : Fin 6)) (coord_ne_zero (4 : Fin 6)))
  rw [mul_inv_cancel₀ (mul_ne_zero (coord_ne_zero (0 : Fin 6)) (coord_ne_zero (4 : Fin 6)))]
  simpa only [map_mul, splitAwayFrac_embed, chartProduct, coord, map_one] using hh

theorem splitAwayBack_inverse : splitAwayBack productInverse = lambda⁻¹ := by
  have hh := congrArg splitAwayBack product_mul_inverse
  apply mul_left_cancel₀ lambda_ne_zero
  rw [mul_inv_cancel₀ lambda_ne_zero]
  have hx : splitSubstitution (X (0 : Fin 6)) = 1 := splitX0
  have hy : splitSubstitution (X (4 : Fin 6)) = lambda := splitX4
  simpa only [map_mul, splitAwayBack_embed, chartProduct, hx, hy, one_mul, map_one] using hh

theorem splitAwayFrac_injective : Function.Injective splitAwayFrac := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers chartProduct) SplitAway splitAwayFrac.toRingHom
  intro f hf
  change splitAwayFrac (splitAwayEmbed f) = 0 at hf
  rw [splitAwayFrac_embed] at hf
  have hz : f = 0 := embed_injective (by simpa using hf)
  simp [hz]

def splitIntoAway : Poly 5 →ₐ[ℚ] SplitAway :=
  aeval ![splitAwayEmbed (X 1*X 4)*productInverse,
    splitAwayEmbed (X 3*X 4)*productInverse,
    splitAwayEmbed (X 2*X 0)*productInverse,
    splitAwayEmbed (X 5*X 0)*productInverse,
    splitAwayEmbed (X 4^2)*productInverse]

theorem splitIntoAway_leftInverse : splitAwayBack.comp splitIntoAway = embed := by
  ext1 i
  change splitAwayBack (splitIntoAway (X i)) = coord i
  fin_cases i <;>
    norm_num [splitIntoAway, splitAwayBack_inverse,
      Matrix.cons_val_succ, Matrix.cons_val_two, map_ofNat, splitX0, splitX1, splitX2, splitX3, splitX4, splitX5]
  all_goals field_simp [lambda_ne_zero]
  all_goals try simp only [lambda]
  all_goals first | rfl | ring

def homSplitPoly : Poly 5 →ₐ[ℚ] K6 := splitAwayFrac.comp splitIntoAway

theorem homSplitPoly_injective : Function.Injective homSplitPoly := by
  apply splitAwayFrac_injective.comp
  intro f g hfg
  apply embed_injective
  rw [← AlgHom.congr_fun splitIntoAway_leftInverse f, ← AlgHom.congr_fun splitIntoAway_leftInverse g]
  exact congrArg splitAwayBack hfg

def homSplit : K →ₐ[ℚ] K6 := IsFractionRing.liftAlgHom (g := homSplitPoly) homSplitPoly_injective
@[simp] theorem homSplit_embed (f : Poly 5) : homSplit (embed f) = homSplitPoly f := IsLocalization.lift_eq _ f

def homCoordinates : Fin 5 → K6 :=
  ![coord 1/coord 0, coord 3/coord 0, coord 2/coord 4, coord 5/coord 4, coord 4/coord 0]

theorem homSplit_coord (i : Fin 5) : homSplit (coord i) = homCoordinates i := by
  rw [coord, homSplit_embed]
  fin_cases i <;>
    norm_num [homSplitPoly, splitIntoAway, homCoordinates, splitAwayFrac_inverse,
      Matrix.cons_val_succ, Matrix.cons_val_two, embed_X]
  all_goals field_simp [coord_ne_zero (0 : Fin 6), coord_ne_zero (4 : Fin 6)]
  all_goals ring

end HodgeTestbed.EllipticAmbient
