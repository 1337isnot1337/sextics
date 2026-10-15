import Proposal.PFrozenChartPolynomial
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.CharP.Algebra

/-! # Actual rational partial derivations, constructed by first-order jets -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.FrozenChart
open MvPolynomial

abbrev RatFun (n : ℕ) := FractionRing (Poly n)

instance ratFunCharZero (n : ℕ) : CharZero (RatFun n) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (RatFun n)).injective

def embed {n : ℕ} : Poly n →ₐ[ℚ] RatFun n := IsScalarTower.toAlgHom ℚ (Poly n) (RatFun n)
def coord {n : ℕ} (i : Fin n) : RatFun n := embed (X i)

def jetPoly {n : ℕ} (i : Fin n) : Poly n →ₐ[ℚ] TrivSqZeroExt (RatFun n) (RatFun n) :=
  aeval (fun j => ⟨coord j, if i = j then 1 else 0⟩)

theorem jetPoly_fst {n : ℕ} (i : Fin n) (p : Poly n) : (jetPoly i p).fst = embed p := by
  have he : (TrivSqZeroExt.fstHom ℚ (RatFun n) (RatFun n)).comp (jetPoly i) = embed := by
    ext j
    change (jetPoly i (X j)).fst = coord j
    have hx : jetPoly i (X j) = ⟨coord j, if i = j then 1 else 0⟩ := aeval_X _ _
    rw [hx]
    rfl
  exact AlgHom.congr_fun he p

theorem jetPoly_snd {n : ℕ} (i : Fin n) (p : Poly n) :
    (jetPoly i p).snd = embed (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [jetPoly, TrivSqZeroExt.algebraMap_eq_inl']
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p j hp =>
    have hx : jetPoly i (X j) = ⟨coord j, if i = j then 1 else 0⟩ := aeval_X _ _
    rw [map_mul, TrivSqZeroExt.snd_mul, jetPoly_fst, hp, hx]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, pderiv_X,
      Pi.single_apply, coord, TrivSqZeroExt.fst, TrivSqZeroExt.snd]
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [hij, Ne.symm hij]
      ring

/-- Localization of the polynomial first-order jet: denominators are units by their first part. -/
def jet {n : ℕ} (i : Fin n) : RatFun n →ₐ[ℚ] TrivSqZeroExt (RatFun n) (RatFun n) :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors (Poly n)) (S := RatFun n)
    (f := jetPoly i) (fun p => by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, jetPoly_fst]
      exact IsFractionRing.isUnit_map_of_injective (IsFractionRing.injective (Poly n) (RatFun n)) p)

theorem jet_embed {n : ℕ} (i : Fin n) (p : Poly n) : jet i (embed p) = jetPoly i p :=
  IsLocalization.lift_eq _ p

theorem jet_fst {n : ℕ} (i : Fin n) (z : RatFun n) : (jet i z).fst = z := by
  have he : ((TrivSqZeroExt.fstHom ℚ (RatFun n) (RatFun n)).comp (jet i)).toRingHom =
      RingHom.id (RatFun n) := by
    apply IsFractionRing.ringHom_ext (A := Poly n)
    intro p
    exact (congrArg TrivSqZeroExt.fst (jet_embed i p)).trans (jetPoly_fst i p)
  exact RingHom.congr_fun he z

/-- The genuine partial derivative on the fraction field of QQ multivariate polynomials. -/
def rationalPartial {n : ℕ} (i : Fin n) : Derivation ℚ (RatFun n) (RatFun n) where
  toLinearMap := ((TrivSqZeroExt.sndHom (RatFun n) (RatFun n)).restrictScalars ℚ).comp
    (jet i).toLinearMap
  map_one_eq_zero' := by simp
  leibniz' := by
    intro x y
    simp [TrivSqZeroExt.snd_mul, jet_fst, smul_eq_mul, mul_comm]

theorem partial_embed {n : ℕ} (i : Fin n) (p : Poly n) :
    rationalPartial i (embed p) = embed (pderiv i p) := by
  change (jet i (embed p)).snd = _
  rw [jet_embed, jetPoly_snd]

@[simp] theorem partial_coord {n : ℕ} (i j : Fin n) :
    rationalPartial i (coord j) = if i = j then 1 else 0 := by
  rw [coord, partial_embed]
  simp [pderiv_X, Pi.single_apply, eq_comm]

end HodgeTestbed.FrozenChart
