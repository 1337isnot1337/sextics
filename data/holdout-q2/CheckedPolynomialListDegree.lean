import Proposal.CheckedPolynomialLists
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.List.GetD

namespace CheckedPolynomialLists
open Polynomial

lemma coeff_encode (xs : List ℚ) (n : ℕ) : (encode xs).coeff n = xs.getD n 0 := by
  induction xs generalizing n with
  | nil => simp [encode]
  | cons x xs ih =>
    cases n with
    | zero => simp [encode]
    | succ n => simp [encode, coeff_X_mul, ih]

lemma natDegree_encode_le (xs : List ℚ) (n : ℕ) (h : xs.length ≤ n+1) :
    (encode xs).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [coeff_encode]
  exact List.getD_eq_default _ _ (le_trans h (Nat.succ_le_iff.mpr hm))

end CheckedPolynomialLists

