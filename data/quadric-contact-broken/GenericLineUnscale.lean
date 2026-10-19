import Proposal.GenericLineChart
import Mathlib.Algebra.GroupWithZero.Units.Basic

namespace GenericLineChart
variable {K : Type*} [CommRing K]

noncomputable def lineZ (r p q s k u v x : K) : K :=
  (aa r p q s k u v*x+k^2*r*bb r u v)*Ring.inverse (k^3*r^3)
noncomputable def lineW (r p q s k u v x : K) : K :=
  r*lineZ r p q s k u v x+hNum r u v*Ring.inverse (k*r)

theorem cubic_scale (p q s k u v S T B C m : K) :
    cubic p q s k u v (m*S) (m*T) (m*B) (m*C) =
      m^3*cubic p q s k u v S T B C := by
  unfold cubic
  ring

/-- Remove the scale factors from the polynomial line chart using certified units. -/
theorem unscaled_line (r p q s k u v x B C : K)
    (hk : IsUnit k) (hr : IsUnit r)
    (hQ : quadratic r p q s k u v x = 0)
    (hC : cubicEq r p q s k u v x = 0) :
    cubic p q s k u v (x*B+(r*x)*C)
      (lineZ r p q s k u v x*B+lineW r p q s k u v x*C) B C = 0 := by
  let m := k^3*r^3
  have hm : IsUnit m := (hk.pow 3).mul (hr.pow 3)
  have hz : m*lineZ r p q s k u v x = aa r p q s k u v*x+k^2*r*bb r u v := by
    unfold lineZ
    rw [mul_left_comm, Ring.mul_inverse_cancel _ hm, mul_one]
  have hw : m*lineW r p q s k u v x =
      r*(aa r p q s k u v*x+k^2*r*bb r u v)+k^2*r^2*hNum r u v := by
    unfold lineW
    rw [mul_add, mul_left_comm m r, hz]
    congr 1
    calc
      m*(hNum r u v*Ring.inverse (k*r)) =
        (k^2*r^2*hNum r u v)*((k*r)*Ring.inverse (k*r)) := by dsimp [m]; ring
      _ = k^2*r^2*hNum r u v := by rw [Ring.mul_inverse_cancel _ (hk.mul hr), mul_one]
  have hh := scaled_line r p q s k u v x (B+r*C) C hQ hC
  have he : cubic p q s k u v (m*(x*B+(r*x)*C))
      (m*(lineZ r p q s k u v x*B+lineW r p q s k u v x*C)) (m*B) (m*C) = 0 := by
    convert hh using 1 <;> dsimp [m] at *
    · congr 1 <;> try ring
      calc
        _ = (k^3*r^3*lineZ r p q s k u v x)*B+
              (k^3*r^3*lineW r p q s k u v x)*C := by ring
        _ = _ := by rw [hz, hw]; ring
  rw [cubic_scale] at he
  exact (hm.pow 3).mul_right_eq_zero.mp he

end GenericLineChart
