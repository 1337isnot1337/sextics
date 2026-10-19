import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Exact algebra for the endpoint cubic reduction. The order of the four
active coordinates throughout this file is `(U,V,S,T)`, with normalized
`T = k*c*d`. No assertion of certificate existence is assumed here. -/

noncomputable section
namespace HoldoutAlgebra

variable {R : Type*} [CommRing R]

def sextic (x a c y b d : R) : R :=
  x^6 + a^6 + c^6 + y^6 + b^6 + d^6 + x^3*a*y*b + a^3*c*b*d

def target (x a c y b : R) : R := x^3*a^2*c^2*y^3*b^2

def commonTarget (x a y b : R) : R := x^3*a^2*y^3*b^2

def delta (k c d : R) : R := c^2-k^2*d^2

def cubic (aa bb cc dd U V S T : R) : R :=
  S^3-3*S*T^2+aa*U^3+bb*V^3+cc*U^2*V+dd*V^2*T

theorem cube_eq_one {k : R} (hk : k^2+k+1=0) : k^3=1 := by
  linear_combination (k-1)*hk

theorem sixth_eq_one {k : R} (hk : k^2+k+1=0) : k^6=1 := by
  calc k^6 = (k^3)^2 := by ring
       _ = 1 := by rw [cube_eq_one hk]; ring

theorem square_is_root {k : R} (hk : k^2+k+1=0) : (k^2)^2+k^2+1=0 := by
  linear_combination (k^2-k+1)*hk

theorem delta_swap {k : R} (hk : k^2+k+1=0) (c d : R) :
    delta k (k*d) (k^2*c) = -delta k c d := by
  have h6 := sixth_eq_one hk
  dsimp [delta]
  linear_combination -c^2*h6

theorem sextic_reflection {k : R} (hk : k^2+k+1=0)
    (x a c y b d : R) :
    sextic x a (k*d) y b (k^2*c) = sextic x a c y b d := by
  have h3 := cube_eq_one hk
  have h6 := sixth_eq_one hk
  have h12 : k^12=1 := by
    calc k^12 = (k^6)^2 := by ring
         _ = 1 := by rw [h6]; ring
  dsimp [sextic]
  linear_combination d^6*h6+c^6*h12+a^3*b*c*d*h3

/-- Polynomial substitution before introducing passive ratios. -/
theorem cubic_substitution {k : R} (hk : k^2+k+1=0)
    (α β x a c d : R) :
    cubic (1+α^6) (1+β^6) (α*β) (β*k^2)
      (x^2) (a^2) (c^2+k^2*d^2) (k*c*d) =
      sextic x a c (α*x) (β*a) d := by
  have h3 := cube_eq_one hk
  have h6 := sixth_eq_one hk
  dsimp [cubic, sextic]
  linear_combination d^6*h6+β*a^4*c*d*h3

theorem commonTarget_substitution (α β x a : R) :
    α^3*β^2*(x^2)^3*(a^2)^2 = commonTarget x a (α*x) (β*a) := by
  dsimp [commonTarget]
  ring

/-- The coefficient specialization used for every finite-algebra unit check. -/
theorem coefficients_good {k : R} (hk : k^2+k+1=0) :
    (1+(k^2)^6, 1+k^6, k^2*k, k*k^2) = (2,2,1,1) := by
  have h3 := cube_eq_one hk
  have h6 := sixth_eq_one hk
  have h12 : (k^2)^6=1 := by
    calc (k^2)^6 = (k^6)^2 := by ring
         _ = 1 := by rw [h6]; ring
  simp only [h6,h12]
  have h21 : k^2*k=1 := by linear_combination h3
  have h12' : k*k^2=1 := by linear_combination h3
  norm_num [h21,h12']

/-- On the denominator test fiber the sextic is exactly `c^6+5`. -/
theorem sextic_good_fiber {k : R} (hk : k^2+k+1=0) (c : R) :
    sextic 1 1 c (k^2) k 0 = c^6+5 := by
  have h6 := sixth_eq_one hk
  have h3 := cube_eq_one hk
  have h12 : k^12=1 := by
    calc k^12 = (k^6)^2 := by ring
         _ = 1 := by rw [h6]; ring
  dsimp [sextic]
  linear_combination h12+h6+h3

section Field
variable {K : Type*} [Field K]

theorem cubic_ratio_substitution {k : K} (hk : k^2+k+1=0)
    (x a c y b d : K) (hx : x≠0) (ha : a≠0) :
    cubic (1+(y/x)^6) (1+(b/a)^6) ((y/x)*(b/a)) ((b/a)*k^2)
      (x^2) (a^2) (c^2+k^2*d^2) (k*c*d) = sextic x a c y b d := by
  simpa only [div_mul_cancel₀ _ hx, div_mul_cancel₀ _ ha]
    using cubic_substitution hk (y/x) (b/a) x a c d

theorem source_ratio_substitution (x a y b : K) (hx : x≠0) (ha : a≠0) :
    (y/x)^3*(b/a)^2*(x^2)^3*(a^2)^2 = commonTarget x a y b := by
  simpa only [div_mul_cancel₀ _ hx, div_mul_cancel₀ _ ha]
    using commonTarget_substitution (y/x) (b/a) x a

end Field
end HoldoutAlgebra

#print axioms HoldoutAlgebra.cubic_substitution
#print axioms HoldoutAlgebra.sextic_reflection
