import Mathlib.Tactic.Ring

/-! Universal polynomial identities for the one-parameter chart of cubic lines.
Every statement here is over an arbitrary commutative ring. -/
namespace GenericLineChart
variable {K : Type*} [CommRing K]

def cubic (p q s k u v S T B C : K) : K :=
  2*S^3 + S*T^2 + S*(p*B^2+q*B*C+s*C^2) + k*T*B*C + u*B^3 + v*C^3

def hNum (r u v : K) : K := v-u*r^3

def aa (r p q s k u v : K) : K :=
  (hNum r u v)^2+k^2*r^2*(p*r^2-q*r+s)

def bb (r u v : K) : K := v+2*u*r^3

def qa (r p q s k u v : K) : K := 2*hNum r u v*aa r p q s k u v

def qb (r p s k u v : K) : K :=
  k^2*r*(2*hNum r u v*bb r u v+(hNum r u v)^2+k^2*r^2*(s-p*r^2))

def qc (r k u v : K) : K := k^4*r^2*hNum r u v

def cd (r p q s k u v : K) : K := (aa r p q s k u v)^2+2*k^6*r^6

def ce (r p q s k u v : K) : K := 2*k^2*r*aa r p q s k u v*bb r u v

def cf (r p k u v : K) : K := k^4*r^2*((bb r u v)^2+p*k^2*r^4)

def cg (r k u : K) : K := u*k^6*r^6

def quadratic (r p q s k u v x : K) : K :=
  qa r p q s k u v*x^2 + qb r p s k u v*x + qc r k u v

def cubicEq (r p q s k u v x : K) : K :=
  cd r p q s k u v*x^3 + ce r p q s k u v*x^2 + cf r p k u v*x + cg r k u

/-- Clearing the common scale of all four line coordinates leaves only the
quadratic and cubic equations, with the other two line coefficients zero. -/
theorem scaled_chart_expansion (r p q s k u v x U C : K) :
    cubic p q s k u v
      (k^3*r^3*x*U)
      ((aa r p q s k u v*x+k^2*r*bb r u v)*U+k^2*r^2*hNum r u v*C)
      (k^3*r^3*(U-r*C)) (k^3*r^3*C)
    = k^3*r^3*cubicEq r p q s k u v x*U^3 +
      k^5*r^5*quadratic r p q s k u v x*U^2*C := by
  unfold cubic cubicEq quadratic qa qb qc cd ce cf cg aa bb hNum
  ring

/-- A simultaneous root of the quadratic and cubic gives a line on the cubic. -/
theorem scaled_line (r p q s k u v x U C : K)
    (hQ : quadratic r p q s k u v x = 0)
    (hC : cubicEq r p q s k u v x = 0) :
    cubic p q s k u v
      (k^3*r^3*x*U)
      ((aa r p q s k u v*x+k^2*r*bb r u v)*U+k^2*r^2*hNum r u v*C)
      (k^3*r^3*(U-r*C)) (k^3*r^3*C) = 0 := by
  rw [scaled_chart_expansion, hQ, hC]
  ring

end GenericLineChart
