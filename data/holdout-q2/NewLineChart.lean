import Mathlib.Tactic.Ring

/-! Universal identities constructing a line on the holdout cubic.  All
identities are polynomial and hold over any commutative ring. -/
namespace HoldoutQ2.NewLineChart
variable {R : Type*} [CommRing R]

def cubic (a b c d U V S T : R) : R :=
  S^3-3*S*T^2+a*U^3+b*V^3+c*U^2*V+d*V^2*T

def kappa (r a b c : R) : R := a*r^3-c*r^2-b
def tt (r a c : R) : R := 3*a*r-2*c
def uu (r a c : R) : R := c-3*a*r

def coordinateNum (r a b c d : R) : R :=
  27*d^2*(uu r a c)^2*(kappa r a b c)^5 -
    d^8*uu r a c*(2*r^2*(tt r a c)^2+kappa r a b c*uu r a c)
def coordinateDen (r a b c d : R) : R :=
  12*kappa r a b c*(27*a*(kappa r a b c)^6+
    d^6*r^3*(tt r a c)^3+kappa r a b c*d^6*r*tt r a c*uu r a c)

def qa (r a b c : R) : R := -18*(kappa r a b c)^3
def qb (r a b c d : R) : R := 6*kappa r a b c*d^2*r*tt r a c
def qc (r a c d : R) : R := d^4*uu r a c
def qe (r a b c : R) : R := 12*(kappa r a b c)^2
def qf (r a b c : R) : R := 12*a*(kappa r a b c)^2
def qh (r a c d : R) : R := -d^2*(uu r a c)^2

def quadratic (r a b c d e : R) : R :=
  qa r a b c*e^2+qb r a b c d*e+qc r a c d
def quartic (r a b c d e : R) : R :=
  qe r a b c*e^4+qf r a b c*e+qh r a c d

def linearCoeff (A B C E F : R) : R := E*(-B^3+2*A*B*C)+F*A^3
def constantCoeff (A B C E H : R) : R := E*(-B^2*C+A*C^2)+H*A^3

theorem quartic_division (A B C E F H z : R) :
    A^3*(E*z^4+F*z+H) =
      (A*z^2+B*z+C)*E*(A^2*z^2-A*B*z+B^2-A*C)+
      linearCoeff A B C E F*z+constantCoeff A B C E H := by
  unfold linearCoeff constantCoeff
  ring

theorem linearCoeff_factor (r a b c d : R) :
    linearCoeff (qa r a b c) (qb r a b c d) (qc r a c d)
      (qe r a b c) (qf r a b c) =
    -216*(kappa r a b c)^4*coordinateDen r a b c d := by
  unfold linearCoeff qa qb qc qe qf coordinateDen
  ring

theorem constantCoeff_factor (r a b c d : R) :
    constantCoeff (qa r a b c) (qb r a b c d) (qc r a c d)
      (qe r a b c) (qh r a c d) =
    216*(kappa r a b c)^4*coordinateNum r a b c d := by
  unfold constantCoeff qa qb qc qe qh coordinateNum
  ring

/-- The four line equations have two common scalar remainders. -/
theorem scaled_chart (r a b c d e U V : R) :
    cubic a b c d
      (6*kappa r a b c*e*d*U) (6*kappa r a b c*e*d*V)
      (6*kappa r a b c*e*d*(e*U+r*e*V))
      (d^2*uu r a c*U+(r*d^2*uu r a c+6*(kappa r a b c)^2*e)*V) =
    (6*kappa r a b c*e*d)*(
      3*d^2*e*quartic r a b c d e*U^3 +
      9*d^2*r*e*quartic r a b c d e*U^2*V +
      (9*d^2*r^2*e*quartic r a b c d e+6*kappa r a b c*e*quadratic r a b c d e)*U*V^2 +
      (3*d^2*r^3*e*quartic r a b c d e+6*r*kappa r a b c*e*quadratic r a b c d e)*V^3) := by
  unfold cubic quartic quadratic qa qb qc qe qf qh kappa tt uu
  ring

theorem homogeneous (a b c d U V S T z : R) :
    cubic a b c d (z*U) (z*V) (z*S) (z*T) = z^3*cubic a b c d U V S T := by
  unfold cubic
  ring

/-- Passing from the two equations to an actual unscaled line uses only
units explicitly accounted for by the finite algebra specialization. -/
theorem line_of_common_root (r a b c d e f g h : R)
    (hf : f=r*e)
    (hg : (6*kappa r a b c*e*d)*g=d^2*uu r a c)
    (hh : (6*kappa r a b c*e*d)*h=r*d^2*uu r a c+6*(kappa r a b c)^2*e)
    (hunit : IsUnit (6*kappa r a b c*e*d))
    (hQ : quadratic r a b c d e=0) (hR : quartic r a b c d e=0)
    (U V : R) : cubic a b c d U V (e*U+f*V) (g*U+h*V)=0 := by
  apply (hunit.pow 3).mul_right_eq_zero.mp
  rw [← homogeneous]
  have hs : (6*kappa r a b c*e*d)*(g*U+h*V) =
      d^2*uu r a c*U+(r*d^2*uu r a c+6*(kappa r a b c)^2*e)*V := by
    calc
      _ = ((6*kappa r a b c*e*d)*g)*U+((6*kappa r a b c*e*d)*h)*V := by ring
      _ = _ := by rw [hg,hh]
  rw [hs,hf,scaled_chart,hQ,hR]
  ring

def rel0 (a e g : R) : R := e^3-3*e*g^2+a
def rel1 (c e f g h : R) : R := 3*e^2*f-3*(2*e*g*h+f*g^2)+c
def rel2 (d e f g h : R) : R := 3*e*f^2-3*(e*h^2+2*f*g*h)+d*g
def rel3 (b d f h : R) : R := f^3-3*f*h^2+b+d*h

end HoldoutQ2.NewLineChart
