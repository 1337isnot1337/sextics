import Mathlib.Tactic.Ring

namespace QuadricContact.Subresultant
variable {R : Type*} [CommRing R]

def quadratic (a b c x : R) := a*x^2+b*x+c
def cubic (d e f g x : R) := d*x^3+e*x^2+f*x+g
def linear (a b c d e f : R) := d*(b^2-a*c)-e*a*b+f*a^2
def constant (a b c d e g : R) := d*b*c-e*a*c+g*a^2
def resultant (a b c d e f g : R) :=
  a^3*g^2-a^2*b*f*g-2*a^2*c*e*g+a^2*c*f^2+
  a*b^2*e*g+3*a*b*c*d*g-a*b*c*e*f+a*c^2*e^2-
  2*a*c^2*d*f-b^3*d*g+b^2*c*d*f-b*c^2*d*e+c^3*d^2

theorem division_identity (a b c d e f g x : R) :
    a^2*cubic d e f g x =
    (a*d*x+a*e-b*d)*quadratic a b c x +
      linear a b c d e f*x+constant a b c d e g := by
  unfold cubic quadratic linear constant
  ring

theorem resultant_identity (a b c d e f g : R) :
    a*(constant a b c d e g)^2 -
      b*(constant a b c d e g)*(linear a b c d e f) +
      c*(linear a b c d e f)^2 = a^2*resultant a b c d e f g := by
  unfold constant linear resultant
  ring

theorem quadratic_identity (a b c l m x : R) :
    l^2*quadratic a b c x =
    a*(l*x+m)^2-(2*a*m-b*l)*(l*x+m)+(a*m^2-b*m*l+c*l^2) := by
  unfold quadratic
  ring

/-- A common root is constructed using only two certified inverses.
This applies in a finite commutative algebra; no irreducibility or field
assumption is required. -/
theorem common_root (a b c d e f g ia il : R)
    (ha : a*ia=1) (hl : linear a b c d e f*il=1)
    (hr : resultant a b c d e f g=0) :
    let x := -constant a b c d e g*il
    quadratic a b c x=0 ∧ cubic d e f g x=0 := by
  dsimp only
  let x := -constant a b c d e g*il
  have hx : linear a b c d e f*x+constant a b c d e g=0 := by
    dsimp [x]
    calc
      _ = constant a b c d e g*(1-linear a b c d e f*il) := by ring
      _ = 0 := by rw [hl]; ring
  have hqmul : (linear a b c d e f)^2*quadratic a b c x=0 := by
    rw [quadratic_identity, hx, resultant_identity, hr]
    ring
  have hq : quadratic a b c x=0 := by
    calc
      _ = il^2*((linear a b c d e f)^2*quadratic a b c x) := by
        calc
          _ = (linear a b c d e f*il)^2*quadratic a b c x := by rw [hl]; ring
          _ = _ := by ring
      _ = 0 := by rw [hqmul]; ring
  have hcmul : a^2*cubic d e f g x=0 := by
    rw [division_identity, hq]
    simpa only [mul_zero, zero_add] using hx
  have hc : cubic d e f g x=0 := by
    calc
      _ = ia^2*(a^2*cubic d e f g x) := by
        calc
          _ = (a*ia)^2*cubic d e f g x := by rw [ha]; ring
          _ = _ := by ring
      _ = 0 := by rw [hcmul]; ring
  exact ⟨hq,hc⟩

end QuadricContact.Subresultant
#print axioms QuadricContact.Subresultant.common_root
