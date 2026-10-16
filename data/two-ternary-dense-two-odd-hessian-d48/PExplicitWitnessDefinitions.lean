import Proposal.PFrozen
import Mathlib.Data.Fin.VecNotation

/-! Explicit degree55 witness; all coefficients bound to the accepted sparse QQ artifact. -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.ExplicitWitness
open MvPolynomial HodgeTestbed.Frozen

def pA : SexticPoly := 14

def pB : SexticPoly := 7*X1^2+21*Y0^2

def pC : SexticPoly := 23*X1^4+12*X1^2*Y0^2+23*Y0^4

def pD : SexticPoly := 4*X1^6+39*X1^4*Y0^2+73*X1^2*Y0^4+8*Y0^6

def qA : SexticPoly := 59

def qB : SexticPoly := 43*X2^2+61*Y2^2

def qC : SexticPoly := 37*X2^4+47*X2^2*Y2^2+67*Y2^4

def qD : SexticPoly := 31*X2^6+41*X2^4*Y2^2+53*X2^2*Y2^4+71*Y2^6

def P : SexticPoly := pA*X0^6+pB*X0^4+pC*X0^2+pD

def Q : SexticPoly := qA*Y1^6+qB*Y1^4+qC*Y1^2+qD

def fpP : SexticPoly := 3*pA*X0^4+2*pB*X0^2+pC

def fpQ : SexticPoly := 3*qA*Y1^4+2*qB*Y1^2+qC

def h0P : SexticPoly := pC^2-3*pB*pD

def HP : SexticPoly := (pB^2-3*pA*pC)*X0^4+(pB*pC-9*pA*pD)*X0^2+h0P

def HQ : SexticPoly := (qB^2-3*qA*qC)*Y1^4+(qB*qC-9*qA*qD)*Y1^2+qC^2-3*qB*qD

def deltaP : SexticPoly := pB^2*pC^2-4*pA*pC^3-4*pB^3*pD-27*pA^2*pD^2+18*pA*pB*pC*pD

def deltaQ : SexticPoly := qB^2*qC^2-4*qA*qC^3-4*qB^3*qD-27*qA^2*qD^2+18*qA*qB*qC*qD

def TQ : SexticPoly := 3*(2*(qB^2-3*qA*qC)*Y1^2+(qB*qC-9*qA*qD))*Q-2*HQ*fpQ

def KP : SexticPoly := (pB*pC^2-6*pB^2*pD+9*pA*pC*pD)*X0^2+2*pC^3-9*pB*pC*pD+27*pA*pD^2

def LP : SexticPoly := X0^2*(pB*X0^4+2*pC*X0^2+3*pD)

def G : SexticPoly := HP^3*deltaQ*Q^2-HQ^3*deltaP*P^2

def U1 : SexticPoly := h0P*HP*HQ*TQ*Q

def V : SexticPoly := KP*HQ^3*P^2-3*deltaQ*Q^2*HP^2*LP

def RP : SexticPoly := 6*P-2*X0^2*fpP

def RQ : SexticPoly := 6*Q-2*Y1^2*fpQ

def R0 : SexticPoly := P*HQ^3*(RP*KP-6*X0^6*deltaP)-18*X0^2*deltaQ*Q^2*HP^2*(X0^2*pC+3*pD)

def R1 : SexticPoly := R0+2*X0^2*fpQ*U1

def D : SexticPoly := 36*X0*Q*G

def nX1 : SexticPoly := -6*X1*Y1*Q*V

def nX2 : SexticPoly := X2*Y1*P*R1

def nY0 : SexticPoly := -6*Y0*Y1*Q*V

def nY1 : SexticPoly := P*(Y1^2*R0-X0^2*RQ*U1)

def nY2 : SexticPoly := Y2*Y1*P*R1

def C : SexticPoly := -72*X0*Y1*Q*G*R0

def N : Fin 6 → SexticPoly := ![0, nX1, nX2, nY0, nY1, nY2]

def degree : ℕ := 55

theorem F_eq : Frozen.F = P + Q := by
  simp only [Frozen.F, P, Q, pA, pB, pC, pD, qA, qB, qC, qD]
  ring

end HodgeTestbed.ExplicitWitness
