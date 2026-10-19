import Proposal.CoefficientFunctional
import Proposal.ConcreteLine

noncomputable section
namespace QuadricContact

/-- Source coefficients are polynomial expressions, so every ring map preserves them. -/
theorem sourceCoefficients_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p q s k x y z w : R) (i : Fin 8) :
    f (ConcreteLine.sourceCoefficients p q s k x y z w i) =
      ConcreteLine.sourceCoefficients (f p) (f q) (f s) (f k)
        (f x) (f y) (f z) (f w) i := by
  fin_cases i <;> simp [ConcreteLine.sourceCoefficients, map_ofNat]

/-- Coordinate specialization with an independently named target polynomial. -/
theorem sourceMinor_map_named {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Polynomial R) (hp : p.Monic) (hn : p.natDegree = 27)
    (q : Polynomial S) (hq : q = p.map f) (hqm : q.Monic) (hqn : q.natDegree = 27)
    (hdiv : q ∣ p.map f) (s : Fin 8 → AdjoinRoot p) :
    (sourceMinor (AdjoinRootSpecialization.basis p hp hn) s).map f =
      sourceMinor (AdjoinRootSpecialization.basis q hqm hqn)
        (fun i => AdjoinRoot.map f p q hdiv (s i)) := by
  subst q
  exact sourceMinor_map f p hp hn hqn s

end QuadricContact
#print axioms QuadricContact.sourceMinor_map_named
