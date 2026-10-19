The central holdout isolates what happens when two adjacent couplings are added to the Fermat sextic:
\[
X_0^3\cdot X_1\cdot Y_0\cdot Y_1
+X_1^3\cdot X_2\cdot Y_1\cdot Y_2.
\]
They form an oriented chain through the three coordinate pairs, while the target \(A=X_0^3\cdot Y_0^3\) is concentrated at its first end. The equation is sparse and retains substantial symmetry, but the separated-block constructions no longer apply directly.

In particular, simultaneously changing the signs of \(X_i,Y_i\) preserves the equation, and exchanging \(X_2,Y_2\) is a reflection. That reflection fixes the target numerator and reverses the residue volume, placing this class outside its invariant residue sector. The collection of direct reflection and diagonal-quotient arguments serves 182 of the 208 primitive odd sextic directions; this target is among the ten missed directions within the 58-dimensional paired-sign sector. These are limits of those particular quotient arguments, not limits of geometric existence.

The equation also has an instructive surface fibration over the ratios \([X_0:Y_0]\), \([X_1:Y_1]\). On a ratio chart, quotienting the two remaining pair scales by their signs gives a degree-six surface in \(\mathbb P(2,2,1,1)\); its generic smooth resolution is a K3 surface. This organizes the geometry without providing a primitive compatible with variation over the whole base. It is a different viewpoint from the cover used in the certificate, rather than an obstruction to every possible supporting divisor.

The successful construction instead adjoins
\[
T^6=Y_0^6+Y_2^6,\qquad
\alpha=Y_0/T,\quad\beta=Y_2/T,
\]
so \(\alpha^6+\beta^6=1\), and sets \(S=Y_1^2+T^2\), \(P=Y_1\cdot T\). Interchanging \(Y_1,T\) preserves the covered equation. Quotienting also by their simultaneous sign change gives a weighted threefold carrying a moving family of conics, and the source for this target is
\[
B=\frac{S\cdot X_0^3}{2\cdot\alpha^2}.
\]
The lifted primitive has the desired density plus a reflected correction of deck exponent \(-4\). The normalized deck trace kills that correction and recovers exactly \(A\).

The essential advance is the use of a useful symmetry on an auxiliary cover, despite the original variety's quotient methods missing the class. The same conic geometry accepts other polynomial sources and serves the companion holdout targets. [Chapter 2](#technical-information/explicit-constructions) explains the source, derivative, and trace identities; [The all-target theorem in §4.6](#technical-information/known-locus/46-all-target-support-on-the-chain-example) combines this cover with a complementary diagonal quotient to prove geometric existence for every odd target at every positive pole parameter on this fixed sextic. Explicit fields, manageable divisors, and formal proofs retain their own computational content.
