This instance asks for the two-term target
\[
A=X_0^3\cdot Y_0^3+X_0^3\cdot Y_0\cdot Y_1^2
\]
on the central holdout sextic. The summands belong to different residue characters, so the bundle tests the assembly of supporting constructions rather than a new hypersurface.

**Geometric existence is known for both summands, and hence for their sum**, as a special case of [Chapter 4, §4.6](#technical-information/known-locus/46-all-target-support-on-the-chain-example). The Fermat-cover construction serves the first summand; the second is supported by a finite quotient whose invariant cohomology has coniveau at least one. The latter calculation includes the determinant of the action on the residue volume. [Chapter 3](#technical-information/geometric-support) explains the quotient-support principle, and [Chapter 2](#technical-information/explicit-constructions) develops the cover construction. An accepted Lean proof for this exact bundle, or an explicit common certificate, remains to be supplied.

The distinction between the two arguments is concrete. On the cover \(T^6=Y_0^6+Y_2^6\), put \(y=Y_1\). For a monomial \(M(X)Y_0^aY_1^bY_2^c\), the reflected term has deck exponent \(b-a-c-1\). That exponent is \(-4\) for the first summand, so its correction has trace zero. For the second it is zero, and the antisymmetrized source itself vanishes. Reusing precisely that source-selection formula therefore does not supply the second summand.

The diagonal symmetry fixing \(X\) and sending \((Y_0,Y_1,Y_2)\) to \((\zeta^2Y_0,\zeta^4Y_1,\zeta^2Y_2)\), with \(\zeta\) a primitive sixth root, fixes the first target and multiplies the second by \(\zeta^4\). The corresponding projections separate a certificate for the bundle into certificates for its two components. Conversely, certificates add after putting their rational fields over a common denominator. Thus the useful remaining task is to make the second support argument effective or formal, then carry out this assembly with the exact target retained.
