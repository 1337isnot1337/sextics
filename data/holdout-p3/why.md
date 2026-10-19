Set \(p=X_2\cdot Y_2\) on the holdout sextic. This instance asks for the endpoint cube
\[
A=p^3=X_2^3\cdot Y_2^3.
\]
It is the endpoint analogue of the central \(X_0^3\cdot Y_0^3\) target, but the analogy is not a coordinate symmetry. Reversing the oriented chain changes the two mixed terms, so the endpoint certificate needs its own target calculation.

The endpoint has a useful algebraic simplification: its coupling \(X_1^3\cdot Y_1\cdot p\) and the target both depend on the product \(p\). If \(s=X_2^6+Y_2^6\), then
\[
(X_2^6-Y_2^6)^2=s^2-4\cdot p^6.
\]
This relation organizes the endpoint's symmetric coordinates and their double cover. It does not by itself supply a primitive as the other coordinates vary. The exchange \(X_2\leftrightarrow Y_2\) fixes \(A\) but reverses the residue volume, so the target occupies the sector missed by that reflection quotient. It is also one of the ten paired-sign directions outside the span of the direct finite-quotient support calculations.

The successful cover combines the two odd endpoints instead:
\[
T^6=Y_0^6+Y_2^6,\qquad
\alpha=Y_0/T,\quad\beta=Y_2/T,\qquad
S=Y_1^2+T^2,\quad P=Y_1\cdot T.
\]
Its new exchange \(Y_1\leftrightarrow T\) produces the weighted quotient used by the moving-conic construction. The source for the endpoint cube is
\[
B=\frac{S\cdot X_2^3\cdot\beta^3}{2\cdot\alpha^5}.
\]
The factor \(\beta^3\) records the original \(Y_2^3\) dependence on the coefficient curve. The reflected correction has deck exponent \(-4\), so normalized trace removes it and returns exactly the prescribed endpoint target.

The central and endpoint cubes therefore share the curve family and trace character, but not the same source. This separates a genuine uniform construction from an unsupported relabeling argument. The simpler endpoint expression does not require a separate elliptic or double-cover primitive: its dependence on the other variables is carried through the existing quotient calculation.

Compare [\(p\cdot Y_1^4\)](#case/holdout-p-y14), which has the same original symmetry but moves four degrees into the middle odd coordinate. Its source and deck exponent differ in a controlled way. [Chapter 2](#technical-information/explicit-constructions) gives the source identities behind these comparisons, and [Chapter 4](#technical-information/known-locus) distinguishes the resulting geometric target coverage from the task of extracting compact explicit divisors.
