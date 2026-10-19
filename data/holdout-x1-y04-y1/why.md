The target on the holdout sextic is
\[
A=X_1\cdot Y_0^4\cdot Y_1.
\]
It uses the first two coordinate pairs and omits the endpoint pair. Compared with the central \(X_0^3\cdot Y_0^3\), it transfers degree toward \(Y_0\) while including both middle coordinates. Its small variable support makes it a useful test of the difference between a sparse numerator and a separated equation.

The tempting interpretation of \(Y_0^4\) as a passive multiplier fails at the level of the equation. The first mixed term contains \(X_1\cdot Y_0\cdot Y_1\), and the second joins the middle pair to \(X_2,Y_2\). A field in the apparent active pair still has to account for both couplings. The certificate cannot be obtained merely by multiplying a field from a binary example and ignoring the resulting derivative terms.

The monomial is invariant under each paired sign change and under the endpoint exchange. The exchange reverses the residue volume, so its quotient serves the opposite residue sector. The larger direct quotient calculation likewise leaves this target outside its 48-dimensional supported span in the 58-dimensional paired-sign sector. These observations identify the limitation overcome by the auxiliary cover; they do not imply that the class lacks support.

Set
\[
T^6=Y_0^6+Y_2^6,\qquad
\alpha=Y_0/T,\quad\beta=Y_2/T,\qquad
S=Y_1^2+T^2,\quad P=Y_1\cdot T.
\]
The useful exchange is now \(Y_1\leftrightarrow T\), and the source on its weighted quotient is
\[
B=\frac{P\cdot S\cdot X_1}{2\cdot\alpha}.
\]
The moving-conic construction accepts this source without requiring \(Y_0\) to be passive in the original variables. Its reflected correction has deck exponent \(-4\); normalized trace eliminates that correction and recovers the prescribed density, with the derivative identity ensuring the full certificate equation.

Compare [\(X_1^2\cdot X_2\cdot Y_0^2\cdot Y_2\)](#case/holdout-x12-p-y02), which trades two powers of \(Y_0\) and one middle odd factor for other coordinates while retaining the same deck exponent. Their sources differ by their polynomial dependence on \(P\) and the even coordinates, rather than by a new curve family. This is the practical content of the source-independent conic machinery explained in [Chapter 2](#technical-information/explicit-constructions): a uniform geometric construction, together with separately verified identities for each target.
