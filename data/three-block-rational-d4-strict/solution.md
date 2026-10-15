## A cyclotomic cofactor across blocks
Let \(L=X_1^2-2\cdot Y_1^2\). The denominator is
\[
D=L^2+L\cdot X_2^2+X_2^4.
\]
Over \(\mathbb Q(\omega)\), where \(\omega^2+\omega+1=0\), it factors as \((L-\omega\cdot X_2^2)\cdot (L-\omega^2\cdot X_2^2)\). Taking the product keeps the construction rational.

For \(A=X_0\cdot X_1\cdot X_2^3\cdot Y_1\), take
\[
N_1=\frac16\cdot X_0\cdot X_2^3\cdot Y_1,\qquad
N_2=\frac16\cdot X_0\cdot X_1\cdot Y_1\cdot (L+X_2^2),\qquad
N_4=\frac16\cdot X_0\cdot X_1\cdot X_2^3.
\]
The non-diagonal middle block is
\[
6\cdot X_1^6-15\cdot X_1^4\cdot Y_1^2+9\cdot X_1^2\cdot Y_1^4+Y_1^6.
\]
Its coefficients are compatible with the same quadratic quantity \(L\). Differentiating this block and the \(X_2^6\) term against the three components gives \(A\cdot D\); the remaining coordinates are untouched.

## Why the rational field works
Direct differentiation of the quartic yields \(N(D)=D\cdot\operatorname{div}N\). This cancels the denominator derivative in the divergence of \(N/D\), so the normalized equation is already the complete certificate. Each numerator has degree five, and the field has total degree one as required at \(q=1\).

The retained source establishes a strict degree-four minimum. In particular, the smaller quadratic candidate space is obstructed by the second equation: satisfying the derivative equation alone does not resolve the divergence condition. This illustrates why the norm of two conjugate factors is useful even when individual quadratic divisors first look promising.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{1}&=\frac{X_{0}\cdot X_{2}^{3}\cdot Y_{1}}{6}\\
N_{2}&=\frac{X_{0}\cdot X_{1}\cdot Y_{1}\cdot \left(X_{1}^{2} + X_{2}^{2} - 2\cdot Y_{1}^{2}\right)}{6}\\
N_{4}&=\frac{X_{0}\cdot X_{1}\cdot X_{2}^{3}}{6}
\end{aligned}
\]


## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The exact algebraic checks are evidence for the construction; no Lean theorem has yet been checked for this instance.

The [exact witness](data/three-block-rational-d4-strict/witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](data/three-block-rational-d4-strict/Solution.lean) checks the certificate and its side conditions.
