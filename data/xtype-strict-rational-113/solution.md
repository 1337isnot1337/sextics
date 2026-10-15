## Interpolating along a binary-cubic pencil
Use \(u=X_0^2\), \(w=Y_0^2\), and set
\[
P=u^3+u^2\cdot w+u\cdot w^2+3\cdot w^3,\qquad C=(u+w)^3.
\]
The pencil \(C-s\cdot P\) has discriminant
\[
\operatorname{disc}(C-s\cdot P)=-4\cdot s^2(3\cdot s-1)\cdot (17\cdot s-27).
\]
Its two nonzero singular parameters, \(1/3\) and \(27/17\), supply the coefficients of the spectator channels:
\[
D=C+\frac13\cdot X_1^6+\frac{27}{17}\cdot (X_2^6+Y_1^6).
\]
This explains the otherwise unusual rational numbers in the polar divisor. They encode special members of a pencil, rather than coefficients found without structure.

## A strict linear completion
The target is \(A=X_1\cdot Y_0^5\). The source reduces the logarithmic construction to a system with 23 unknown coefficients and obtains a unique strict completion. For example, two of its components are
\[
N_0=-\frac{2}{153}\cdot X_0\cdot X_1\cdot Y_0\cdot (u+w)\cdot (u+4\cdot w),\qquad
N_2=-\frac1{34}\cdot u\cdot X_1\cdot X_2\cdot Y_0\cdot (u+2\cdot w).
\]
The remaining components, including the compensating \(Y_0\) component, are supplied by the retained constructor. Together they satisfy \(N(F)=A\cdot D\) and \(D\cdot\operatorname{div}N=N(D)\). The latter equation couples the pencil channels and is the reason one cannot simply add arbitrary single-block antiderivatives.

## Why interpolation matters
The source distinguishes this construction from a single constant-spectral Piola atom. The numerator combines more than one pencil degeneration, using the spare coordinates to cancel the divergence obstruction. The conclusion is an exact strict certificate for this specialization and target; it is not an assertion that every binary cubic admits the same denominator with the same coefficients.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. A local Lean replay proves the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](data/xtype-strict-rational-113/witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](data/xtype-strict-rational-113/Solution.lean) checks the certificate and its side conditions.
