## A linear-contact constituent of a larger family
Write
\[
R=\frac{13}{17}\cdot Y_0^2+\frac59\cdot Y_0\cdot Y_2+\frac7{11}\cdot Y_2^2.
\]
The active part of the sextic is \(X_0^6+X_1^6+X_0^2\cdot X_1^2\cdot R\). The displayed divisor is
\[
D_L=X_0^6+X_1^6+X_0^2\cdot X_1^2\cdot R-\frac{R^3}{27}.
\]
This is the singular Hesse value: in squared active coordinates the cubic correction turns the expression into a product of three conjugate linear factors, whose pullbacks are quadrics. Their product is rational even when the factors are not individually rational.

## Serve the selected target with a logarithmic field
The target is \(A=X_0^3\cdot X_1\cdot X_2\cdot Y_1\). The factor \(X_2\cdot Y_1\) is passive for the active contact construction. The retained family formula chooses the appropriate ordered active pair and logarithmic density, then clears \(D_L\) to obtain a degree-seven numerator. The resulting identities are strict: \(N(F)=A\cdot D_L\) and \(D_L\operatorname{div}N=N(D_L)\).

The passive quadratic \(R\) enters the factorization algebraically, but its variables are not differentiated by the active part. This is why a mixed term such as \(Y_0\cdot Y_2\) can be included without forcing a new denominator shape.

## Keep the constituent distinct from the whole bundle
The source develops a larger three-target construction with further Piola constituents. Combining all those directions can require product denominators of higher degree, and some constituents are non-strict. This card selects only the strict linear-contact constituent, with the other target coefficient set to zero. Its degree-six denominator must not be presented as a certificate for the entire larger bundle.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. A local Lean replay proves the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](data/family-passive-contact/witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](data/family-passive-contact/Solution.lean) checks the certificate and its side conditions.
