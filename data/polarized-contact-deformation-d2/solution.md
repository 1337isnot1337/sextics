## Deform by a multiple of the preserved divisor
Start with the coupled polarized-contact field \(N\), denominator \(D=X_2^2-Y_2^2\), and target \(A_0\). Its special properties are
\[
N(F_0)=A_0\cdot D,\qquad N(D)=0,\qquad \operatorname{div}N=0.
\]
Choose \(H=Y_1^4\) and \(s=101000303=101\cdot1000003\). Define
\[
F=F_0+s\cdot D\cdot H,\qquad A=A_0+s\cdot N(H).
\]
The numerator and denominator are unchanged.

## The transport calculation
The product rule gives
\[
N(F)=A_0\cdot D+s\bigl(N(D)H+D\cdot N(H)\bigr)=D\cdot(A_0+s\cdot N(H))=A\cdot D.
\]
Since both \(N(D)\) and \(\operatorname{div}N\) remain zero, the second strict equation survives automatically. The changed target has degree six: the numerator has degree three and differentiates a quartic. Thus the deformation preserves the required grading as well as the certificate identity.

## Why this coefficient was selected
The deformation vanishes modulo both primes used for the original control checks. Smoothness can be retained through reduction modulo \(1000003\), and the primitive-target check through reduction modulo 101. A separate calculation at 103 records the centroid rank of the deformed polynomial. These are exact arithmetic design choices, not numerical continuity arguments.

The source retains exact identity and legality checks for this deformation, but does not claim that the full expression-expanding arbiter was rerun for this packet. That distinction remains in the agent-facing audit file. The direct polynomial transport proves the strict field equation; a future Lean replay must still certify the complete protected statement, including admissibility.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The exact algebraic checks are evidence for the construction; no Lean theorem has yet been checked for this instance.

The [exact witness](data/polarized-contact-deformation-d2/witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](data/polarized-contact-deformation-d2/Solution.lean) checks the certificate and its side conditions.
