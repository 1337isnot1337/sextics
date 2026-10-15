## A compatible target bundle
Put \(u=X_0^2\), \(w=Y_0^2\). The active binary block is
\[
P(u,w)=u^3+u^2\cdot w-\frac14\cdot u\cdot w^2+2\cdot w^3.
\]
The selected target and denominator are
\[
A=X_1\cdot Y_0^5-\frac1{29}\cdot X_0^2\cdot X_1\cdot Y_0^3,\qquad
D=(u+w)^3+\frac12\cdot X_1^6.
\]
The denominator is a cube of a quadratic form plus one spectator sixth power. This shape makes its logarithmic tangency equation sparse. The coefficient \(-1/29\) in \(A\) is a compatibility condition of the construction: it is not a freely adjustable decoration on the target.

## How the numerator is obtained
With this \(D\) fixed, write each component of \(N\) as an unknown homogeneous polynomial of degree seven, retaining the parity sectors dictated by \(F\) and \(A\). Substitution into \(N(F)=A\cdot D\) and \(D\cdot\operatorname{div}N=N(D)\) gives linear equations in those unknown coefficients. The retained sparse-family recipe specializes its rational parameter to \(1\); at the displayed binary-block coefficients, the exact compatibility system determines the strict completion.

This is an instance of designing the polar divisor and target together. One does not first choose an arbitrary sextic denominator and hope that a numerator exists. The cubic block's discriminant is nonzero, and the additional denominator-legality factors in the recipe are nonzero at this specialization, so this is a legal rational fiber of the family.

## Scope of the construction
The result is the displayed two-term target bundle. It does not individually solve both summands. The source also discusses quartic constructions after adjoining an algebraic cube root; those are a different witness, not a cancellation of the displayed rational sextic denominator. The record contains the unique exact rational completion of the 23-column coefficient system, with all six numerator components written explicitly.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. A local Lean replay proves the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](data/xtype-sparse-rational-1m142/witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](data/xtype-sparse-rational-1m142/Solution.lean) checks the certificate and its side conditions.
