## A contact field with two first integrals
In three variables define
\[
r=z_0^3+2\cdot z_0^2\cdot z_1+3\cdot z_0\cdot z_1^2+5\cdot z_1^3,
\]
\[
Q=z_0^5+2\cdot z_0^4\cdot z_1+3\cdot z_0^3\cdot z_1^2+5\cdot z_0^2\cdot z_1^3+7\cdot z_0\cdot z_1^4+11\cdot z_1^5+z_2^5,
\qquad f=r^2+z_2\cdot Q.
\]
The Hamiltonian field \(W=(-r_{z_1},r_{z_0},0)\) has zero divergence and annihilates both \(r\) and \(z_2\). With \(g=W(Q)\), it satisfies \(W(f)=z_2\cdot g\).

## Couple the two polarized copies without changing the field
Set \(U=X+Y\), \(V=X-Y\), and
\[
F=f(U)+f(V)+1000003\,r(U)r(V),\quad
A=g(U)-g(V),\quad D=U_2\cdot V_2=X_2^2-Y_2^2.
\]
The coupling is large and genuinely mixed, but both contact fields annihilate it because they preserve their respective \(r\)'s. Define
\[
N_X=\frac{V_2\cdot W(U)-U_2\cdot W(V)}2,\qquad
N_Y=\frac{V_2\cdot W(U)+U_2\cdot W(V)}2.
\]
In polarized coordinates this is \((V_2\cdot W(U),-U_2\cdot W(V))\). Its derivative of \(F\) is \(A\cdot D\), its divergence is zero, and it annihilates \(D\). This proves the strict certificate.

## Independent geometric and target checks
The coupling coefficient vanishes modulo \(1000003\), allowing the retained finite-field smoothness check to compare with the uncoupled control. The target's Jacobian-column rank rises from 18 to 19 modulo 101, certifying that the target is primitive over \(\mathbb Q\). A separate centroid computation rules out the tested separated-block explanation. These checks have distinct roles; none is inferred from the rendered surface.

The lesson is precise: a coupling built from common first integrals can preserve the rational field even when it destroys visible separation. Arbitrary mixed couplings do not share this property.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The exact algebraic checks are evidence for the construction; no Lean theorem has yet been checked for this instance.

The [exact witness](data/polarized-contact-coupled-d2/witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](data/polarized-contact-coupled-d2/Solution.lean) checks the certificate and its side conditions.
