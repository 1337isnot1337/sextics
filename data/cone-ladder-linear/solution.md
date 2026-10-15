## A hyperplane contact presentation
In the \(X\) variables put
\[
e=X_0^2,\qquad P=X_1-X_2,\qquad k=X_1^5+X_2^5,\qquad f=e^3+P\cdot k.
\]
The six-variable sextic is \(F=f(X)+f(Y)\). The vector field
\[
W=\nabla P\times\nabla e=(0,-2\cdot X_0,-2\cdot X_0)
\]
annihilates both \(P\) and \(e\) and has zero divergence. Consequently \(W(f)=P\cdot W(k)\).

## A passive odd multiplier
Multiply the field by \(Y_0\), keeping its components in the \(X\) slots. Then
\[
D=X_1-X_2,\qquad
N=(0,-2\cdot X_0\cdot Y_0,-2\cdot X_0\cdot Y_0,0,0,0),
\]
\[
A=Y_0\cdot W(k)=-10\cdot X_0\cdot Y_0\cdot (X_1^4+X_2^4).
\]
Since the field differentiates none of the \(Y\) variables, the second sextic copy and the multiplier are passive. We obtain \(N(F)=A\cdot D\), \(N(D)=0\), and \(\operatorname{div}N=0\). These are the strict equations with a degree-one denominator and degree-two numerator.

## Why the pole is legal
The contact presentation does not make \(P\) a component of the smooth sextic: on \(P=0\), the surviving cubic-power and second-block terms are not identically zero. The independent legality checks are retained with the record. The construction relies on \(W\) preserving the contact data; it does not assert that every sextic admits a hyperplane certificate or that a small pole makes the target Jacobian-trivial.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{1}&=- 2\cdot X_{0}\cdot Y_{0}\\
N_{2}&=- 2\cdot X_{0}\cdot Y_{0}
\end{aligned}
\]


## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The exact algebraic checks are evidence for the construction; no Lean theorem has yet been checked for this instance.

The [exact witness](data/cone-ladder-linear/witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](data/cone-ladder-linear/Solution.lean) checks the certificate and its side conditions.
