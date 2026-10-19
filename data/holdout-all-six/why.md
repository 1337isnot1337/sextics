This is the most evenly distributed of the basic holdout monomials:
\[
A=X_0\cdot X_1\cdot X_2\cdot Y_0\cdot Y_1\cdot Y_2.
\]
Every variable occurs once. On a coordinatewise-even sextic, such a product suggests the Jacobian density of the map to squared coordinates. The holdout's two mixed chain terms are not coordinatewise even, so that immediate square-coordinate reduction does not apply to its equation.

A more selective symmetry remains: simultaneously negating \(X_i,Y_i\) preserves both the equation and the numerator. The target also has equal endpoint exponents, so exchanging \(X_2,Y_2\) fixes the numerator and reverses the residue. Passing to a paired-sign quotient or observing an endpoint reflection is therefore not enough to supply the required support. Direct quotient calculations place this monomial among ten directions outside their 48-dimensional span in the 58-dimensional paired-sign sector, specifically in the four-dimensional character component conjugate to the central cubic's component.

Writing \(A=(X_0\cdot Y_0)\cdot(X_1\cdot Y_1)\cdot(X_2\cdot Y_2)\) makes the three pairs visible, but does not remove the unequal exponents in the chain couplings. The successful construction keeps the full equation and instead introduces an auxiliary cover:
\[
T^6=Y_0^6+Y_2^6,\qquad
\alpha=Y_0/T,\quad\beta=Y_2/T,\qquad
S=Y_1^2+T^2,\quad P=Y_1\cdot T.
\]
The exchange \(Y_1\leftrightarrow T\) gives a weighted quotient with source
\[
B=\frac{P\cdot X_0\cdot X_1\cdot X_2\cdot\beta}{2\cdot\alpha^4}.
\]
The moving-conic primitive for this source lifts with a correction of deck exponent \(-2\). Normalized trace removes the correction, and the source and derivative identities recover the exact balanced target.

The example demonstrates that the conic method is not tied to a numerator concentrated in a single binary pair. It handles a product involving every coordinate through a polynomial source on the same quotient. At the same time, changing the sextic is a separate issue: [the mixed-polar instance](#case/mixed-polar) keeps this numerator but adds a term that breaks the cover's exchange symmetry. A source formula alone cannot be imported when the covered equation is no longer invariant.

[Chapter 2](#technical-information/explicit-constructions) explains this distinction between the geometry of the quotient and the selection of its source. The balanced target is a particularly direct comparison between generalizing across numerators on a fixed variety and generalizing the construction to a different variety.
