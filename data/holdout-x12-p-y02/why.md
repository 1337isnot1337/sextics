With \(p=X_2\cdot Y_2\), the target is
\[
A=X_1^2\cdot p\cdot Y_0^2.
\]
It distributes its degree across all three coordinate pairs while remaining linear in the endpoint product. This places it between targets concentrated in one pair and [the monomial using all six variables](#case/holdout-all-six). The factors \(X_1^2\) and \(Y_0^2\) connect the middle even coordinate to the initial odd coordinate without including their partners.

The equation is invariant under paired sign changes and depends on \(X_2,Y_2\) through their symmetric sixth-power sum and product. Those facts suggest quotient coordinates, but the residue density has to be transported with the equation. Exchanging the endpoint coordinates fixes this numerator and reverses the volume form. Thus the reflection quotient does not serve the class; the broader direct quotient calculation also leaves it among the ten paired-sign directions outside its supported span. A short expression in invariant coordinates is not enough to identify a supported residue.

The Fermat cover uses
\[
T^6=Y_0^6+Y_2^6,\qquad
\alpha=Y_0/T,\quad\beta=Y_2/T,\qquad
S=Y_1^2+T^2,\quad P=Y_1\cdot T.
\]
After the exchange \(Y_1\leftrightarrow T\), the polynomial source on the weighted quotient is
\[
B=\frac{S\cdot X_1^2\cdot X_2\cdot\beta}{2\cdot\alpha^3}.
\]
The moving-conic primitive lifts to the desired density with a correction of deck exponent \(-4\). Normalized trace kills the correction. This is the same character used for the central cubic, although the source records a different distribution among \(X_1,X_2\) and the coefficient functions \(\alpha,\beta\).

The example shows what is uniform and what remains target-specific in the construction. The same family of conics integrates the new polynomial source, so there is no need to choose a separate geometric family for each numerator. Nevertheless, the source identity and its derivative must be checked for this exact monomial; a certificate for the central target alone would not justify changing its exponents. The dependence on all three pairs remains part of that calculation.

Compare [\(X_0^4\cdot p\)](#case/holdout-x04-p). Both targets are linear in the endpoint product, but the latter has the conjugate deck character and a source independent of \(S,P\). This makes the pair useful for seeing why original endpoint symmetry does not determine the cover calculation. [Chapter 2](#technical-information/explicit-constructions) explains these source transformations, and [Chapter 4](#technical-information/known-locus) places them in the full target-space picture.
