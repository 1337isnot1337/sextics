# 2. Explicit constructions: transport, contact, and algebraic cycles

[Previous: certificates](#technical-information/certificates) · [Contents](#technical-information/introduction) · [Next: binary blocks](#technical-information/binary-blocks)

The useful common structure behind the explicit certificates is a transport identity. A change of variables converts \(F\) into an equation with accessible geometry; a rational field on that equation is pulled back by cofactors. Its Jacobian determines the target. Geometry becomes decisive when it proves that the available targets span the required space.

We first work at \(q=1\). An Euler-normalized strict certificate satisfies \(v(F)=A\) and \(\operatorname{div} v=0\). After writing \(v=N/D\), these are \(N(F)=A\cdot D\) and \(D\cdot \operatorname{div} N-N(D)=0\). Every construction below also requires the homogeneity, involution parity, and denominator legality of [Chapter 1](#technical-information/certificates). Finite sums and normalized field traces preserve the identities.

## 2.1 Cofactor transport

Let \(\Phi \) be a polynomial or rational map between affine spaces of the same dimension. Put \(J=d\Phi \) and \(\Delta =\operatorname{det} J\). For a target-space rational field \(w\) and a target function \(G\), define

\[
\begin{gathered}
V = \operatorname{adj}(J)\cdot w(\Phi ).\\
V(G(\Phi )) = \Delta\cdot w(G)(\Phi ),\\
\operatorname{div} V = \Delta\cdot (\operatorname{div} w)(\Phi ).
\end{gathered}
\]

To prove both identities, let \(\Theta \) and \(\Theta _t\) denote the source and target volume forms. Expansion by minors gives \(\Phi^{*}(\iota _w\Theta _t)=\iota _V\Theta \). Taking exterior derivatives gives \(\operatorname{div} V=\Delta\cdot (\operatorname{div} w)(\Phi )\). Independently, \(J\cdot\operatorname{adj}(J)=\Delta\cdot I\) and the chain rule give the identity on \(G\). This argument uses polynomial identities among derivatives and therefore remains valid for rational \(\Phi \) on its domain. Every coordinate is differentiated, including parameters written as ratios. Thus a divergence-free field serving \(B\) downstairs serves \(\Delta\cdot B(\Phi )\) upstairs. The determinant is the transformation law for the differential-form density.

A useful polynomial constructor makes \(G\) spectrally simple. Give \(\Phi _{i}\) positive degrees \(m_{i}\), let \(G\) have weighted degree six, and let \(w\) be a polynomial derivation of weighted degree zero. Choose a polynomial density \(b\) of weight \(12-\sum m_{i}\). Suppose, for constants \(\mu ,\nu \),

\[
\begin{gathered}
D_{0} = w(G),\\
w(D_{0}) = (\mu +\nu )\cdot D_{0}-\mu\cdot\nu\cdot G,\\
\operatorname{div}(b\cdot w) = (\mu +\nu )\cdot b.
\end{gathered}
\]

Then

\[
\begin{gathered}
F = G(\Phi ),       A = b(\Phi )\cdot\Delta,\\
D = D_{0}(\Phi ),     N = \operatorname{adj}(d\Phi )\cdot(b\cdot w)(\Phi ),\\
N(F) = A\cdot D,\\
D\cdot \operatorname{div} N-N(D) = \mu\cdot\nu\cdot A\cdot F.
\end{gathered}
\]

Indeed, cofactor transport gives \(N(F)=\Delta\cdot b(\Phi )\cdot w(G)(\Phi )=A\cdot D, \operatorname{div} N=(\mu +\nu )\cdot A\), and \(N(D)=A\cdot((\mu +\nu )\cdot D-\mu\cdot\nu\cdot F)\). Subtraction proves the displayed \(E_{2}\) identity, hence the \(q=1\) certificate assertion. The degrees are \(\operatorname{deg} A=6, \operatorname{deg} D=6\) and \(\operatorname{deg} N_{i}=7\): the \(i\)-th target coordinate contributes \(m_{i}\) to \(w\), while its adjugate column has source degree \(\sum m_{j}-m_{i}-5\). Legality still requires \(D\ne 0\) and \(\operatorname{gcd}(D,F)=1\).

There is also a homogeneous nilpotent branch. If \(w\) has weighted degree \(e, w^{2}(G)=0\) and \(\operatorname{div}(b\cdot w)=0\), the same calculation gives \(N(F)=A\cdot D\) and \(\operatorname{div} N=N(D)=0\). Its denominator has degree \(6+e\) and numerator degree \(7+e\). When \(e\ne 0\), a constant-spectrum quadratic equation for \(w\) on \(G\) can have only the nilpotent form: its three terms have distinct weights unless their nonhomogeneous coefficients vanish.

These spectral hypotheses are sufficient conditions for explicit fields. They are not a characterization of certificates. For nonlinear polynomial \(\Phi \), the determinant-density targets have a broader finite weighted-Fano interpretation without a spectral condition, proved in [Chapter 3](#technical-information/geometric-support/34-nonlinear-polynomial-piola-maps-are-finite-fano-maps). Rational maps can introduce additional boundary terms. The scope and necessity questions belong to [Chapter 4](#technical-information/known-locus).

## 2.2 Euler and Nambu fields

Subset Euler is the simplest spectral instance. Write \(E_I=\sum _{i\in I} Z_{i}\partial _{i}\). If \(E_I^{2}(F)=6\cdot E_I(F)\), and a target monomial satisfies \(\operatorname{deg}_I A+|I|=6\), then

\[
\begin{gathered}
v = A\cdot E_I / E_I(F)
\end{gathered}
\]

is strict, provided its denominator is legal. Its value on \(F\) is \(A\), while the product rule gives

\[
\operatorname{div}(A\cdot E_I/E_I(F)) = A[\operatorname{deg}_I A+|I|-E_I^{2}(F)/E_I(F)]/E_I(F)=0.
\]

The same calculation proves that \(A\cdot E_I/[qE_I(F)]\) works at any \(q\) under the stated subset condition. Finite sums serve the linear span of these targets; a sum need not itself be a single spectral atom.

Nambu fields provide the contact version. Choose homogeneous \(P,h_{1},\ldots ,h_{4}\) with \(\sum (\operatorname{deg} h_{i}-1)=2\), and define \(W\) by

\[
\begin{gathered}
\iota _W(dZ_{0}\wedge \cdots \wedge dZ_{5}) = dP\wedge dh_{1}\wedge \cdots \wedge dh_{4}.
\end{gathered}
\]

The defining five-form is closed, which proves \(\operatorname{div} W=0\). Wedging it with the differential of any of its five first integrals gives zero, so \(W\) annihilates each of them. Consequently

\[
\begin{gathered}
F = \Gamma (h_{1},\ldots ,h_{4})+P\cdot K,      A = W(K)
\end{gathered}
\]

gives the strict field \(W/P: W(F)=P\cdot W(K)\), and \(\operatorname{div}(W/P)=0\) because \(W(P)=0\). Its degree is one since \(\operatorname{deg} W=\operatorname{deg} P-1+\sum (\operatorname{deg} h_{i}-1)=\operatorname{deg} P+1\). It is cofactor transport through \(\Phi =(K,P,h_{1},\ldots ,h_{4})\), with target equation \(t_{0}\cdot t_{1}+\Gamma \) and target derivation \(\partial _{0}\). Rational first integrals obey exactly the same exterior-calculus proof, but polynomiality of \(A\) and cancellation of unwanted poles must be checked.

The determinant target has an adjunction interpretation. Suppose \(\operatorname{deg} K>0\) and \(E=V(P,h_{1},\ldots ,h_{4})\subset \mathbb P^{5}\) is a zero-dimensional complete intersection, and write \(d=\operatorname{deg} P\). The five equation degrees sum to \(d+6\). Twist the Koszul resolution by \(d\): its last term is \(\mathcal O(-6)\), with one-dimensional \(H^{5}\), while every preceding term has no \(H^{5}\) and all intermediate projective-space cohomology vanishes. Hence restriction of degree-\(d\) polynomials to \(H^{0}(E,\mathcal O_E(d))\) has one-dimensional cokernel.

The four positive degrees \(\operatorname{deg} h_{i}\) sum to six, so \(\Gamma \) has no linear term in the \(h_{i}\). Thus \(dF=K dP\) on \(E\) and smoothness forces \(K\) to be a unit there. Choose an affine chart containing \(E\). Euler column reduction in \(\operatorname{det} d(K,P,h_{1},\ldots ,h_{4})\) gives \((A/K)|_E=(\operatorname{deg} K)J_E\), where \(J_E\) is the affine complete-intersection Jacobian. The residue functional representing the Koszul cokernel has \(\operatorname{Res}(J_E)=\operatorname{length}(E)\): at a reduced point its local value is one, and the same identity follows at a multiple point from the local algebra trace. It annihilates degree-\(d\) polynomial restrictions by the preceding Koszul calculation. Therefore \(A/K\) has nonzero residue and spans the missing adjoint direction. This proves that the contact selects a specific target through a residue pairing; it does not serve an arbitrary prescribed \(A\).

## 2.3 Perfect-power contact and its source surface

For a split ternary equation \(F=P(U)+Q(V)\), first suppose \(D,H,K\) are homogeneous polynomials with

\[
\begin{gathered}
Q = cH^{m}+D\cdot K,      m\in \{2,3,6\},      c\ne 0,\\
k = \operatorname{deg} H = 6/m,\\
W = \nabla D\times \nabla H.
\end{gathered}
\]

Take \(B(U,T)\) of weighted degree \(3-k\), with weights \((1,1,1,k)\). Then

\[
\begin{gathered}
v = B(U,H)W/D,      A = B(U,H)W(K)
\end{gathered}
\]

is strict: \(W(D)=W(H)=\operatorname{div} W=0\) and \(W(Q)=D\cdot W(K)\). The support \(V(F,D)\) maps to the cyclic surface

\[
\begin{gathered}
S = \{P(U)+cT^{m}=0\} \subset  \mathbb P(1,1,1,k),      T=H(V).
\end{gathered}
\]

Smoothness of the separated \(F\) implies smoothness of \(P=0\): a singular point of \(P\), with \(V=0\), would be singular on \(F\). The cyclic surface \(S\) is smooth by the chain rule and misses the singular vertex of its weighted ambient space. Weighted adjunction gives \(K_S=\mathcal O_S(6-3-k)=\mathcal O_S(3-k)\). In these degrees its sections are exactly the weighted polynomials \(B\), since the defining equation has larger degree. Thus its holomorphic two-forms are residues with numerator \(B\): one constant direction for \(m=2\), three passive linear directions for \(m=3\), and ten quadratic directions for \(m=6\). This explains the allowed multiplier in the field.

The identification of the source form follows from the same computation, not merely adjunction. Namely \(\iota _W \mathrm{vol}_V=dD\wedge dH\), so the residue of \(\iota _W \mathrm{vol}_V/D\) along a reduced component of \(D\) is its multiplicity times \(dH\). In the six-dimensional volume form, multiply this identity by the passive volume form and \(B\), then take the residue along \(F\). On \(D\), substitute \(F=P+cH^{m}\) and \(T=H\); contracting by the homogeneous Euler field gives precisely \(\operatorname{Res}_S(B\cdot \Omega _{\mathrm{weighted}}/(P+cT^{m}))\), up to orientation and the stated multiplicities. Resolve the graph of this rational substitution. The pulled-back source two-form is holomorphic, and the residue boundary map for the supporting divisor is its Gysin map. The displayed exact field identity identifies its image with the class of \(A\); possible boundary components are retained on the graph. Nonvanishing still requires checking that target class.

The identity also has a rational version. If \(H\) and \(K\) are rational homogeneous functions with \(Q=cH^{m}+D\cdot K\), the same derivatives give \(v(F)=A\) and \(\operatorname{div} v=0\) in the function field. This is a certificate only when \(A\) is the required polynomial and all remaining poles are legal. A root \(H\) on the normalization of \(D\) need not descend to an ambient polynomial: distinct branches of a node can have distinct root values. Enforcing an ambient polynomial root would exclude such contacts. Conversely, permitting rational roots without checking their extra poles would admit many false candidates.

The relevant geometric distinction is between a contact relation and the class of its lift to the cyclic surface. An ambient divisor has invariant class; a correspondence applied to this class can vanish in the nontrivial character required by the target. A useful model is a smooth cubic surface \(S\) with hyperplane class \(H_S\) and a twisted cubic \(\Gamma \subset S\). Adjunction gives \(\Gamma ^{2}=1\) because \(\Gamma \) is rational, \(K_S=-H_S\), and \(H_S\cdot \Gamma =3\). Consequently \(r=[\Gamma ]-H_S\) satisfies \(r^{2}=-2\) and \(r\cdot H_S=0\). These are root classes in the negative-definite \(E_{6}\) lattice \(H_S^\perp \). If \(S\to \mathbb P^{2}\) is a cyclic triple-plane quotient, its invariant rational Picard space is generated by \(H_S; \Gamma \) cannot have invariant class, since an invariant class of degree three would have square three. Movement within a linear system preserves its cycle class, although it changes the projected denominator.

This model explains why line constructions and normalized nodal contacts can encode the same Picard geometry. A rational Nambu field may need a second divergence-free field to cancel its poles away from the intended denominator. Such cancellation is an additional rational-function identity, not a consequence of the perfect-power relation.

## 2.4 A complete target map on cubic surfaces

**Cubic-surface theorem.** Let \(G\) be a homogeneous cubic in four variables over a characteristic-zero field \(K\), with smooth projective zero set. For every \(q\ge 1\) and homogeneous \(B\) of degree \(3\cdot q-1\), there is a rational field \(w_q\), with components of degree \(3\cdot q-3\), satisfying \(q w_q(G)=B\) and \(\operatorname{div} w_q=0\). One common denominator of active degree 45 suffices for every \(B\) and \(q\), and is coprime to \(G\).

We use the following classical geometric input. Over an algebraic closure, a smooth cubic surface is the blowup of \(\mathbb P^{2}\) at six points in general position; in particular it has six mutually skew lines, Picard rank seven, and 27 lines in total. Its 45 tritangent planes each cut three distinct lines, and five pass through any given line. These statements include special smooth cubics; see [Huybrechts, Chapter 4, §3](https://www.math.uni-bonn.de/people/huybrech/Notes.pdf). The residue realization needed below is the specialization of [Villaflor Loyola, Theorem 1.1](https://arxiv.org/pdf/1812.03964): if \(G=\ell _{1}Q_{1}+\ell _{2}Q_{2}\) and \(L=V(\ell _{1},\ell _{2})\), then \(\operatorname{Res}(\operatorname{det} d(\ell _{1},Q_{1},\ell _{2},Q_{2})\Omega /G^{2})\) is a fixed nonzero scalar times \(H_S-3[L]\), the scalar depending only on the residue normalization. Together with Griffiths' residue description \(R(G)_{2}\cong H^{2}(S)_{\mathrm{prim}}\), this identifies explicit determinant polynomials with primitive line classes. The remainder of the theorem follows from the calculations below.

Choose a line \(L\) given by \(\ell _{1}=\ell _{2}=0\) and write \(G=\ell _{1}Q_{1}+\ell _{2}Q_{2}\). Cofactor transport through \(\Phi _L=(\ell _{1},Q_{1},\ell _{2},Q_{2})\) gives

\[
\begin{gathered}
J_L = \operatorname{det}(d\Phi _L),\\
w_L = \operatorname{adj}(d\Phi _L)e_{2}/\ell _{1},\\
w_L(G)=J_L,      \operatorname{div} w_L=0,
\end{gathered}
\]

where \(e_{2}\) is the second coordinate vector. The map has output weights (1,2,1,2). Downstairs \(G\) becomes \(a\cdot b+c\cdot d\), and \((1/a)\partial _b\) has value one on this polynomial and zero divergence. The cofactor identity proves both displayed equations, including the derivative of \(1/\ell _{1}\). Equivalently, the second adjugate column annihilates \(\ell _{1}\) and has zero divergence. Thus \(J_L\) is quadratic and \(w_L\) has degree zero.

The four partial derivatives \(G_{i}\) are independent: a constant linear relation would make \(G\) independent of one linear coordinate and its projective hypersurface a singular cone. They account for four of the ten quadratic directions. For six mutually skew lines, the classes \(r_{i}=[L_{i}]-H_S/3\) have intersection matrix \(-I_{6}-11^{T}/3\), because \(L_{i}^{2}=-1, L_{i}\cdot L_{j}=0\) for \(i\ne j\), and \(H_S\cdot L_{i}=1\). Its eigenvalues are \(-3\) and five copies of \(-1\), so its determinant is three. The \(r_{i}\) are independent. The cited residue formula therefore proves that their six \(J_L\) classes form a basis of the six-dimensional quadratic Jacobian quotient. A \(10\times 10\) linear solve expresses \(B\) as \(\sum a_{i}G_{i}+\sum b_{j}J_{L_{j}}\); the field \(\sum a_{i}\partial _{i}+\sum b_{j}\cdot w_{L_{j}}\) serves \(B\) strictly.

Find the lines over a finite extension \(E/K\) and descend by

\[
\begin{gathered}
\overline{w} = \operatorname{Tr}_{E/K}(w)/[E:K].
\end{gathered}
\]

All line coordinates and the coefficients \(a_i,b_j\) lie in some finite extension \(E/K\). Its elements are constants for the four active derivatives, so these commute with normalized trace. Hence \(\overline{w}(G)=B\) and \(\operatorname{div} \overline{w}=0\). Multiplication matrices compute the trace without root approximation: for a component \(N/D\), its normalized trace is \(\operatorname{tr}(\operatorname{adj}(M_D)M_N)/([E:K]\operatorname{det}M_D)\). Every conjugate denominator is a product of linear equations, so cannot contain the geometrically irreducible cubic \(G\). This proves both descent and legality at \(q=1\).

Higher \(q\) requires no new surface cycles. The four quadratic partial derivatives have only the origin as common zero, so form a regular sequence in \(K[u_{0},\ldots ,u_{3}]\). Their quotient has Hilbert series \((1+t)^{4}\), obtained from its Koszul resolution; in particular it vanishes above degree four. For \(\operatorname{deg} B=3\cdot q-1\) and \(q\ge 2\), ordinary polynomial linear algebra therefore gives \(B=\sum b_{i}G_{i}\), with \(\operatorname{deg} b_{i}=3\cdot q-3\). Put \(c=\operatorname{div} b\). Inductively choose \(w\) with \((q-1)w(G)=c\) and \(\operatorname{div} w=0\), and define

\[
\begin{gathered}
v_q = [b+G\cdot w-c\cdot E_{4}/(3(q-1))]/q
\end{gathered}
\]

The two added terms cancel on \(G\) because \(E_{4}(G)=3\cdot G\). For divergence, \(\operatorname{div} b=c, \operatorname{div}(G\cdot w)=c/(q-1)\), and \(\operatorname{div}(c\cdot E_4)=(\operatorname{deg}c+4)c=3\cdot qc\). Their sum is zero. The component degree is \(3\cdot q-3\), and the recursion introduces no new active denominator.

To obtain one denominator over \(K\), choose \(p\in K^{4}\) outside the 45 tritangent planes and normalize each plane equation \(\ell \) by \(\ell (p)=1\). Such \(p\) exists because \(K\) is infinite. Galois permutes the normalized equations, so \(T=\prod \ell \) lies in \(K[u]\) and has degree 45. For each chosen line use a containing tritangent plane as \(\ell _{1}\) in its cofactor field. Its denominator divides \(T\); so do their sum and normalized coefficient trace. The recursion retains \(T\) for every \(q\), and its numerator has degree \(45+3\cdot q-3\). Since \(T\) is a product of linear forms over an algebraic closure, \(\operatorname{gcd}(T,G)=1\). This completes the theorem, including its common-denominator assertion.

## 2.5 From sextics to cubic surfaces

Suppose \(F\) is coordinatewise-even. For a monomial \(A\), choose coordinates \(x\) from \(X\) and \(y\) from \(Y\) with odd exponents; write the remaining \(X\) coordinates as \((a,b)\) and the remaining \(Y\) coordinates as \((c,d)\). Introduce passive ratios and active squares:

\[
\begin{gathered}
\alpha =b/a,      \beta =d/c,\\
\Psi =(x^{2},a^{2},\alpha ,y^{2},c^{2},\beta ),      \operatorname{det}(d\Psi )=16\cdot x\cdot y.
\end{gathered}
\]

In this coordinate order the determinant has the displayed sign; another ordering contributes its permutation sign. For example, each triple map \((x,a,b)\mapsto (x^{2},a^{2},b/a)\) has Jacobian \(4\cdot x\), giving 16xy in six variables. Write \(F=f(Z_{0}^{2},\ldots ,Z_{5}^{2})\). Over \(K=k(\alpha ,\beta )\), it becomes

\[
\begin{gathered}
G(u,s,w,t)=f(u,s,\alpha ^{2}s,w,t,\beta ^{2}t),
\end{gathered}
\]

with coordinates in the corresponding physical order. It is homogeneous cubic in \((u,s,w,t)\). At \(\alpha =\beta =0\), a singular point of this cubic would lift through square roots to a singular point of \(F\), with \(b=d=0\). All omitted derivatives vanish because \(F\) is even in those omitted coordinates. Therefore this specialization is smooth, and so is the cubic over \(K\).

If \(A=x^{r}\cdot a^{m}\cdot b^{n}\cdot y^{j}\cdot c^{h}d^{l}\), its globally odd \(Y\) degree and even total degree ensure that \(j,r\) are odd and \(m+n,h+l\) are even after the selected odd pair has been chosen. Hence its transformed density is

\[
\begin{gathered}
B=\alpha ^{n}\cdot \beta ^{l}u^{(r-1)/2}\cdot s^{(m+n)/2}\cdot w^{(j-1)/2}\cdot t^{(h+l)/2}/16,
\end{gathered}
\]

with the permutation sign inserted if necessary. This is a polynomial of active degree \(3\cdot q-1\). Apply the cubic theorem, append zero passive components in the order of \(\Psi \), and put \(v=\operatorname{adj}(d\Psi )w_q(\Psi )\). Cofactor transport gives \(q\cdot v(F)=A\) and \(\operatorname{div} v=0\), with physical component degree \(6\cdot q-5\).

The target coordinates \(\Psi \) are globally \(Y\)-even. If \(S=\operatorname{diag}(1,1,1,-1,-1,-1)\), differentiating \(\Psi (SZ)=\Psi (Z)\) gives \(\operatorname{adj}(d\Psi )(SZ)=-S \operatorname{adj}(d\Psi )(Z)\). Thus \(v(SZ)=-Sv(Z)\), exactly the required component parities. A homogeneous common denominator can be made \(Y\)-even by multiplication with its involution transform.

Legality follows on the ratio chart from the finite square map: its restriction maps the irreducible hypersurface \(F=0\) dominantly onto \(G=0\). Consequently a denominator coprime to \(G\) cannot pull back to a multiple of \(F\). A passive coefficient pole cannot contain \(F\) either, since the map from \(F\) to the passive parameter plane is dominant; nor can either ratio-chart boundary contain the smooth irreducible hypersurface \(F\). Clearing all these denominators therefore gives \(\operatorname{gcd}(D,F)=1\). Finite sums serve every allowed polynomial \(A\). This proves the all-\(q\), all-target theorem on every smooth coordinatewise-even sextic, and constant block-linear coordinate changes preserve the construction.

**Two-reflection extension.** Suppose \(F\) is globally \(Y\)-even and even separately in one \(X\) coordinate \(x\) and one \(Y\) coordinate \(y\). The same construction serves every allowed \(A\) odd in \(x\) and \(y\). Indeed, the remaining \(X\) pair is jointly even by total degree, and the remaining \(Y\) pair is jointly even by global \(Y\)-parity. Thus the ratio substitution still gives a polynomial cubic and polynomial density.

Here the coordinate-face smoothness argument need not apply, but the generic cubic is smooth nonetheless. If it had a singular point over an algebraic closure of \(k(\alpha ,\beta )\), choose an affine projective chart there and differentiate \(G=0\) with respect to \(\alpha ,\beta \). Characteristic zero lets the derivations extend to this algebraic field. All active derivatives vanish, so \(G_\alpha =G_\beta =0\) at the point. Lift it by square roots. When \(a\ne 0\), the identities

\[
\begin{gathered}
F_b=G_\alpha /a,       F_a=2\cdot aG_s-\alpha G_\alpha /a
\end{gathered}
\]

show that both derivatives vanish; when \(a=0\), also \(b=0\) and joint evenness gives the same conclusion. The pair \((c,d)\) is identical. Finally \(F_x=2\cdot xG_u\) and \(F_y=2\cdot yG_w\) vanish. This contradicts smoothness of \(F\). The previous transport and legality proof now applies without change. This is a partial-target theorem on the larger family: global \(Y\)-evenness alone does not supply the selected reflections.

The degree-45 common denominator lies over \(K\). Clearing passive coefficients contributes physical poles, so it is not a numerical degree bound in the six original coordinates. Nevertheless one finite physical support serves every \(q\) for a fixed \(F\) and pair: fix the quadratic line basis and decompositions of the 56 degree-five active monomials into the partial derivatives. Multiplying these decompositions by monomials supplies every higher-degree decomposition used in the recursion. Only their finitely many passive coefficient poles, the line poles, and the chart boundaries occur. Taking all nine coordinate pairs still gives finite support. This argument bounds neither its physical degree nor its pole multiplicities.

The theorem is a finite algebraic recipe over effectively presented coefficient fields: solve the finite line scheme over the passive field, perform finite linear algebra and trace, then substitute and clear denominators. It gives no practical bound on the size of that calculation.

## 2.6 The conic specialization and physical degree bounds

**Conic theorem.** Let \(\Phi _{0}=(Q_{1},Q_{2},Q_{3},Q_{4},r,s)\), where the \(Q_{i}\) are homogeneous quadratics and \(r,s\) are linear forms, and let \(F=H(\Phi _{0})\) be a smooth sextic. Give \(H\) weights (2,2,2,2,1,1). For every \(q\ge 1\) and density \(B\) of weight \(6\cdot q-4\), the target \(A=\operatorname{det}(d\Phi _{0})B(\Phi _{0})\) has a strict certificate \(N_q/D^q\) over an extension of degree at most 27, with \(\operatorname{deg} D=10\) and \(\operatorname{deg} N_q=16\cdot q-5\). For a fixed line chosen in the construction, the same \(D\) serves every density and \(q\). The parity bounds are stated after the proof.

First, \(\Phi _{0}\) is finite. A nonzero common zero of its six coordinates would be singular on \(F\), since \(H\) and its first derivatives vanish at the origin. Thus the homogeneous ideal generated by the coordinates has finite-dimensional quotient. Lifting a homogeneous basis of that quotient and inducting on degree expresses \(k[Z]\) as a finite module over \(k[\Phi _{0}]\). Equality of dimensions forces the six coordinates to be algebraically independent. The map is therefore finite and surjective; its Jacobian is nonzero in characteristic zero. Any nonzero singular point of \(H\) would lift to one of \(F\), so \(H\) is quasismooth. The cubic surface \(H(Q,0,0)=0\) is smooth as well, because the omitted \(r,s\) derivatives vanish there for weight reasons.

Choose a line on this cubic surface. The 27 lines form a finite étale scheme: each line has normal bundle \(\mathcal O(-1)\), whose \(H^{0}\) and \(H^{1}\) vanish, and the classical count is 27. Hence some line is defined over an extension \(K/k\) of degree at most 27. Choose quadratic coordinates \((x,y,U,V)\) so that it is \(U=V=0\). The equation then has the form

\[
\begin{gathered}
G=a\cdot x^{2}+h\cdot x\cdot y+b\cdot y^{2}+c\cdot x+d\cdot y+e,\\
Q=\begin{pmatrix} a & h/2 & c/2 \\ h/2 & b & d/2 \\ c/2 & d/2 & e \end{pmatrix}.
\end{gathered}
\]

The coefficients depend only on \((U,V,r,s)\). Their physical degrees are two for \(a,h,b\), four for \(c,d\), and six for \(e\). There are no terms cubic in \(x,y\) because the chosen line lies on the restricted cubic surface.

The determinant of \(Q\) is nonzero. Otherwise choose a nonzero kernel vector \(p\) over the spectator function field and homogenize \(G\) with a third active coordinate \(z\). At \(p\) its value and every active derivative vanish. Differentiating its value with respect to any spectator gives zero as well: terms differentiating \(p\) vanish by the active equations. If \(p_z\ne 0\), dehomogenization gives a nonzero singular point of \(H\). If \(p_z=0\), the resulting \(U,V\) derivative equations are the \(U,V\) derivatives of \(H\) at \((p_x,p_y,0,0,0,0)\), since \(a,h,b\) are linear in \(U,V\) plus quadratics in \(r,s\). The \(x,y\) derivatives vanish along the chosen line, and the \(r,s\) derivatives vanish at that point for weight reasons. This again gives a singular point of \(H\), a contradiction. Thus \(D=-8\operatorname{det} Q\) is nonzero of physical degree ten.

At \(q=1\), dividing the target by the Jacobian of the adjusted map gives an affine-linear density \(B_{1}=\kappa\cdot x+\lambda\cdot y+\mu \), with spectator coefficients. Solve

\[
\begin{gathered}
\begin{pmatrix}2\cdot a & h & -c \\ h & 2\cdot b & -d \\ c & d & -2\cdot e\end{pmatrix}
\cdot\begin{pmatrix}p_1\\p_2\\\rho\end{pmatrix}
=\begin{pmatrix}\kappa\\\lambda\\\mu\end{pmatrix}
\end{gathered}
\]

by its adjugate; its determinant is \(D\). The field \(w=(\rho\cdot x+p_{1})\partial _{x}+(\rho\cdot y+p_{2})\partial _y\) satisfies \(w(G)-G \operatorname{div} w=B_{1}\), as coefficient comparison shows: the quadratic terms cancel and the remaining coefficients are exactly the three rows of this system. Also \(\operatorname{div} w=2\cdot \rho \). Cofactor transport gives a physical field \(V\) with \(V(F)-F\cdot \operatorname{div} V=A\). It has degree one, so \(s=\operatorname{div} V\) has degree zero. The Euler correction

\[
\begin{gathered}
v_{1}=V-sE_{6}/6
\end{gathered}
\]

has \(v_{1}(F)=A\) and \(\operatorname{div} v_{1}=0\), since \(E_{6}(F)=6\cdot F\) and \(\operatorname{div}(sE_{6})=6\cdot s\). The numerator of each active component of \(w\) over \(D\) has degree eight, and its cofactor column has degree three; hence \(v_{1}\) has numerator degree eleven. The correction retains \(D\) because \(\operatorname{div} V=2\cdot \rho  \operatorname{det}(d\Phi )\).

The denominator is legal. The irreducibility of \(F\) and finite surjectivity of \(\Phi \) imply irreducibility of \(H\). If \(F\) divided the pullback of \(D\), then \(D\) would vanish on all \(H=0\). But \(D\) is independent of \(x,y\), whereas \(H\) has positive active degree, so \(H\) cannot divide it. The same argument works over every coefficient-field embedding. Normalized trace consequently gives a ground-field certificate with denominator \(\operatorname{Norm}_{K/k}(D)\), of degree at most 270.

### Coefficient raising and the bound at every \(q\)

The following identity is useful beyond conics. Suppose \(F_t=F+tT\) is a family of sextics and \(v_q(t)\) has degree \(6\cdot q-5\), with \(q\cdot v_q(t)(F_t)=A\) and \(\operatorname{div} v_q(t)=0\), where \(A\) is independent of \(t\). A dot denotes coefficient differentiation at zero. Set

\[
\begin{gathered}
v_{q+1}=(qTv_q-F\dot{v}_q)/(q+1)-v_q(T)E_{6}/[6(q+1)].
\end{gathered}
\]

Differentiation gives \(\dot{v}_q(F)=-v_q(T)\) and \(\operatorname{div} \dot{v}_q=0\). If \(W\) denotes the first term, then \(W(F)=(A\cdot T+Fv_q(T))/(q+1)\) and \(\operatorname{div} W=v_q(T)\). The scalar \(v_q(T)\) has degree \(6\cdot q\), so the Euler correction has the required value on \(F\) and divergence to give \((q+1)v_{q+1}(F)=A\cdot T\) and \(\operatorname{div} v_{q+1}=0\). If \(v_q=N_q/D^q\), the numerator identity is

\[
\begin{gathered}
N_{q+1}=[q(T\cdot D+F\dot{D})N_q-F\cdot D\cdot \dot{N}_q-(D/6)N_q(T)E_{6}]/(q+1).
\end{gathered}
\]

Thus coefficient differentiation raises the power of \(D\) by at most one and introduces no new physical divisor.

The necessary coefficient derivatives exist at every smooth member, not merely for a generic choice of coefficients. Keep \(\Phi _{0}\) fixed and vary \(H\) in its weighted coefficient space. Over its smooth locus, the 27-line scheme of \(H(Q,0,0)\) is finite étale, by the normal-bundle calculation above. A chosen line over \(K\) therefore has a unique formal lift in every coefficient direction. A Grassmannian chart and complementary coordinates chosen with nonzero minors at the initial line make the conic formulas regular at that point. All these minors are coefficient units. Every finite derivative needed in the recursion is consequently defined over the same \(K\); no successive field extensions are required.

A monomial of weight \(6\cdot q-4\) in four weight-two and two weight-one variables is a product of \(3\cdot q-2\) weight-two units: pair occurrences of the weight-one variables. Reserve one unit for the initial density, and group the remaining units in triples to form \(q-1\) sextic coefficient directions \(T\). The raising identity constructs the desired target. Add monomials to obtain every \(B\), using the same \(D\). This proves the field-degree, denominator and numerator bounds in the theorem.

### Parity and the relation to all-target coverage

For a globally even \(F\) and odd \(A\), replace \(v\) by \((v(Z)-Sv(SZ))/2\). This preserves both strict identities and gives the required parity. Its denominator divides \(D(Z)^q\cdot D(SZ)^q\), giving degree at most \(20\cdot q\) over \(K\) and \(540\cdot q\) after trace.

If \(\Phi _{0}\) is equivariant for linear involutions on its quadratic and linear coordinate spaces, the bounds improve. The induced involution permutes 27 lines, so fixes at least one. The fixed-line scheme has degree at most 27; choose a line over its residue field and use an adapted eigenbasis. If \(\epsilon _{x},\epsilon _y\) are the active eigenvalues, \(Q\) transforms by conjugation with \(\operatorname{diag}(\epsilon _{x},\epsilon _y,1)\). Its determinant is invariant. Parity projection therefore retains \(D\) itself, and its norm is invariant as well. The resulting bounds are

| Conditions | Degree over the line field | Degree after trace |
|---|---:|---:|
| Equivariant \(\Phi _{0}\) and required target parity | \(\le 10\cdot q\) | \(\le 270\cdot q\) |
| General \(\Phi _{0}\), followed by parity projection | \(\le 20\cdot q\) | \(\le 540\cdot q\) |

For coordinatewise-even \(F\) at \(q=1\), square four chosen coordinates and retain two linearly in \(\Phi _{0}\). Its determinant is a nonzero scalar times their product \(C_I\). The initial density has weight two, giving \(C_I(\sum b_{j}\cdot Z_{j}^{2}+b_{rs}\cdot r\cdot s)\). There are six globally odd four-coordinate carriers, each giving six distinct four-odd target monomials; the single all-six-odd monomial is also obtained. Thus the degree-ten construction covers 37 of the 226 allowed monomials. The six-line construction serves the other 189 two-odd monomials too, but has no stated physical degree bound. Arbitrary quadratics enlarge the bounded construction beyond coordinatewise-even equations while retaining its determinant-density target restriction.

Cofactor transport makes fields explicit, and algebraic cycle classes prove target spanning. The conic and cubic-surface arguments now establish these assertions at every smooth member of their stated families. Their success does not prove that a suitable adapted map or sufficiently rich cycle space exists for a general \(Y\)-even sextic.
