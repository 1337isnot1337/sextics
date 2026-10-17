# 4. The known locus and the open frontier

[Previous: split sextics and K3 surfaces](#technical-information/split-and-k3) · [Contents](#technical-information/introduction) · [Next: computation](#technical-information/computation)

The outstanding problem concerns a Zariski-general smooth globally \(Y\)-even sextic and every invariant primitive class. This chapter proves the dimension statements used to measure our coverage, gives a coupled application of the cubic-surface and Fano mechanisms, and proves the generic-target reduction. The construction theorems themselves are proved in Chapters 2 and 3.

## 4.1 Coefficient spaces, target spaces and orbit dimensions

Write \(S=\mathbb C[X_{0},X_{1},X_{2},Y_{0},Y_{1},Y_{2}]\) and let \(\pm \) indicate total \(Y\)-parity. Counting by \(Y\)-degree gives

\[
\begin{gathered}
\operatorname{dim} S_{6}^{+} = 28+90+90+28 = 236,\\
\operatorname{dim} S_{6}^{-} = 63+100+63 = 226.
\end{gathered}
\]

Indeed, the summand of \(Y\)-degree \(j\) has dimension \(\binom{8-j}{2}\binom{j+2}{2}\). Hence the parameter space of even sextics is \(\mathbb P^{235}\). For smooth \(F\) its six quintic partial derivatives form a regular sequence: their affine common zero is only the origin, and a homogeneous system of parameters in a polynomial ring is regular. The Koszul resolution, with three even and three odd generators, gives the Hilbert and trace series

\[
\begin{gathered}
H(t) = (1+t+t^{2}+t^{3}+t^{4})^{6},\\
\Theta (t) = (1+t^{2}+t^{4}+t^{6}+t^{8})^{3},\\
\operatorname{dim} (R_F)_d^\pm  = ([t^{d}]H \pm  [t^{d}]\Theta )/2,\\
R_F = S/J(F).
\end{gathered}
\]

For example, the trace follows by dividing \((1-t^{5})^{3}(1+t^{5})^{3}\) by \((1-t)^{3}(1+t)^{3}\). Griffiths' residue identification from Chapter 1 therefore gives primitive invariant Hodge numbers (208,866,208), in types (3,1), (2,2), (1,3). In degree six, the same calculation is \(226-18=208\): the odd Jacobian directions are \(Y_{j}F_{X_{i}}\) and \(X_{i}F_{Y_{j}}\), and there are no linear syzygies among the quintic partials. The ambient \(h^{2}\) adds one algebraic middle direction.

Let \(G=GL_{3}(X)\times GL_{3}(Y)\), of dimension eighteen. For a linear coefficient family \(V\) preserved by a connected subgroup \(H\subset G\), the image of \(G\times V\to S_{6}\) has dimension at most \(\operatorname{dim} V+18-\operatorname{dim} H\): the action of \(H\) on the source, \((g,F)\mapsto(gh^{-1},hF)\), supplies fibres of dimension \(\operatorname{dim} H\). A matching differential rank at any point proves equality. At the Fermat member \(F_{0}=\sum Z_{i}^{6}\) the eighteen orbit derivatives are the distinct monomials \(6\cdot Z_{i}^{5}\cdot Z_{j}\), with \(i,j\) in the same parity block. Thus, for a monomial coefficient family containing \(F_{0}\), counting those derivatives outside \(V\) proves the required lower bound without a generic-rank assumption.

The same eighteen independent derivatives give affine orbit dimension eighteen at \(F_{0}\) and generically. Projectivization removes the common scalar direction, so the generic projective orbit has dimension seventeen. We report the projective normal-form dimension, the dimension of its \(G\)-saturation, and the quotient dimension. The latter is saturation dimension minus seventeen; in particular, the ambient quotient has dimension 218.

| Smooth sextic locus | Certificate conclusion | \(q\) | Normal form | Saturation | Quotient |
| --- | --- | --- | ---: | ---: | ---: |
| Coordinatewise-even \(F=f(X_{0}^{2},X_{1}^{2},X_{2}^{2},Y_{0}^{2},Y_{1}^{2},Y_{2}^{2})\) | Constructive strict cubic-surface fields | Every positive \(q\) | 55 | 67 | 50 |
| \(F\) separately even in \(Y_{0},Y_{1},Y_{2}\), or its \(X/Y\) mirror | Finite covering-curve construction | Every positive \(q\) | 118 | 124 | 107 |
| Arbitrary \(f(X)+g(Y)\) | Finite elliptic-companion construction | Every positive \(q\) | 55 | 55 | 38 |
| Crossed \(p(X_{0},X_{1},Y_{0})+r(X_{2},Y_{1},Y_{2})\), with global \(Y\)-evenness | Finite elliptic-companion construction | Every positive \(q\) | 31 | 39 | 22 |
| Polarized split \(f(X+Y)+f(X-Y)\), with the order-three plane family below | K3 correspondence existence | Every positive \(q\) | 11 | 24 | 7 |
| Two arbitrary same-parity binary blocks and one square-binary block | Explicit binary-block construction | 1,2 | 17 | 25 | 8 |

Here the order-three family is \(f(z_{0},z_{1},z_{2})=g_{6}(z_{0},z_{1})+z_{2}^{3}g_{3}(z_{0},z_{1})+a z_{2}^{6}\). The last row is \(F=P_{0}(X_{0},X_{1})+P_{1}(Y_{0},Y_{1})+P_{2}(X_{2}^{2},Y_{2}^{2})\). The proofs of its explicit formulas are in [the binary-block chapter](#technical-information/binary-blocks); arbitrary binary sextics need not have the reflections required by the cubic-surface construction.

**Proof of the dimensions.** Cubics in six squares have 56 coefficients. Their preserving diagonal torus has dimension six, and all twelve off-diagonal Fermat orbit monomials lie outside the family. Hence the saturated affine dimension is 56+12=68. With three separate \(Y\) reflections the coefficient count is 28+45+36+10=119, according to half the \(Y\)-degree. \(GL_{3}(X)\) and the diagonal \(Y\) torus preserve this space, a subgroup of dimension twelve; exactly six Fermat orbit monomials lie outside it. The saturated cone therefore has dimension 125.

The ordinary split family has 28+28=56 coefficients and is already \(G\)-stable. Each crossed ternary block contributes sixteen coefficients, giving 32. \(GL_{2}(X_{0},X_{1})\times G_{m}(X_{2})\times G_{m}(Y_{0})\times GL_{2}(Y_{1},Y_{2})\), of dimension ten, preserves it; the eight Fermat derivatives mixing the indicated subblocks lie outside it. The binary family has 7+7+4=18 coefficients, is preserved by a subgroup of dimension ten, and again has exactly eight outside Fermat derivatives. These give saturated cone dimensions 40 and 26 respectively.

For the polarized family, the twelve coefficients are 7+4+1. Put \(U=X+Y\) and \(V=X-Y\). At \(f=\sum z_{i}^{6}\) the family tangent consists of \(h(U)+h(V)\) for the twelve order-three monomials \(h\). A block-linear infinitesimal change in \(X,Y\) becomes

\[
\begin{gathered}
\delta U=C\cdot U+E\cdot V,     \delta V=C\cdot V+E\cdot U,\\
\delta F=6\sum _{i} [U_{i}^{5}(C\cdot U+E\cdot V)_{i}+V_{i}^{5}(C\cdot V+E\cdot U)_{i}],
\end{gathered}
\]

with arbitrary \(3\times 3\) matrices \(C,E\). The eighteen displayed directions are independent. The nine \(E\) directions have mixed \(U,V\) degree and do not meet the family tangent. Of the nine \(C\) directions, exactly five meet it: \(i,j\in \{0,1\}\), and \(i=j=2\). Thus the combined tangent dimension is \(12+18-5=25\). The simultaneous \(GL_{2}(z_{0},z_{1})\times G_{m}(z_{2})\), of dimension five, supplies the matching upper bound. Subtracting one for projectivization and seventeen for the generic orbit proves every entry in the table. All witnesses used here are smooth; for the polarized witness, the invertible \(U,V\) change reduces smoothness to Fermat. ∎

The largest proved all-target dimensions are consequently **118/124/107 for existence and finite constructive legal certificates**, and **55/67/50 for constructive strict certificates**. A finite construction means specified terminating algebraic operations, as in Chapter 3; it need not be computationally practical. These numbers measure proved families, not the unknown full solvable locus.

## 4.2 Scope of the partial-target constructions

The two-reflection theorem of Chapter 2 requires one selected \(X\) reflection and one selected \(Y\) reflection, and constructs all targets odd in those two coordinates. Counting degree-six monomials with these parities gives 104 coefficients for \(F\) and 34 raw \(q=1\) targets. Exactly two odd Jacobian directions lie in that target character, namely \(X_{i}F_{Y_{j}}\) and \(Y_{j}F_{X_{i}}\) for the selected coordinates. They are independent by regularity of the partial derivatives. Thus the primitive sector has dimension 32. The count is also obtained directly by taking the indicated coefficients of \(\prod _{i}(1-t\epsilon _{i})^{-1}\) in the group algebra of the three sign characters. This is a sector theorem, not all-target coverage on that coefficient family.

For the conic construction with four arbitrary quadrics and two linears, the weighted sextic \(H\) has 77 coefficients. Four quadrics contribute \(4\cdot 21\) and two linears contribute \(2\cdot 6\) parameters. Consequently its coefficient image has affine dimension at most 77+84+12=173, even before accounting for changes of adapted coordinates. Its intersection with \(S_{6}^{+}\) is proper. The construction serves the specified Jacobian-density targets and has the denominator bounds proved in Chapter 2; it does not assert that those densities fill the target space.

The weighted-Fano theorem of Chapter 3 likewise serves \(A=\operatorname{det}(d\Phi )b(\Phi )\). It covers every primitive \(q=1\) nonlinear polynomial Piola atom under its stated hypotheses and removes the atom's spectral condition. The density condition remains. A theorem that transfers all cohomology from a smaller model need not transfer all cohomology of the covering fourfold.

For arbitrary smooth ternary \(f\), the polarized split theorem in [Chapter 3a](#technical-information/split-and-k3) supports a rank-1073 invariant substructure including the ambient class, with primitive Hodge numbers (189,694,189). Its \(q=1\) sector contains every odd \(A\) with \(A(X,X)=0\). The remaining rank-210 piece has Hodge numbers (19,172,19) and is an exterior square of primitive K3 cohomology. Chapter 3a proves both the decomposition and the sufficient algebraic Kuga–Satake criterion, including its application to the order-three family. No unconditional support theorem for that remaining piece for arbitrary \(f\) is asserted.

## 4.3 A coupled cyclic-seven application

This example is useful because the quotient and its smoothness can be written out, including the mixed terms. Let \(\sigma \) act on \((x,y,z)=(X_{0},X_{1},X_{2})\) with weights (1,2,4) modulo seven and fix \(Y\). The complete \(\sigma \)-invariant, \(Y\)-even sextic family is

\[
\begin{gathered}
F=a x^{5}\cdot y+b y^{5}\cdot z+c z^{5}\cdot x+d x^{2}\cdot y^{2}\cdot z^{2}\\
+x\cdot y^{3}Q_{0}(Y)+x^{3}zQ_{1}(Y)+y\cdot z^{3}Q_{2}(Y)+g(Y),
\end{gathered}
\]

where \(Q_{i}\) are arbitrary ternary quadratics and \(g\) is an arbitrary ternary sextic. This is a fifty-dimensional coefficient space. Every smooth member has its entire \((\tau ,\sigma )\)-invariant \(H^{4}\) supported on a divisor. All nineteen \(q=1\) primitive directions in this sector admit strict cubic-surface constructions.

**Proof.** Introduce the rational coordinates

\[
\begin{gathered}
U=x^{2}\cdot y/z,     V=y^{2}\cdot z/x,     W=z^{2}\cdot x/y,\\
p=aU^{2}W+bV^{2}U+cW^{2}V+dUVW,\\
P=p+UVQ_{0}+UWQ_{1}+VWQ_{2}+g.
\end{gathered}
\]

Substitution gives \(F=P\). The target is the weighted fourfold \(\mathcal W=\{P=0\}\subset \mathbb P(2,2,2,1,1,1)\). On a chart \(Y_{j}=1\) and \(x\cdot y\cdot z\ne0\), the exponent matrix for \((x,y,z)\mapsto (U,V,W)\) is

\[
\begin{gathered}
\begin{pmatrix}2&1&-1\\-1&2&1\\1&-1&2\end{pmatrix},
\qquad \det=14.
\end{gathered}
\]

Its kernel consists of \(\sigma \) and the simultaneous sign change of \(x,y,z\), the latter being \(\tau \) projectively on this chart. Thus the rational map has degree fourteen and identifies the function field of \(\mathcal W\) with the invariant function field of \(X\). The full inverse image of \(P=0\) is \(F=0\), which is irreducible because a reducible projective hypersurface of this dimension is singular along an intersection of components.

We check quasismoothness on every coordinate stratum. Smoothness of \(F\) implies smoothness of its plane restrictions \(F(X,0)\) and \(g(Y)\), because derivatives in the omitted coordinates vanish there. It also forces \(ab\cdot c\ne0\) by examining the three \(X\)-coordinate points. On \(U\cdot V\cdot W\ne 0\), the coordinate map is étale, with Jacobian \(14\cdot x\cdot y\cdot z\), so a singular cone point of \(P\) would lift to one of \(F\). If \(U=0\) and \(V\cdot W\ne 0\), then \(P_V=W(cW+Q_{2})\) and \(P_W=V(2\cdot cW+Q_{2})\); these cannot both vanish. The other two such strata follow cyclically. If \(U\ne 0,V=W=0\), the equation reduces to \(g=0\): for \(Y\ne 0\) use \(\nabla g\ne 0\), while for \(Y=0\) use \(P_W=aU^{2}\ne 0\). Treat the \(V\)-only and \(W\)-only strata in the same way. If \(U=V=W=0\), use smoothness of \(g\) once more. These exhaust the nonzero cone points.

The singular locus of the weighted ambient space meets \(\mathcal W\) along the smooth plane cubic \(p=0\) at \(Y=0\). Transversely the singularities are 1/2(1,1,1), since the three \(Y\) directions are the odd stabilizer directions. Their age is 3/2, so they are terminal. Weighted adjunction gives \(-K_\mathcal W=\mathcal O(3)\). The normal-Fano support theorem of Chapter 3 therefore gives divisor-supported \(H^{4}\) on a resolution. The quotient-transfer theorem there transfers this support to \(H^{4}(X)^{\tau ,\sigma }\). This proves the all-\(q\) support assertion without claiming that the rational quotient map extends over every boundary point.

For the strict \(q=1\) construction, project to the \(Y\)-direction plane. Over \(k(\mathbb P^{2}_Y)\) the projective generic fibre has equation

\[
\begin{gathered}
p(U,V,W)+T[UVQ_{0}+UWQ_{1}+VWQ_{2}]+T^{3}g=0.
\end{gathered}
\]

Its affine part \(T\ne 0\) is smooth by generic smoothness of the projection from the smooth locus \(Y\ne 0\) of \(\mathcal W\); the projection is dominant, since its nonconstant cubic equation has affine solutions over an algebraic closure of the base field. At \(T=0\) smoothness follows from that of \(p\). Hence this is a smooth cubic surface. Set \(T=Y_{0}^{2}, \alpha =Y_{1}/Y_{0}\) and \(\beta =Y_{2}/Y_{0}\). The full six-coordinate Jacobian of \((U,V,W,T,\alpha ,\beta )\) is \(28\cdot x\cdot y\cdot z/Y_0\).

The required numerator character is trivial under \(\sigma \) and odd under \(\tau \), since the residue volume has those respective characters. Enumerating monomials gives

\[
x\cdot y\cdot z\cdot k[Y_{0},Y_{1},Y_{2}]_{3} \oplus  \operatorname{span}\{x^{3}\cdot y^{2},y^{3}\cdot z^{2},z^{3}\cdot x^{2}\}\cdot k[Y_{0},Y_{1},Y_{2}]_{1}.
\]

There are 10+9=19 directions. Dividing by the full Jacobian gives the quadratic cubic-surface densities \(T^{2}\cdot \alpha _{i}\cdot \alpha _{j}\cdot \alpha _{k}/28\) and \(UT\alpha _{i}/28, VT\alpha _{i}/28, WT\alpha _{i}/28\), where \(\alpha _{0}=1, \alpha _{1}=\alpha , \alpha _{2}=\beta \). Chapter 2's six-line theorem, trace and full Piola transport now supply strict fields. The coordinates are \(Y\)-even and the Jacobian is \(Y\)-odd, giving the required field parity; chart divisors and line divisors avoid \(F\). The degree-six odd Jacobian generators \(Y_{j}F_{X_{i}}, X_{i}F_{Y_{j}}\) have nonzero \(\sigma \)-characters \(-w_{i},w_{i}\), with \(w_{i}\in \{1,2,4\}\). Consequently none of the nineteen directions is Jacobian-trivial. ∎

For completeness, all character dimensions here follow from one explicit Koszul series. In the ring with \(u^{7}=v^{2}=1\), take the coefficient of \(t^{6\cdot q}\cdot u^{0}\cdot v^{1}\) in

\[
\begin{gathered}
\prod _{i} (1-t^{5}\cdot u^{-w_{i}}v^{e_{i}})/(1-t\cdot u^{w_{i}}v^{e_{i}}),\\
w=(1,2,4,0,0,0),     e=(0,0,0,1,1,1).
\end{gathered}
\]

At \(q=1\) it is 19; at \(q=2\) it is \(395-276+9=128\), the three terms being the polynomial, first Koszul and second Koszul contributions. Hodge symmetry gives (19,128,19). The same monomial count in \(S_{6}\) gives fifty coefficients. Diagonal \(X\) changes and all \(Y\) changes preserve the family, so its projective saturation has dimension at most 49+6=55. At the smooth split Klein member, the six off-diagonal \(X\) orbit derivatives are nonzero and have the six distinct nontrivial \(\sigma \)-characters. They therefore supply six independent directions outside the invariant family, proving equality. That witness is smooth: a zero coordinate at a common zero of the ternary Klein gradient forces all coordinates to vanish; on the coordinate torus, multiplying its three derivative equations gives \(1=(-5)^{3}\), a contradiction. This remains partial-sector coverage on a family of projective dimension 49, saturated dimension 55.

## 4.4 One generic nonzero target suffices

Here “generic” means the geometric generic point of the full even-sextic parameter space, or equivalently a finite-type certificate/support family dominating that space. An isolated certificate, however difficult to find, does not satisfy this hypothesis.

**Theorem.** Suppose a dominating finite-type family of reduced divisor supports on smooth even sextics carries one nonzero invariant primitive (3,1) class at the geometric generic point. Its Gysin image then carries the entire invariant primitive \(H^{4}\) there. In particular, a generic \(q=1\) certificate for any one nonzero primitive target, such as \(X_{0}^{3}\cdot Y_{0}^{3}\), suffices for every required target. If \(E_i\) are the resolved support components, necessarily \(\sum _i h^{2,0}(E_i)\ge 208\).

We use two standard inputs from variation of Hodge structure. First, the infinitesimal residue variation for a hypersurface is multiplication by the deformation polynomial in its Jacobian ring. Second, images of morphisms of polarizable variations are polarizable subvariations, their polarization-orthogonal complements are again subvariations, and such morphisms are strict for the Hodge filtration. The first identification follows by differentiating \(A\cdot \Omega /F^{2}\): its next leading numerator is \(-2\cdot gA\), a harmless nonzero scalar times multiplication. For the second input, a morphism preserves the Hodge decomposition, so its image and kernel are Hodge substructures and the map is strict. Positivity of the associated Hodge metric makes the polarization nondegenerate on a substructure; its orthogonal complement is flat and is again a Hodge substructure, giving the required splitting. These arguments apply fibrewise and in families of constant rank. Resolve the support family and shrink its base before applying them.

**Proof of the linear-algebra step.** At Fermat,

\[
\begin{gathered}
R=\mathbb C[Z_{0},\ldots ,Z_{5}]/(Z_{0}^{5},\ldots ,Z_{5}^{5}),\\
V=R_{6}^{-},     G=R_{6}^{+},     W=R_{12}^{-},\\
(\operatorname{dim} G,\operatorname{dim} V,\operatorname{dim} W)=(218,208,866).
\end{gathered}
\]

For \(g\in G\) the Higgs map is \(M_g:V\to W, u\mapsto gu\). The diagonal Fermat automorphisms act by distinct characters on the monomial basis in each fixed degree, so its Hodge metric is diagonal. For a monomial \(g=Z^{a}\), the positive operator \(M_g^{\dagger} M_g\) is consequently diagonal, and its entry on \(Z^{u}\) is nonzero exactly when \(u+a\le (4,\ldots ,4)\) coordinatewise.

The following finite calculation proves three combinatorial facts: these support signatures distinguish all 208 monomials \(u\); every \(u\) has a common nonzero product with the anchor \(b=(1,1,1,1,1,1)\); and \(G\cdot V=W\). It is included in full, uses only integer comparisons and sets, and also checks the one-reflection variant used below.

```python
from itertools import product

def check(extra, anchor, expected):
    def parity(u): return sum(u[3:]) % 2
    box = list(product(range(5), repeat=6))
    G = [u for u in box if sum(u)==6 and parity(u)==0 and extra(u)]
    V = [u for u in box if sum(u)==6 and parity(u)==1 and extra(u)]
    W = {u for u in box if sum(u)==12 and parity(u)==1 and extra(u)}
    signatures, images = [], []
    for u in V:
        image = {tuple(x+y for x,y in zip(u,a)) for a in G
                 if all(x+y<=4 for x,y in zip(u,a))}
        images.append(image)
        signatures.append(tuple(all(x+y<=4 for x,y in zip(u,a)) for a in G))
    assert (len(G),len(V),len(W)) == expected
    assert len(set(signatures)) == len(V)
    anchor_image = images[V.index(anchor)]
    assert all(image & anchor_image for image in images)
    assert set().union(*images) == W
    return expected

assert check(lambda u: True, (1,1,1,1,1,1), (218,208,866)) == (218,208,866)
assert check(lambda u: u[5]%2==0, (1,1,1,1,2,0), (144,126,492)) == (144,126,492)
```

Distinct support signatures give distinct joint eigenvalue tuples, regardless of the actual positive metric coefficients. Polynomial interpolation in the commuting diagonal operators therefore supplies every monomial projector \(P_u\). Given a common product exponent \(w\ge u,b\), write \(a=w-u\) and \(c=w-b\). Both are allowed even sextic exponents, so \(P_b M_{Z^{c}}^{\dagger} M_{Z^{a}}P_u\) is a nonzero matrix unit from the \(u\)-line to the \(b\)-line. Taking adjoints and composing supplies every matrix unit. Thus the \(M_h^{\dagger} M_g\) generate \(\operatorname{End}(V)\).

**Proof of the geometric step.** Let \(U\) be a polarizable subvariation of the invariant primitive variation, over a dominant base change. Orthogonal splitting shows that every \(M_h^{\dagger} M_g\) preserves \(U^{3,1}\). The full endomorphism algebra forces that piece to be zero or all of \(V\). To justify using Fermat even when the support family is defined only over a different open set, choose finitely many matrix-unit words witnessing generation. Their nonzero determinant persists in a real-analytic neighbourhood of Fermat. The smooth locus of a dominant finite-type map meets that neighbourhood with surjective tangent map; it therefore supplies all allowed Higgs directions there. Hodge numbers of the subvariation are locally constant, so the zero-or-full alternative holds generically.

If \(U^{3,1}=V\), stability under the Higgs field and the verified equality \(G\cdot V=W\) force \(U^{2,2}=W\). Complex conjugation gives its whole (1,3) part as well. Apply this to the image of the component Gysin maps, intersected with the invariant primitive sector. The assumed nonzero class rules out the zero alternative. Strictness gives a surjection \(\bigoplus _i H^{2,0}(E_i)\to H^{3,1}(X)^\tau \), proving the lower bound 208. Exceptional components whose image has codimension at least two contribute no (3,1) part, so they do not weaken that bound. ∎

A certificate over the algebraic closure of the universal coefficient field uses finitely many algebraic coefficients. They lie in a finite extension; the denominator and its support spread over a nonempty open of a finite-type base change. Thus the theorem applies. Chapter 1 then converts the resulting support back to certificates for every \(q=1\) and \(q=2\) target. The class of \(X_{0}^{3}\cdot Y_{0}^{3}\) is nonzero at Fermat and hence generically: its exponents are at most four, so it is a nonzero monomial in the displayed Fermat ring.

### The intermediate one-reflection locus

Retain the \(Y_{2}\) reflection \(r\) as well as \(\tau \). The unresolved sector has \(\tau \)-character +1 and \(r\)-character \(-1\); its residue numerators are \(Y\)-odd and \(Y_{2}\)-even. The second calculation above proves dimensions (126,492,126), all monomial projectors, anchor connectivity and middle-piece multiplication surjectivity for the allowed 144-dimensional infinitesimal deformation space. Repeating the proof verbatim gives: one dominating support carrying a nonzero residual (3,1) class carries this entire residual sector. The \(r\)-invariant complement already has the Fano support of Chapter 3. Hence that missing premise would settle all targets on an open of the one-reflection family, and would force \(\sum _i h^{2,0}(E_i)\ge 126\) for a residual support.

Its coefficient dimension is 158, by counting even-\(Y\), even-\(Y_{2}\) sextics. The preserving subgroup \(GL_{3}(X)\times GL_{2}(Y_{0},Y_{1})\times G_{m}(Y_{2})\) has dimension fourteen. Four outside Fermat orbit monomials, \(Y_{2}^{5}\cdot Y_{0},Y_{2}^{5}\cdot Y_{1},Y_{0}^{5}\cdot Y_{2},Y_{1}^{5}\cdot Y_{2}\), attain the upper bound \(158+18-14=162\). The conditional projective dimensions are therefore 157/161/144. A support with the required nonzero residual image has not been constructed.

## 4.5 Raising \(q\) by differentiating a generic certificate

The preceding theorem settles the Hodge-theoretically required \(q=1,2\) once its premise is met. There is also an algebraic identity giving every positive \(q\) over the generic coefficient field.

**Proposition.** Let \(F_t=F+tC\), with \(C\) an even sextic, and suppose \(A\) is independent of \(t\) and

\[
\begin{gathered}
K_q(F_t,A;v_t)=F_t^{q+1}R_t,\\
K_q(F,A;v)=A-q\cdot v(F)+F\cdot \operatorname{div}(v).
\end{gathered}
\]

Then \(w=(qCv-F\dot{v})/(q+1)\) satisfies

\[
\begin{gathered}
K_{q+1}(F,A\cdot C;w)=-F^{q+2}\dot{R}/(q+1).
\end{gathered}
\]

**Proof.** The product rules for \(v(F)\) and \(\operatorname{div}(v)\) give the exact identity

\[
K_{q+1}(F,A\cdot C;w) = C K_q(F,A;v) - F \partial _t K_q(F_t,A;v_t)|_{0}/(q+1).
\]

Differentiating \(F_t^{q+1}R_t\) cancels its \(C F^{q+1}R\) term and leaves the stated expression. The field has degree \(6(q+1)-5\) and the required parity. For \(v=N/D\) it has denominator dividing \(D^{2}\); its reduced support and coprimality with \(F\) are preserved. ∎

Over the universal coefficient field, the direction \(\dot{F}=C\) is a derivation. It extends uniquely to every finite separable coefficient extension in characteristic zero. Applying the proposition there and then the normalized trace of Chapter 1 produces a certificate over the original field. Thus an analytic choice of solutions is unnecessary, but a generic family is necessary.

Every odd monomial of degree \(6\cdot q\) is a product of an odd sextic and \(q-1\) even sextics. To prove this, let its total \(Y\)-degree be \(s\), and choose \(b\in \{1,3,5\}\) congruent to \(s\) modulo six. Select \(b Y\) factors and \(6-b X\) factors for the odd sextic; there are enough since both remaining totals are nonnegative multiples of six. Group the remaining \(Y\) factors into all-\(Y\) sextics and the remaining \(X\) factors into all-\(X\) sextics. Iterating the proposition and taking linear combinations proves the all-positive-\(q\) assertion. This differentiates a coefficient family; it cannot be applied to an isolated successful tuple without such an extension.

## 4.6 What remains open

The general mechanism must produce a support with a nonzero global Gysin image, or a certificate accomplishing the same thing. The available methods impose explicit hypotheses: individual reflections, polynomial Jacobian densities, suitable cyclic quotients, separated companions, or an algebraic Kuga–Satake correspondence. Their proofs do not establish those hypotheses for general \(F\). Existence of a contact configuration alone also does not calculate its Gysin image.

A concrete unresolved input is

\[
\begin{gathered}
F = X_{0}^{6}+X_{1}^{6}+X_{2}^{6}+Y_{0}^{6}+Y_{1}^{6}+Y_{2}^{6}\\
+X_{0}^{3}\cdot X_{1}\cdot Y_{0}\cdot Y_{1}+X_{1}^{3}\cdot X_{2}\cdot Y_{1}\cdot Y_{2},\\
q = 1,     A = X_{0}^{3}\cdot Y_{0}^{3}.
\end{gathered}
\]

It is smooth by a direct estimate over \(\mathbb C\). At a hypothetical nonzero common zero of the partial derivatives, choose a coordinate of largest modulus \(M\). Its pure-sixth derivative has modulus \(6\cdot M^{5}\), whereas the sum of the absolute coefficients of all its mixed derivative terms is at most four, giving modulus at most \(4\cdot M^{5}\). This is impossible. The target is nonzero modulo \(J(F)\): none of the monomials in any \(Z_{i}F_{Z_{j}}\) is \(X_{0}^{3}\cdot Y_{0}^{3}\), so extraction of that coefficient annihilates \(J(F)_{6}\) but takes value one on \(A\). No certificate for this input is known here.

Failure for a selected denominator or a restricted numerator space does not exclude support on other divisors. The generic reduction identifies a sufficient next theorem: construct one nonzero support class in a family dominating the full even-sextic parameter space. Solving isolated atlas instances may suggest such a construction, but does not by itself supply that family.

## 4.7 Structured targets beyond the holdout

An open atlas entry means that its exact existence statement has no accepted
Lean proof here. It need not be an instance of unknown mathematical existence.
The following targets separate the task of extracting explicit certificates
from known geometric arguments from the task of extending those arguments to
new sectors.

| Target | Structure and remaining task |
| --- | --- |
| [Reflection · coupled Fano quotient](#case/reflection-coupled-fano) | Existence follows from §3.3. Compute a support or rational field on a coupled sextic with one serving reflection. |
| [Cyclic triple cover · Fano density](#case/cyclic-triple-fano) | Existence follows from §3.4. Make the weighted-Fano density construction explicit for an order-three cover. |
| [Split ternaries · third-order pole](#case/split-ternary-q2) | Existence follows from §§3A.1–3A.3. Construct a certificate at \(q=2\), beyond the elementary split Euler target degrees. |
| [Crossed ternaries · elliptic transfer](#case/crossed-ternary-asymmetric) | Existence follows from the involution-stable split theorem in §3A.3. The individual coordinate reflections miss this target. |
| [Polarized split · K3 remainder](#case/polarized-k3-remainder) | The target has a nonzero component in the K3 exterior-square remainder of §§3A.4–3A.6. |
| [Coupled Klein · nontrivial character](#case/klein-coupled-character) | The numerator selects a nontrivial order-seven residue character, outside the invariant sector of §4.3. |
| [Permutation symmetry · residual sector](#case/symmetric-sextic-residual) | The numerator is symmetric but the residue is alternating under each permutation group, outside the quotient-density sector. |
| [Rank-one coupling · biquartic pencil](#case/rank-one-biquartic) | A single factored mixed component destroys the split while retaining a structured binary-cubic discriminant. |
| [Quadric contact · broken reflections](#case/quadric-contact-broken) | A deformation of an accepted example cannot use its old quadric denominator, even with completely new numerators. |
| [Four plus two · suspension remainder](#case/four-plus-two-residual) | The decomposition is \(4+2\), rather than \(3+3\), and the target lies outside the two visible reflection sectors. |

The first four have geometric existence proofs; the book also explains finite
algebraic procedures in principle. Their atlas entries ask for a concrete
certificate or a formal proof, not a new proof that the geometric theorem is
true. For the other six, the stated methods do not supply the selected class;
this is not an assertion that every possible method has been ruled out.

All ten sextics are smooth by reduction modulo five, and the selected targets
are nonzero in their Jacobian rings. Their records include exact, reproducible
checks of these statements and the specified symmetry and denominator
obstructions. The motivations explain the scope of each check. Neither those
checks nor a visually interesting slice constitutes an accepted certificate.
