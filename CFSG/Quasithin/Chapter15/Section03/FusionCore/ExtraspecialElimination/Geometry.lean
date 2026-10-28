module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.LocalAlgebra
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.RankComparison
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.StrongConstruction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Sections
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Local
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Selection
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Consequences

/-!
# Geometric deductions for the extraspecial branch of 15.3.49

The two seeds retain their source meanings: U_H = localSpan Z_S H and
V_H = localSpan V H. The endpoint spans use their actual conjugate seeds.
Geometry.Sections constructs D as the image of D_H in U_H/Z, identifies
section-centralizer kernels through the faithful conjugation action, and
computes the literal star ranks and quotient dimensions. Its kernel theorem
applies to either SectionAction denominator, Z or centralizerLayer H U_H.

Geometry.Local proves F.9.8(f) from fusion and the abelian centralizer span,
and proves both cross-centralizations from the omega-center bounds, the
normalizer test of 15.3.47, and the F.9.13 commutator bounds. Geometry.Consequences
then proves the quotient-centralizer equality and D_gamma < U_gamma.
Geometry.Selection translates the selected F.9.16 rank inequality into
quadratic ordinary offending by the actual star images.

Explicit earlier inputs for the parent to discharge are:
* F.9.1, the faithful SectionActions from 15.3.48 and 15.3.49(a), and
  15.3.49(c)–(d) at the two conjugate endpoints;
* the fusion statement of 15.3.46(1), the ambient test of 15.3.47, and
  the abelian span at C_G(Z);
* the endpoint placement and commutator bounds of F.9.13(2)–(3), its
  noncentrality assertion (5), and F.9.16(4)'s positive selected ranks.
The normalizer of the opposite central line used by Selection comes from
placing U_H in the opposite endpoint and that endpoint's SectionAction.

This is an incomplete source assembly. In particular, ordinary offending
is not B.1.2 best offending. The missing subgroup weight comparisons,
the fixed-plane calculation for (m), and the derivation of the reversed
star-image equality by F.9.17 remain separate obligations. The latter
identity gives the symmetric cover by
Geometry.starImage_eq_iff_centralizer_cover; it is not assumed to follow
from the rank equalities here. StrongConstruction is reused without
asserting its undischarged symmetry premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.49(e)–(h), (m)–(n), printed pp.1143–1144; F.9.8–17, printed
pp.321–324; and B.1.2–3, printed p.68.
-/
