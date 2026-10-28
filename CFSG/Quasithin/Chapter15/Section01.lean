module

public import Theory.GroupTheory.CentralizerControlProjection
public import CFSG.Quasithin.Chapter15.Section01.SourceReduction
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonComplete
public import CFSG.Quasithin.Chapter15.Section01.Source14_2Consumer
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedNineControl
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceResidualIntersection
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceNineComponents
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceNineResidual
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceNinePlaneAction
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceCubicExclusion
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceTrialityExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonParabolicEscape
public import CFSG.Quasithin.Chapter15.Section01.CaseI.OrdinarySource.InnerPlacement
public import CFSG.Quasithin.Chapter15.Section01.CaseI.OrdinarySource.CentralizerComparison
public import CFSG.Quasithin.Chapter15.Section01.WreathFactor

/-!
# Initial reductions when the nonsolvable uniqueness family is empty

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), Section 15.1, pp. 1083--1104.

The terminal result of this section is Theorem 15.1.15: in a counterexample to
Theorem 15.1.3, cases (4), (6), and (7) of Lemma 15.1.7 are impossible. The proof
of Theorem 15.1.3 itself ends in Section 15.2.

The source reduction selects the actual ordering maximum and constructs
15.1.1(1)'s normalizer and qrc configuration, with the common-normal branch
excluded. The noncentral Thompson action supplies the original rank-two
setup or full orthogonal action. The centralizing branch has the Baumann
control of 15.1.9(1),(5),(7), complete chosen-module preparation, and the
Thompson conclusions of 15.1.13(3--4). Its exclusion remains to be proved.

The elementary-nine Case-I branch now constructs its literal outside component,
proves the centralizer odd core trivial, and derives component movement and
the local Sylow intersection. Its same-marker fixed and moved four-groups
are complementary in V. The original prime-to-three residual escapes MZ,
normalizes the component, and acts fully on the moved plane; every outside
two-perfect subgroup has centralizer index three there. The earlier
15.1.14(1) premise and later component/parabolic exclusions remain.
The triality row uses the genuine A.3.18 cubic residual argument, allowing
its outer automorphism group to contain an element of order three.
Failure of 15.1.14 now produces a moving minimal parabolic and a strictly
smaller H-star subgroup in the escape join; eliminating that nested
configuration remains necessary.

The literal Sylow centralizer has index two, stabilizes both planes, and
has centralizer index two on the fixed plane; every other Sylow element
exchanges them. In the ordinary component branch the original central
involutions act faithfully, the center is a two-group, and the original
intersection has characteristic two. Inner marked involutions give the
required centralizer containment, leaving the two actual alternating outer
actions as exceptions. Compatible parabolic recognition remains open.

For the symmetric-five wreath quotient in 15.2.4, the actual alternating-five
component is now extracted with characteristic two, escape from the chosen
maximal subgroup, and an index-two Sylow normalizer containing J(T). These
source facts require no additional quotient marking or chief-kernel premise.

The imports also supply the faithful-projection argument of Lemma 15.1.29:
centralizer control on nonidentity elements of `Z`, together with `L` outside
`M_c`, makes a projection of `Z` faithful if its discarded factors centralize
`L`. The quotient case analysis, component reductions, and natural-module
contradiction remain to be assembled before Theorem 15.1.15 can be stated here
as a proved result.
-/
