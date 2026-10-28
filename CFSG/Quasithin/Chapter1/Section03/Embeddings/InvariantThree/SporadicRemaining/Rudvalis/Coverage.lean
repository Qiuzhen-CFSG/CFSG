module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.CoverageReduction
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage

/-!
# Rudvalis odd-index maximal-subgroup coverage

Every odd-index maximal subgroup of the concrete Rudvalis model is
isomorphic to the preserved ATLAS max4 or max6, under the source pair input.
The checked two-normalizer generation calculation supplies its nontrivial
intrinsic two-core. The pair input supplies the trivial ambient two-core,
so maximality identifies the subgroup with the normalizer of its core's
ambient image. That image is two-radical, and the exhaustive radical-normalizer
calculation supplies an actual multiplicative equivalence to a candidate.

The final theorem discharges both local-analysis premises of the retained
conditional reduction. The candidate cardinality bounds and pair exclusion
remain with the parent assembly.

Source: Aschbacher--Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), citing [Asc86b]; GLS3 Table 5.3r.
-/

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining

/-- Assemble coverage from the two independent local-analysis obligations.
The final source assembly must discharge both premises. -/
public theorem rudvalis_oddIndexMaximalCover_of_twoCore_of_radicalCover
    {S : Sylow 2 Rudvalis.Model} {R : Subgroup Rudvalis.Model}
    (h : PairInput S R)
    (hcore : Rudvalis.SylowOvergroups.OddIndexMaximalTwoCore)
    (hlocal : Rudvalis.SylowOvergroups.OddIndexMaximalRadicalCover) :
    Rudvalis.SylowOvergroups.OddIndexMaximalCover :=
  Rudvalis.SylowOvergroups.oddIndexMaximalCover_of_twoCore_of_radicalCover
    h.twoCore hcore hlocal

/-- Every odd-index maximal subgroup is isomorphic to one of the two
concrete ATLAS candidates. The source pair input is the only hypothesis. -/
public theorem rudvalis_oddIndexMaximalCover
    {S : Sylow 2 Rudvalis.Model} {R : Subgroup Rudvalis.Model}
    (h : PairInput S R) : Rudvalis.SylowOvergroups.OddIndexMaximalCover :=
  rudvalis_oddIndexMaximalCover_of_twoCore_of_radicalCover h
    rudvalis_oddIndexMaximalTwoCore
    Rudvalis.SylowOvergroups.oddIndexMaximalRadicalCover

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining
