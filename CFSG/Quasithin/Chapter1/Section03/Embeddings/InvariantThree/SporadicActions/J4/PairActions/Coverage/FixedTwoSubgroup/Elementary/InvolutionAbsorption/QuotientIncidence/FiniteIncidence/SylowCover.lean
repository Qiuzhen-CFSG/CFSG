module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.SylowCover.SubgroupBound
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.SylowCover.Orbit

/-!
# The fixed Sylow subgroup and its exhaustive double-coset cover

The four published words generate a group of order 256. The 110 published
words cover the entire certified matrix quotient by double cosets of this
subgroup. The proof uses a checked 256-point subgroup orbit and 10395 distinct
images of a subgroup-fixed unordered row pair. The proved ambient order
2661120 forces equality in the resulting coset count and hence coverage.

All word actions, orbit edges, roots, and distinctness checks are supplied by
the imported kernel-checked certificates. Source context and reproducible
witness generation are documented in SylowCover/source/README.md.
-/

public section
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence

private theorem sylow_cover_certificates : Nat.card baseSubgroup = 256 ∧
    Theory.GroupTheory.SubgroupEnumeration.DoubleCosetCover baseSubgroup representative :=
  SylowCover.count_and_cover_of_forest SylowCover.SubgroupBound.lower_bound
    SylowCover.base_fixes (fun i => SylowCover.point (SylowCover.CoverData.codes i))
    SylowCover.Orbit.distinct SylowCover.Orbit.reachable

/-- The fixed four published words generate a subgroup of order 256. -/
theorem baseSubgroup_card : Nat.card baseSubgroup = 256 :=
  sylow_cover_certificates.1

/-- Every matrix factors through one of the 110 fixed double-coset representatives. -/
theorem representative_doubleCoset_cover :
    Theory.GroupTheory.SubgroupEnumeration.DoubleCosetCover baseSubgroup representative :=
  sylow_cover_certificates.2

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence
