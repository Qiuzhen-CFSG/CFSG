module

public import CFSG.Quasithin.Chapter12.Section08.Setup.Consumers
public import CFSG.Quasithin.Chapter12.Section08.Setup.RankTwoBase
public import CFSG.Quasithin.Chapter12.Section08.Setup.Completion

/-!
# Source construction for the Section 12.8 setup

Both original alternatives construct the unique T-invariant subspace in each
dimension, a complete invariant flag, its nonidentity point generator, and a
conjugator in the omitted-point parabolic outside the point normalizer.
`HigherRankHypothesis.lemma1283` and `RankTwoHypothesis.lemma1283` prove all
four clauses, with the literal centralizer quotient and action images: L gives
the full action in higher rank, while LT gives it in dimension two and the
L-image has order three. The original n=5 solvable-residual convention is retained.

The two `exists_localKernel_center_product` applications supply constructed
flags and conjugators. `HigherRankHypothesis.normal_L1_geometry_of_source`
supplies the subspace and transporter inputs of NormalL1. SourceGeometry
applications discharge their normalization, transitivity and escape premises.
The original nonabelian, center-containment and relative-normality antecedents
of those later source results remain explicit.

The higher-rank family is conditional on the universal structural implication
12.2.2(3), uniqueness 1.2.7 and the full alternatives of 12.2.13, using the single
shared Section 12.2 specification. The Section 12.8 source owner must discharge
these three earlier implications and instantiate the full known-simple class.
The dimension-two family uses only the original `RankTwoHypothesis`.

Source: Aschbacher–Smith, Hypothesis 12.8.1, Notation 12.8.2 and Lemma 12.8.3,
combined manuscript of 1 March 2004, printed pp.849–850.
-/
