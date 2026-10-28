module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.WordEvaluations
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Products3
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Products4
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Products5
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank3
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank4
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank5
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank6
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank7
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank8
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank9
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank10
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank11
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank12
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank13
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank14
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Rank15

/-!
# Certified ranks and involutions for the max2 fiber representatives

Each representative is evaluated from its prescribed increasing-bit kernel
word and original ATLAS source lift. Full packed matrix products also evaluate
its translate by `sourceSeed ^ 2` and certify each required square. Two row
expansions and an identity pivot minor prove each displacement rank in the
mathematical sense of `Matrix.rank`.

These are representative facts only. The separate orbit forest and local order
bound are inputs to the parent census assembly. The source motivation is
Aschbacher--Smith, `refs/quasithin.pdf`, printed pp.64--65, A.6.1--4.
The matrices are those of the unchanged ATLAS J4G1-max2W1 program, credited to
R. A. Wilson, S. J. Nickerson and J. N. Bray. See the source README here and
Janko4.Model.Data for provenance. All finite identities use kernel reduction.
-/

set_option backward.isDefEq.respectTransparency true

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound Janko4.GeneratorCertificates RepresentativeMatrices

private theorem rank0 : (decodeRows r0 - 1).rank = 0 := by
  rw [rows0, decode_packedOne, sub_self, Matrix.rank_zero]

private theorem pair_certificate (k : Fin 11) {rs ss : Vector ℕ 112} {a b : ℕ}
    (hg : toMatrix ((sourceRepresentative k : sourceSubgroup) : Model) = decodeRows rs)
    (hc : packedMul rs r1 = ss)
    (ha : (decodeRows rs - 1).rank = a) (hb : (decodeRows ss - 1).rank = b) :
    sourceRankPair (sourceRepresentative k) = (a, b) := by
  have ht : toMatrix (((sourceRepresentative k) * sourceSeed^2 : sourceSubgroup) : Model) =
      decodeRows ss := by
    change toMatrix ((sourceRepresentative k : Model) * ((sourceSeed^2 : sourceSubgroup) : Model)) = _
    rw [map_mul, hg, eval_marked, ← decode_packedMul, hc]
  change ((toMatrix (sourceRepresentative k : Model) - 1).rank,
    (toMatrix (((sourceRepresentative k) * sourceSeed^2 : sourceSubgroup) : Model) - 1).rank) = _
  rw [hg, ht, ha, hb]

/-- The eleven displacement rank pairs, including the marked translate. -/
theorem sourceRepresentative_rankPair (k : Fin 11) :
    sourceRankPair (sourceRepresentative k) = expectedRanks k := by
  fin_cases k
  · exact pair_certificate 0 eval_representative0 product_translate0 rank0 rank1
  · exact pair_certificate 1 eval_representative1 product_translate1 rank1 rank0
  · exact pair_certificate 2 eval_representative2 product_translate2 rank2 rank3
  · exact pair_certificate 3 eval_representative3 product_translate4 rank4 rank5
  · exact pair_certificate 4 eval_representative4 product_translate6 rank6 rank7
  · exact pair_certificate 5 eval_representative5 product_translate8 rank8 rank9
  · exact pair_certificate 6 eval_representative6 product_translate9 rank9 rank8
  · exact pair_certificate 7 eval_representative7 product_translate10 rank10 rank11
  · exact pair_certificate 8 eval_representative8 product_translate12 rank12 rank13
  · exact pair_certificate 9 eval_representative9 product_translate14 rank14 rank15
  · exact pair_certificate 10 eval_representative10 product_translate15 rank15 rank14

private theorem square_certificate (u : sourceSubgroup) {rs : Vector ℕ 112}
    (hu : toMatrix (u : Model) = decodeRows rs) (hc : packedMul rs rs = packedOne) :
    u^2 = 1 := by
  apply Subtype.ext
  apply toMatrix_injective
  change toMatrix ((u : Model)^2) = toMatrix 1
  rw [pow_two, map_mul, hu, ← decode_packedMul, hc, decode_packedOne, map_one]

/-- Each of the seven representatives used by the census squares to one. -/
theorem sourceRepresentative_square_one (k : Fin 11) (hk : Required k) :
    (sourceRepresentative k)^2 = 1 := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact square_certificate _ eval_representative2 product_square2
  · exact square_certificate _ eval_representative3 product_square3
  · exact square_certificate _ eval_representative4 product_square4
  · exact square_certificate _ eval_representative6 product_square6
  · exact square_certificate _ eval_representative7 product_square7
  · exact square_certificate _ eval_representative8 product_square8
  · exact square_certificate _ eval_representative9 product_square9

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus
