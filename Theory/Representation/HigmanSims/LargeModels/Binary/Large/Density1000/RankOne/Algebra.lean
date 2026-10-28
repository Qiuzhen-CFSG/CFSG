module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Alignments
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Words
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Products.AA
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Products.AB
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Products.BA
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Products.ABAB
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Products.CB
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Products.CBB
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Sums

/-!
# The packed degree-1000 operator is the sum of its four literal words

Six checked matrix products certify A²=1, AB, BA, (AB)², CB and CBB, where
C=(AB)²+BA. Three checked sums identify C, CBB+BA and D. The involution
identity simplifies the original four words to CBB+BA+AB. Every packed row
is connected to the original arrays by the shared binary decoder.

Source: R. A. Wilson et al., ATLAS HSG1-f2r1000B0 and the preserved witness
`Binary/source/density1000.json`. See `Algebra/source/README.md` for provenance,
reproduction and measurements. No relation for B is assumed or used.
-/

public section
open Thompson.BinaryMatrix
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
open _root_.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra
open _root_.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra.Tables
open RowArithmetic

/-- The original packed D is exactly the four published generator words. -/
theorem decoded_algebra_eq : decode 1000 Data.dRows = algebraMatrix := by
  have haa : generator false * generator false = 1 := by
    change decode 1000 D1000.aRows * decode 1000 D1000.aRows = 1
    rw [← a_matrix, aa_matrix, one_matrix]
  rw [literal_words_factor haa]
  change decode 1000 Data.dRows =
    ((decode 1000 D1000.aRows * decode 1000 D1000.bRows) *
      (decode 1000 D1000.aRows * decode 1000 D1000.bRows) +
      decode 1000 D1000.bRows * decode 1000 D1000.aRows) *
      decode 1000 D1000.bRows * decode 1000 D1000.bRows +
        decode 1000 D1000.bRows * decode 1000 D1000.aRows +
          decode 1000 D1000.aRows * decode 1000 D1000.bRows
  simp only [← a_matrix, ← b_matrix, ab_matrix, ba_matrix, abab_matrix,
    ← c_sum_matrix, cb_matrix, cbb_matrix, ← e_sum_matrix, ← d_sum_matrix, d_matrix]

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
