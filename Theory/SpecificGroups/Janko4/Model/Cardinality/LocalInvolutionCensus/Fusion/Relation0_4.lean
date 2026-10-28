module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Bridge
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.ProductsCase0_4

/-!
# Odd-product fusion witness 0_4

The evaluated square-one word has an odd product of exponent 43 with a
conjugate of the literal target. The dihedral argument constructs the
conjugacy inside `Janko4.Model`. See `source/README.md` for attribution.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation
open Janko4.GeneratorCertificates
open Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations (decoded_product eval_mul eval_inv)

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
open Case0_4

private theorem odd_power : decodeRows odd0_4Rows ^ 43 = (1 : BinaryMatrix) := by
  have h2 : decodeRows odd0_4RowsP2 = decodeRows odd0_4Rows ^ 2 := by
    rw [← decoded_product product_02, ← pow_two]
  have h4 : decodeRows odd0_4RowsP4 = decodeRows odd0_4Rows ^ 4 := by
    rw [← decoded_product product_03, h2, ← pow_add]
  have h5 : decodeRows odd0_4RowsP5 = decodeRows odd0_4Rows ^ 5 := by
    rw [← decoded_product product_04, h4, ← pow_succ]
  have h10 : decodeRows odd0_4RowsP10 = decodeRows odd0_4Rows ^ 10 := by
    rw [← decoded_product product_05, h5, ← pow_add]
  have h20 : decodeRows odd0_4RowsP20 = decodeRows odd0_4Rows ^ 20 := by
    rw [← decoded_product product_06, h10, ← pow_add]
  have h21 : decodeRows odd0_4RowsP21 = decodeRows odd0_4Rows ^ 21 := by
    rw [← decoded_product product_07, h20, ← pow_succ]
  have h42 : decodeRows odd0_4RowsP42 = decodeRows odd0_4Rows ^ 42 := by
    rw [← decoded_product product_08, h21, ← pow_add]
  have h := decoded_product product_09
  rw [h42, ← pow_succ, decode_packedOne] at h
  exact h

theorem fuse_0_4 {u : Model} (hu : toMatrix u = decodeRows w10Rows) : IsConj t u := by
  have hs : u ^ 2 = 1 := by
    apply toMatrix_injective
    rw [map_pow, map_one, hu, pow_two, decoded_product product_00, decode_packedOne]
  apply of_odd_product u t (Janko4.a) 43 hs target_sq (by decide)
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, hu]
  rw [eval_aztRows]
  rw [decoded_product product_01]
  exact odd_power

end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
