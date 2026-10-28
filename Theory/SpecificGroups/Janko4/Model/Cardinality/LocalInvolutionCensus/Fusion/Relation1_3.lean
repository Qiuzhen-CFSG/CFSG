module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Bridge
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.ProductsCase1_3

/-!
# Odd-product fusion witness 1_3

The evaluated square-one word has an odd product of exponent 31 with a
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
open Case1_3

private theorem odd_power : decodeRows odd1_3Rows ^ 31 = (1 : BinaryMatrix) := by
  have h2 : decodeRows odd1_3RowsP2 = decodeRows odd1_3Rows ^ 2 := by
    rw [← decoded_product product_02, ← pow_two]
  have h3 : decodeRows odd1_3RowsP3 = decodeRows odd1_3Rows ^ 3 := by
    rw [← decoded_product product_03, h2, ← pow_succ]
  have h6 : decodeRows odd1_3RowsP6 = decodeRows odd1_3Rows ^ 6 := by
    rw [← decoded_product product_04, h3, ← pow_add]
  have h7 : decodeRows odd1_3RowsP7 = decodeRows odd1_3Rows ^ 7 := by
    rw [← decoded_product product_05, h6, ← pow_succ]
  have h14 : decodeRows odd1_3RowsP14 = decodeRows odd1_3Rows ^ 14 := by
    rw [← decoded_product product_06, h7, ← pow_add]
  have h15 : decodeRows odd1_3RowsP15 = decodeRows odd1_3Rows ^ 15 := by
    rw [← decoded_product product_07, h14, ← pow_succ]
  have h30 : decodeRows odd1_3RowsP30 = decodeRows odd1_3Rows ^ 30 := by
    rw [← decoded_product product_08, h15, ← pow_add]
  have h := decoded_product product_09
  rw [h30, ← pow_succ, decode_packedOne] at h
  exact h

theorem fuse_1_3 {u : Model} (hu : toMatrix u = decodeRows translate3Rows) : IsConj t u := by
  have hs : u ^ 2 = 1 := by
    apply toMatrix_injective
    rw [map_pow, map_one, hu, pow_two, decoded_product product_00, decode_packedOne]
  apply of_odd_product u t (1) 31 hs target_sq (by decide)
  simp only [one_mul, inv_one, mul_one]
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, hu]
  rw [eval_target]
  rw [decoded_product product_01]
  exact odd_power

end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
