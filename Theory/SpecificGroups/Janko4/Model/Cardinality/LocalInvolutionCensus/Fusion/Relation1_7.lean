module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Bridge
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.ProductsCase1_7

/-!
# Odd-product fusion witness 1_7

The evaluated square-one word has an odd product of exponent 11 with a
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
open Case1_7

private theorem odd_power : decodeRows odd1_7Rows ^ 11 = (1 : BinaryMatrix) := by
  have h2 : decodeRows odd1_7RowsP2 = decodeRows odd1_7Rows ^ 2 := by
    rw [← decoded_product product_02, ← pow_two]
  have h4 : decodeRows odd1_7RowsP4 = decodeRows odd1_7Rows ^ 4 := by
    rw [← decoded_product product_03, h2, ← pow_add]
  have h5 : decodeRows odd1_7RowsP5 = decodeRows odd1_7Rows ^ 5 := by
    rw [← decoded_product product_04, h4, ← pow_succ]
  have h10 : decodeRows odd1_7RowsP10 = decodeRows odd1_7Rows ^ 10 := by
    rw [← decoded_product product_05, h5, ← pow_add]
  have h := decoded_product product_06
  rw [h10, ← pow_succ, decode_packedOne] at h
  exact h

theorem fuse_1_7 {u : Model} (hu : toMatrix u = decodeRows translate7Rows) : IsConj Janko4.a u := by
  have hs : u ^ 2 = 1 := by
    apply toMatrix_injective
    rw [map_pow, map_one, hu, pow_two, decoded_product product_00, decode_packedOne]
  apply of_odd_product u Janko4.a (1) 11 hs Janko4.a_pow_two (by decide)
  simp only [one_mul, inv_one, mul_one]
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, hu]
  change (decodeRows translate7Rows * decodeRows aRows) ^ 11 = 1
  rw [decoded_product product_01]
  exact odd_power

end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
