module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Bridge
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.ProductsCase1_8

/-!
# Odd-product fusion witness 1_8

The evaluated square-one word has an odd product of exponent 33 with a
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
open Case1_8

private theorem odd_power : decodeRows odd1_8Rows ^ 33 = (1 : BinaryMatrix) := by
  have h2 : decodeRows odd1_8RowsP2 = decodeRows odd1_8Rows ^ 2 := by
    rw [← decoded_product product_02, ← pow_two]
  have h4 : decodeRows odd1_8RowsP4 = decodeRows odd1_8Rows ^ 4 := by
    rw [← decoded_product product_03, h2, ← pow_add]
  have h8 : decodeRows odd1_8RowsP8 = decodeRows odd1_8Rows ^ 8 := by
    rw [← decoded_product product_04, h4, ← pow_add]
  have h16 : decodeRows odd1_8RowsP16 = decodeRows odd1_8Rows ^ 16 := by
    rw [← decoded_product product_05, h8, ← pow_add]
  have h32 : decodeRows odd1_8RowsP32 = decodeRows odd1_8Rows ^ 32 := by
    rw [← decoded_product product_06, h16, ← pow_add]
  have h := decoded_product product_07
  rw [h32, ← pow_succ, decode_packedOne] at h
  exact h

theorem fuse_1_8 {u : Model} (hu : toMatrix u = decodeRows translate8Rows) : IsConj t u := by
  have hs : u ^ 2 = 1 := by
    apply toMatrix_injective
    rw [map_pow, map_one, hu, pow_two, decoded_product product_00, decode_packedOne]
  apply of_odd_product u t (1) 33 hs target_sq (by decide)
  simp only [one_mul, inv_one, mul_one]
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, hu]
  rw [eval_target]
  rw [decoded_product product_01]
  exact odd_power

end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
