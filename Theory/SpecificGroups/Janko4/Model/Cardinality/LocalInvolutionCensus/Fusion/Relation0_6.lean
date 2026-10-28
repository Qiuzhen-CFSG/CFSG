module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Bridge
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Evaluation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.ProductsCase0_6

/-!
# Odd-product fusion witness 0_6

The evaluated square-one word has an odd product of exponent 37 with a
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
open Case0_6

private theorem odd_power : decodeRows odd0_6Rows ^ 37 = (1 : BinaryMatrix) := by
  have h2 : decodeRows odd0_6RowsP2 = decodeRows odd0_6Rows ^ 2 := by
    rw [← decoded_product product_02, ← pow_two]
  have h4 : decodeRows odd0_6RowsP4 = decodeRows odd0_6Rows ^ 4 := by
    rw [← decoded_product product_03, h2, ← pow_add]
  have h8 : decodeRows odd0_6RowsP8 = decodeRows odd0_6Rows ^ 8 := by
    rw [← decoded_product product_04, h4, ← pow_add]
  have h9 : decodeRows odd0_6RowsP9 = decodeRows odd0_6Rows ^ 9 := by
    rw [← decoded_product product_05, h8, ← pow_succ]
  have h18 : decodeRows odd0_6RowsP18 = decodeRows odd0_6Rows ^ 18 := by
    rw [← decoded_product product_06, h9, ← pow_add]
  have h36 : decodeRows odd0_6RowsP36 = decodeRows odd0_6Rows ^ 36 := by
    rw [← decoded_product product_07, h18, ← pow_add]
  have h := decoded_product product_08
  rw [h36, ← pow_succ, decode_packedOne] at h
  exact h

theorem fuse_0_6 {u : Model} (hu : toMatrix u = decodeRows rep6Rows) : IsConj t u := by
  have hs : u ^ 2 = 1 := by
    apply toMatrix_injective
    rw [map_pow, map_one, hu, pow_two, decoded_product product_00, decode_packedOne]
  apply of_odd_product u t (1) 37 hs target_sq (by decide)
  simp only [one_mul, inv_one, mul_one]
  apply toMatrix_injective
  rw [map_pow, map_one, map_mul, hu]
  rw [eval_target]
  rw [decoded_product product_01]
  exact odd_power

end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
