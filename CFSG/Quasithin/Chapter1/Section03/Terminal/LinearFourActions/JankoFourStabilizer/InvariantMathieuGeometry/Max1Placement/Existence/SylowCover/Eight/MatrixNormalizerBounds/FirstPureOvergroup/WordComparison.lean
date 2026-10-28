module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup.KernelWords
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup.WordComparison.Products198
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.MatrixRealization.WordEvaluation

/-!
# The first pure PC generators in the actual max1 kernel coordinates

The certified PC-word evaluations and the fifteen additional kernel-basis
products give the same matrices in the original ATLAS basis. Faithfulness
of `Janko4.toMatrix` therefore identifies the three actual model elements
with masks 1011, 1387 and 198. Applying `KernelWords` then identifies `U 0`,
transports its full subgroup trace, and proves that the marked plane witness
does not normalize it.

Source: the literal word and mask conventions in
`SylowNormalEights/source/README.md` and `KernelOrbits.Coordinates`;
ATLAS attribution is retained in `Model/Data.lean`. These are the word
comparisons used in the A.3.12 route (Aschbacher–Smith, printed pp.47–48).
The independent trace-image identity remains with the overgroup assembly.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Subgroup Janko4 Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Simplicity.Max1Fusion.KernelOrbits
open Janko4.LocalStructure.SylowNormalEights.MatrixWords
open Janko4.LocalStructure.SylowNormalEights.MatrixRealization
open FirstPureWordComparison

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localKernelSeed basis

private theorem mask_basis (i : Fin 11) :
    toMatrix (kernelMask (2 ^ i.val)) = decodeRows (basisRows i) := by
  change representation matrixA_mul_self matrixB_pow_four
    (maskValue matrixA_mul_self matrixB_pow_four (2 ^ i.val)) = _
  rw [maskValue_basis]
  exact representation_basis matrixA_mul_self matrixB_pow_four i

private theorem mask_mul_eval {m n : ℕ} {a b c : ℕ → ℕ}
    (hm : toMatrix (kernelMask m) = rowsMatrix a)
    (hn : toMatrix (kernelMask n) = rowsMatrix b)
    (hp : rowsMatrix a * rowsMatrix b = rowsMatrix c) :
    toMatrix (kernelMask (Nat.xor m n)) = rowsMatrix c := by
  have hx : kernelMask (Nat.xor m n) = kernelMask m * kernelMask n := by
    simp only [kernelMask, maskValue_xor, map_mul]
  rw [hx, map_mul, hm, hn]
  exact hp

private theorem mask1_eval : toMatrix (kernelMask 1) = rowsMatrix r3 :=
  (mask_basis 0).trans decoded_e0Rows.symm

private theorem mask2_eval : toMatrix (kernelMask 2) = rowsMatrix r4 :=
  (mask_basis 1).trans decoded_e1Rows.symm

private theorem mask4_eval : toMatrix (kernelMask 4) = rowsMatrix r5 :=
  (mask_basis 2).trans decoded_e2Rows.symm

private theorem mask8_eval : toMatrix (kernelMask 8) = rowsMatrix r6 :=
  (mask_basis 3).trans decoded_e3Rows.symm

private theorem mask16_eval : toMatrix (kernelMask 16) = rowsMatrix r7 :=
  (mask_basis 4).trans decoded_e4Rows.symm

private theorem mask32_eval : toMatrix (kernelMask 32) = rowsMatrix r8 :=
  (mask_basis 5).trans decoded_e5Rows.symm

private theorem mask64_eval : toMatrix (kernelMask 64) = rowsMatrix r9 :=
  (mask_basis 6).trans decoded_e6Rows.symm

private theorem mask128_eval : toMatrix (kernelMask 128) = rowsMatrix r10 :=
  (mask_basis 7).trans decoded_e7Rows.symm

private theorem mask256_eval : toMatrix (kernelMask 256) = rowsMatrix r11 :=
  (mask_basis 8).trans decoded_e8Rows.symm

private theorem mask512_eval : toMatrix (kernelMask 512) = rowsMatrix r12 :=
  (mask_basis 9).trans decoded_e9Rows.symm

private theorem mask1024_eval : toMatrix (kernelMask 1024) = rowsMatrix r13 :=
  (mask_basis 10).trans decoded_e10Rows.symm

private theorem mask3_eval : toMatrix (kernelMask 3) = rowsMatrix maskRows3 :=
  mask_mul_eval (m := 1) (n := 2) mask1_eval mask2_eval product_mask3

private theorem mask19_eval : toMatrix (kernelMask 19) = rowsMatrix maskRows19 :=
  mask_mul_eval (m := 3) (n := 16) mask3_eval mask16_eval product_mask19

private theorem mask51_eval : toMatrix (kernelMask 51) = rowsMatrix maskRows51 :=
  mask_mul_eval (m := 19) (n := 32) mask19_eval mask32_eval product_mask51

private theorem mask115_eval : toMatrix (kernelMask 115) = rowsMatrix maskRows115 :=
  mask_mul_eval (m := 51) (n := 64) mask51_eval mask64_eval product_mask115

private theorem mask243_eval : toMatrix (kernelMask 243) = rowsMatrix maskRows243 :=
  mask_mul_eval (m := 115) (n := 128) mask115_eval mask128_eval product_mask243

private theorem mask499_eval : toMatrix (kernelMask 499) = rowsMatrix maskRows499 :=
  mask_mul_eval (m := 243) (n := 256) mask243_eval mask256_eval product_mask499

private theorem mask1011_eval : toMatrix (kernelMask 1011) = rowsMatrix r193 :=
  mask_mul_eval (m := 499) (n := 512) mask499_eval mask512_eval product_mask1011

private theorem mask11_eval : toMatrix (kernelMask 11) = rowsMatrix maskRows11 :=
  mask_mul_eval (m := 3) (n := 8) mask3_eval mask8_eval product_mask11

private theorem mask43_eval : toMatrix (kernelMask 43) = rowsMatrix maskRows43 :=
  mask_mul_eval (m := 11) (n := 32) mask11_eval mask32_eval product_mask43

private theorem mask107_eval : toMatrix (kernelMask 107) = rowsMatrix r372 :=
  mask_mul_eval (m := 43) (n := 64) mask43_eval mask64_eval product_mask107

private theorem mask363_eval : toMatrix (kernelMask 363) = rowsMatrix maskRows363 :=
  mask_mul_eval (m := 107) (n := 256) mask107_eval mask256_eval product_mask363

private theorem mask1387_eval : toMatrix (kernelMask 1387) = rowsMatrix r197 :=
  mask_mul_eval (m := 363) (n := 1024) mask363_eval mask1024_eval product_mask1387

private theorem mask6_eval : toMatrix (kernelMask 6) = rowsMatrix maskRows6 :=
  mask_mul_eval (m := 2) (n := 4) mask2_eval mask4_eval product_mask6

private theorem mask70_eval : toMatrix (kernelMask 70) = rowsMatrix maskRows70 :=
  mask_mul_eval (m := 6) (n := 64) mask6_eval mask64_eval product_mask70

private theorem mask198_eval : toMatrix (kernelMask 198) = rowsMatrix r166 :=
  mask_mul_eval (m := 70) (n := 128) mask70_eval mask128_eval product_mask198

/-- Literal PC generator 18 (`word79`) has the specified actual kernel coordinates. -/
theorem pcGenerator18_eq_kernelMask : (pcGenerator 18 : Model) = kernelMask 1011 := by
  apply toMatrix_injective
  exact pc18_eval.trans mask1011_eval.symm

/-- Literal PC generator 19 (`word85`) has the specified actual kernel coordinates. -/
theorem pcGenerator19_eq_kernelMask : (pcGenerator 19 : Model) = kernelMask 1387 := by
  apply toMatrix_injective
  exact pc19_eval.trans mask1387_eval.symm

/-- Literal PC generator 20 (`word38`) has the specified actual kernel coordinates. -/
theorem pcGenerator20_eq_kernelMask : (pcGenerator 20 : Model) = kernelMask 198 := by
  apply toMatrix_injective
  exact pc20_eval.trans mask198_eval.symm

/-- The actual first pure eight is precisely the subgroup of the eight kernel masks. -/
theorem firstPure_eq_maskEight : U 0 = firstPureMaskEight :=
  firstPure_eq_maskEight_of_word_equalities
    pcGenerator18_eq_kernelMask pcGenerator19_eq_kernelMask pcGenerator20_eq_kernelMask

/-- The complete subgroup trace is the trace over the explicit kernel masks. -/
theorem firstPureTrace_eq_maskTrace : firstPureTrace = firstPureMaskTrace :=
  firstPureTrace_eq_maskTrace_of_word_equalities
    pcGenerator18_eq_kernelMask pcGenerator19_eq_kernelMask pcGenerator20_eq_kernelMask

/-- The marked plane witness does not normalize the actual first pure eight. -/
theorem firstPureStrictWitness_not_normalizer :
    firstPureStrictWitness ∉ normalizer (U 0 : Set Model) :=
  firstPureStrictWitness_not_normalizer_of_word_equalities
    pcGenerator18_eq_kernelMask pcGenerator19_eq_kernelMask pcGenerator20_eq_kernelMask

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
