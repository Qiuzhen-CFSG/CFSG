module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.Products.Batch9
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.Words

/-!
# The matrix of the actual ambient word

Checked products evaluate each intermediate word in the faithful representation.
No presentation relations, group order or normalizer bound enters the calculation.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
open Janko4 Janko4.GeneratorCertificates

private theorem matrix_a : toMatrix a = decodeRows aRows := rfl
private theorem matrix_b : toMatrix b = decodeRows bRows := rfl

theorem matrix_mask1 : toMatrix (kernelMask 1) = decodeRows Janko4.Cardinality.KernelCount.e0Rows := by
  change toMatrix (kernelMask (2 ^ (0 : Fin 11).val)) = _
  rw [kernelMask_basis]
  exact Janko4.Cardinality.KernelCount.representation_basis matrixA_mul_self matrixB_pow_four (0 : Fin 11)

theorem matrix_mask2 : toMatrix (kernelMask 2) = decodeRows Janko4.Cardinality.KernelCount.e1Rows := by
  change toMatrix (kernelMask (2 ^ (1 : Fin 11).val)) = _
  rw [kernelMask_basis]
  exact Janko4.Cardinality.KernelCount.representation_basis matrixA_mul_self matrixB_pow_four (1 : Fin 11)

theorem matrix_mask8 : toMatrix (kernelMask 8) = decodeRows Janko4.Cardinality.KernelCount.e3Rows := by
  change toMatrix (kernelMask (2 ^ (3 : Fin 11).val)) = _
  rw [kernelMask_basis]
  exact Janko4.Cardinality.KernelCount.representation_basis matrixA_mul_self matrixB_pow_four (3 : Fin 11)

theorem matrix_mask16 : toMatrix (kernelMask 16) = decodeRows Janko4.Cardinality.KernelCount.e4Rows := by
  change toMatrix (kernelMask (2 ^ (4 : Fin 11).val)) = _
  rw [kernelMask_basis]
  exact Janko4.Cardinality.KernelCount.representation_basis matrixA_mul_self matrixB_pow_four (4 : Fin 11)

theorem matrix_mask32 : toMatrix (kernelMask 32) = decodeRows Janko4.Cardinality.KernelCount.e5Rows := by
  change toMatrix (kernelMask (2 ^ (5 : Fin 11).val)) = _
  rw [kernelMask_basis]
  exact Janko4.Cardinality.KernelCount.representation_basis matrixA_mul_self matrixB_pow_four (5 : Fin 11)

theorem matrix_mask512 : toMatrix (kernelMask 512) = decodeRows Janko4.Cardinality.KernelCount.e9Rows := by
  change toMatrix (kernelMask (2 ^ (9 : Fin 11).val)) = _
  rw [kernelMask_basis]
  exact Janko4.Cardinality.KernelCount.representation_basis matrixA_mul_self matrixB_pow_four (9 : Fin 11)

theorem matrix_mask544 : toMatrix (kernelMask 544) = decodeRows mask544Rows := by
  rw [show kernelMask 544 = kernelMask 32 * kernelMask 512 from kernelMask_xor 32 512]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask32 matrix_mask512 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask544)

theorem matrix_mask560 : toMatrix (kernelMask 560) = decodeRows mask560Rows := by
  rw [show kernelMask 560 = kernelMask 16 * kernelMask 544 from kernelMask_xor 16 544]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask16 matrix_mask544 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask560)

theorem matrix_mask568 : toMatrix (kernelMask 568) = decodeRows mask568Rows := by
  rw [show kernelMask 568 = kernelMask 8 * kernelMask 560 from kernelMask_xor 8 560]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask8 matrix_mask560 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask568)

theorem matrix_mask570 : toMatrix (kernelMask 570) = decodeRows mask570Rows := by
  rw [show kernelMask 570 = kernelMask 2 * kernelMask 568 from kernelMask_xor 2 568]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask2 matrix_mask568 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask570)

theorem matrix_mask571 : toMatrix (kernelMask 571) = decodeRows mask571Rows := by
  rw [show kernelMask 571 = kernelMask 1 * kernelMask 570 from kernelMask_xor 1 570]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask1 matrix_mask570 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask571)

theorem matrix_mask64 : toMatrix (kernelMask 64) = decodeRows Janko4.Cardinality.KernelCount.e6Rows := by
  change toMatrix (kernelMask (2 ^ (6 : Fin 11).val)) = _
  rw [kernelMask_basis]
  exact Janko4.Cardinality.KernelCount.representation_basis matrixA_mul_self matrixB_pow_four (6 : Fin 11)

theorem matrix_mask256 : toMatrix (kernelMask 256) = decodeRows Janko4.Cardinality.KernelCount.e8Rows := by
  change toMatrix (kernelMask (2 ^ (8 : Fin 11).val)) = _
  rw [kernelMask_basis]
  exact Janko4.Cardinality.KernelCount.representation_basis matrixA_mul_self matrixB_pow_four (8 : Fin 11)

theorem matrix_mask1024 : toMatrix (kernelMask 1024) = decodeRows Janko4.Cardinality.KernelCount.e10Rows := by
  change toMatrix (kernelMask (2 ^ (10 : Fin 11).val)) = _
  rw [kernelMask_basis]
  exact Janko4.Cardinality.KernelCount.representation_basis matrixA_mul_self matrixB_pow_four (10 : Fin 11)

theorem matrix_mask1280 : toMatrix (kernelMask 1280) = decodeRows mask1280Rows := by
  rw [show kernelMask 1280 = kernelMask 256 * kernelMask 1024 from kernelMask_xor 256 1024]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask256 matrix_mask1024 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1280)

theorem matrix_mask1344 : toMatrix (kernelMask 1344) = decodeRows mask1344Rows := by
  rw [show kernelMask 1344 = kernelMask 64 * kernelMask 1280 from kernelMask_xor 64 1280]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask64 matrix_mask1280 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1344)

theorem matrix_mask1376 : toMatrix (kernelMask 1376) = decodeRows mask1376Rows := by
  rw [show kernelMask 1376 = kernelMask 32 * kernelMask 1344 from kernelMask_xor 32 1344]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask32 matrix_mask1344 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1376)

theorem matrix_mask1384 : toMatrix (kernelMask 1384) = decodeRows mask1384Rows := by
  rw [show kernelMask 1384 = kernelMask 8 * kernelMask 1376 from kernelMask_xor 8 1376]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask8 matrix_mask1376 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1384)

theorem matrix_mask1386 : toMatrix (kernelMask 1386) = decodeRows mask1386Rows := by
  rw [show kernelMask 1386 = kernelMask 2 * kernelMask 1384 from kernelMask_xor 2 1384]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask2 matrix_mask1384 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1386)

theorem matrix_mask1387 : toMatrix (kernelMask 1387) = decodeRows mask1387Rows := by
  rw [show kernelMask 1387 = kernelMask 1 * kernelMask 1386 from kernelMask_xor 1 1386]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask1 matrix_mask1386 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1387)

theorem matrix_mask4 : toMatrix (kernelMask 4) = decodeRows Janko4.Cardinality.KernelCount.e2Rows := by
  change toMatrix (kernelMask (2 ^ (2 : Fin 11).val)) = _
  rw [kernelMask_basis]
  exact Janko4.Cardinality.KernelCount.representation_basis matrixA_mul_self matrixB_pow_four (2 : Fin 11)

theorem matrix_mask128 : toMatrix (kernelMask 128) = decodeRows Janko4.Cardinality.KernelCount.e7Rows := by
  change toMatrix (kernelMask (2 ^ (7 : Fin 11).val)) = _
  rw [kernelMask_basis]
  exact Janko4.Cardinality.KernelCount.representation_basis matrixA_mul_self matrixB_pow_four (7 : Fin 11)

theorem matrix_mask192 : toMatrix (kernelMask 192) = decodeRows mask192Rows := by
  rw [show kernelMask 192 = kernelMask 64 * kernelMask 128 from kernelMask_xor 64 128]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask64 matrix_mask128 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask192)

theorem matrix_mask196 : toMatrix (kernelMask 196) = decodeRows mask196Rows := by
  rw [show kernelMask 196 = kernelMask 4 * kernelMask 192 from kernelMask_xor 4 192]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask4 matrix_mask192 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask196)

theorem matrix_mask198 : toMatrix (kernelMask 198) = decodeRows mask198Rows := by
  rw [show kernelMask 198 = kernelMask 2 * kernelMask 196 from kernelMask_xor 2 196]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask2 matrix_mask196 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask198)

theorem matrix_mask1408 : toMatrix (kernelMask 1408) = decodeRows mask1408Rows := by
  rw [show kernelMask 1408 = kernelMask 128 * kernelMask 1280 from kernelMask_xor 128 1280]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask128 matrix_mask1280 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1408)

theorem matrix_mask1440 : toMatrix (kernelMask 1440) = decodeRows mask1440Rows := by
  rw [show kernelMask 1440 = kernelMask 32 * kernelMask 1408 from kernelMask_xor 32 1408]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask32 matrix_mask1408 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1440)

theorem matrix_mask1448 : toMatrix (kernelMask 1448) = decodeRows mask1448Rows := by
  rw [show kernelMask 1448 = kernelMask 8 * kernelMask 1440 from kernelMask_xor 8 1440]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask8 matrix_mask1440 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1448)

theorem matrix_mask1452 : toMatrix (kernelMask 1452) = decodeRows mask1452Rows := by
  rw [show kernelMask 1452 = kernelMask 4 * kernelMask 1448 from kernelMask_xor 4 1448]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask4 matrix_mask1448 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1452)

theorem matrix_mask1453 : toMatrix (kernelMask 1453) = decodeRows mask1453Rows := by
  rw [show kernelMask 1453 = kernelMask 1 * kernelMask 1452 from kernelMask_xor 1 1452]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask1 matrix_mask1452 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1453)

theorem matrix_mask1536 : toMatrix (kernelMask 1536) = decodeRows mask1536Rows := by
  rw [show kernelMask 1536 = kernelMask 512 * kernelMask 1024 from kernelMask_xor 512 1024]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask512 matrix_mask1024 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1536)

theorem matrix_mask1792 : toMatrix (kernelMask 1792) = decodeRows mask1792Rows := by
  rw [show kernelMask 1792 = kernelMask 256 * kernelMask 1536 from kernelMask_xor 256 1536]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask256 matrix_mask1536 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1792)

theorem matrix_mask1920 : toMatrix (kernelMask 1920) = decodeRows mask1920Rows := by
  rw [show kernelMask 1920 = kernelMask 128 * kernelMask 1792 from kernelMask_xor 128 1792]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask128 matrix_mask1792 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1920)

theorem matrix_mask1936 : toMatrix (kernelMask 1936) = decodeRows mask1936Rows := by
  rw [show kernelMask 1936 = kernelMask 16 * kernelMask 1920 from kernelMask_xor 16 1920]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask16 matrix_mask1920 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1936)

theorem matrix_mask1940 : toMatrix (kernelMask 1940) = decodeRows mask1940Rows := by
  rw [show kernelMask 1940 = kernelMask 4 * kernelMask 1936 from kernelMask_xor 4 1936]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask4 matrix_mask1936 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1940)

theorem matrix_mask1942 : toMatrix (kernelMask 1942) = decodeRows mask1942Rows := by
  rw [show kernelMask 1942 = kernelMask 2 * kernelMask 1940 from kernelMask_xor 2 1940]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask2 matrix_mask1940 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1942)

theorem matrix_mask1856 : toMatrix (kernelMask 1856) = decodeRows mask1856Rows := by
  rw [show kernelMask 1856 = kernelMask 64 * kernelMask 1792 from kernelMask_xor 64 1792]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask64 matrix_mask1792 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1856)

theorem matrix_mask1872 : toMatrix (kernelMask 1872) = decodeRows mask1872Rows := by
  rw [show kernelMask 1872 = kernelMask 16 * kernelMask 1856 from kernelMask_xor 16 1856]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask16 matrix_mask1856 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask1872)

theorem matrix_mask640 : toMatrix (kernelMask 640) = decodeRows mask640Rows := by
  rw [show kernelMask 640 = kernelMask 128 * kernelMask 512 from kernelMask_xor 128 512]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask128 matrix_mask512 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask640)

theorem matrix_mask704 : toMatrix (kernelMask 704) = decodeRows mask704Rows := by
  rw [show kernelMask 704 = kernelMask 64 * kernelMask 640 from kernelMask_xor 64 640]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask64 matrix_mask640 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask704)

theorem matrix_mask736 : toMatrix (kernelMask 736) = decodeRows mask736Rows := by
  rw [show kernelMask 736 = kernelMask 32 * kernelMask 704 from kernelMask_xor 32 704]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask32 matrix_mask704 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask736)

theorem matrix_mask752 : toMatrix (kernelMask 752) = decodeRows mask752Rows := by
  rw [show kernelMask 752 = kernelMask 16 * kernelMask 736 from kernelMask_xor 16 736]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask16 matrix_mask736 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask752)

theorem matrix_mask760 : toMatrix (kernelMask 760) = decodeRows mask760Rows := by
  rw [show kernelMask 760 = kernelMask 8 * kernelMask 752 from kernelMask_xor 8 752]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask8 matrix_mask752 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask760)

theorem matrix_mask764 : toMatrix (kernelMask 764) = decodeRows mask764Rows := by
  rw [show kernelMask 764 = kernelMask 4 * kernelMask 760 from kernelMask_xor 4 760]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask4 matrix_mask760 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask764)

theorem matrix_mask765 : toMatrix (kernelMask 765) = decodeRows mask765Rows := by
  rw [show kernelMask 765 = kernelMask 1 * kernelMask 764 from kernelMask_xor 1 764]
  exact Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_mask1 matrix_mask764 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_mask765)

theorem matrix_firstProduct : toMatrix firstProduct = decodeRows firstProductRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix Janko4.LocalStructure.SymmetricLinear.NormalEight.matrix_seed matrix_mask1453 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_firstProduct)

theorem matrix_firstSquare : toMatrix firstSquare = decodeRows firstSquareRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_firstProduct matrix_firstProduct (Janko4.Cardinality.KernelCount.Relations.decoded_product check_firstSquare)

theorem matrix_firstCube : toMatrix firstCube = decodeRows firstCubeRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_firstSquare matrix_firstProduct (Janko4.Cardinality.KernelCount.Relations.decoded_product check_firstCube)

theorem matrix_firstConjugator : toMatrix firstConjugator = decodeRows firstConjugatorRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_firstCube matrix_firstCube (Janko4.Cardinality.KernelCount.Relations.decoded_product check_firstConjugator)

theorem matrix_bInverse : toMatrix bInverse = decodeRows bInverseRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_inv toMatrix matrix_b (by rw [← decode_packedMul, check_bInverse, decode_packedOne])

theorem matrix_ambientWord1 : toMatrix ambientWord1 = decodeRows ambientWord1Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_a matrix_bInverse (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord1)

theorem matrix_ambientWord2 : toMatrix ambientWord2 = decodeRows ambientWord2Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord1 matrix_bInverse (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord2)

theorem matrix_ambientWord3 : toMatrix ambientWord3 = decodeRows ambientWord3Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord2 matrix_a (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord3)

theorem matrix_ambientWord4 : toMatrix ambientWord4 = decodeRows ambientWord4Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord3 matrix_b (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord4)

theorem matrix_ambientWord5 : toMatrix ambientWord5 = decodeRows ambientWord5Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord4 matrix_b (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord5)

theorem matrix_ambientWord6 : toMatrix ambientWord6 = decodeRows ambientWord6Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord5 matrix_b (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord6)

theorem matrix_ambientWord7 : toMatrix ambientWord7 = decodeRows ambientWord7Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord6 matrix_a (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord7)

theorem matrix_ambientWord8 : toMatrix ambientWord8 = decodeRows ambientWord8Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord7 matrix_bInverse (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord8)

theorem matrix_ambientWord9 : toMatrix ambientWord9 = decodeRows ambientWord9Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord8 matrix_a (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord9)

theorem matrix_ambientWord10 : toMatrix ambientWord10 = decodeRows ambientWord10Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord9 matrix_bInverse (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord10)

theorem matrix_ambientWord11 : toMatrix ambientWord11 = decodeRows ambientWord11Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord10 matrix_a (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord11)

theorem matrix_ambientWord12 : toMatrix ambientWord12 = decodeRows ambientWord12Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord11 matrix_bInverse (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord12)

theorem matrix_ambientWord13 : toMatrix ambientWord13 = decodeRows ambientWord13Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord12 matrix_a (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord13)

theorem matrix_ambientWord14 : toMatrix ambientWord14 = decodeRows ambientWord14Rows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord13 matrix_bInverse (Janko4.Cardinality.KernelCount.Relations.decoded_product check_ambientWord14)

theorem matrix_ambientInverse : toMatrix ambientInverse = decodeRows ambientInverseRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_inv toMatrix matrix_ambientWord14 (by rw [← decode_packedMul, check_ambientInverse, decode_packedOne])

theorem matrix_secondLeft : toMatrix secondLeft = decodeRows secondLeftRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientInverse matrix_mask1453 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_secondLeft)

theorem matrix_secondConjugate : toMatrix secondConjugate = decodeRows secondConjugateRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_secondLeft matrix_ambientWord14 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_secondConjugate)

theorem matrix_secondProduct : toMatrix secondProduct = decodeRows secondProductRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_secondConjugate matrix_mask1453 (Janko4.Cardinality.KernelCount.Relations.decoded_product check_secondProduct)

theorem matrix_secondSquare : toMatrix secondSquare = decodeRows secondSquareRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_secondProduct matrix_secondProduct (Janko4.Cardinality.KernelCount.Relations.decoded_product check_secondSquare)

theorem matrix_secondCube : toMatrix secondCube = decodeRows secondCubeRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_secondSquare matrix_secondProduct (Janko4.Cardinality.KernelCount.Relations.decoded_product check_secondCube)

theorem matrix_secondSixth : toMatrix secondSixth = decodeRows secondSixthRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_secondCube matrix_secondCube (Janko4.Cardinality.KernelCount.Relations.decoded_product check_secondSixth)

theorem matrix_centralizerWord : toMatrix centralizerWord = decodeRows centralizerWordRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_ambientWord14 matrix_secondSixth (Janko4.Cardinality.KernelCount.Relations.decoded_product check_centralizerWord)

theorem matrix_rightConjugator : toMatrix rightConjugator = decodeRows rightConjugatorRows :=
  Janko4.Cardinality.KernelCount.Relations.eval_mul toMatrix matrix_firstConjugator matrix_centralizerWord (Janko4.Cardinality.KernelCount.Relations.decoded_product check_rightConjugator)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
