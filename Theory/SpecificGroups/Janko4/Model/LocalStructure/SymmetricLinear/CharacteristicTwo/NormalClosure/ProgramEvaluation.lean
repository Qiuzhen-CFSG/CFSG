module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure.ProgramProducts

/-!
# Evaluation of all seventeen max4 register instructions

Each intermediate matrix is linked to its literal word in the certified J₄
generators. The inverse steps use certified products with the identity.
The final two products give the supplied faithful coordinates of `first` and
`second`. Adapted from the saved quotient certificate with originals preserved;
see `source/README.md` and `SymmetricLinear/Model/source/J4G1-max4W1`.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure
open GeneratorCertificates ProgramData ProgramData.Products

private theorem decode_a : decodeRows aRows = toMatrix a := rfl

private theorem decode_b : decodeRows bRows = toMatrix b := rfl

private def stage01 : Model := a * b

private theorem decode_stage01 : decodeRows product_stage01Rows = toMatrix stage01 := by
  change _ = toMatrix (a * b)
  simp only [map_mul, ← decode_a, ← decode_b]
  rw [← decode_packedMul, product_stage01]

private theorem decode_stage02Power1 : decodeRows product_stage01Rows = decodeRows product_stage01Rows ^ 1 := by simp

private theorem decode_stage02Power2 : decodeRows stage02Power2Rows = decodeRows product_stage01Rows ^ 2 := by
  rw [← stage02Power2, decode_packedMul, pow_two]

private theorem decode_stage02Power3 : decodeRows stage02Power3Rows = decodeRows product_stage01Rows ^ 3 := by
  rw [← stage02Power3, decode_packedMul, decode_stage02Power2, ← pow_succ]

private def stage02 : Model := stage01 ^ 3

private theorem decode_stage02 : decodeRows stage02Power3Rows = toMatrix stage02 := by
  change _ = toMatrix (stage01 ^ 3)
  rw [map_pow, ← decode_stage01]
  exact decode_stage02Power3

private def stage03 : Model := stage02 * b

private theorem decode_stage03 : decodeRows product_stage03Rows = toMatrix stage03 := by
  change _ = toMatrix (stage02 * b)
  simp only [map_mul, ← decode_stage02, ← decode_b]
  rw [← decode_packedMul, product_stage03]

private def stage04 : Model := b * a

private theorem decode_stage04 : decodeRows product_stage04Rows = toMatrix stage04 := by
  change _ = toMatrix (b * a)
  simp only [map_mul, ← decode_b, ← decode_a]
  rw [← decode_packedMul, product_stage04]

private def stage05 : Model := stage03 * b

private theorem decode_stage05 : decodeRows product_stage05Rows = toMatrix stage05 := by
  change _ = toMatrix (stage03 * b)
  simp only [map_mul, ← decode_stage03, ← decode_b]
  rw [← decode_packedMul, product_stage05]

private theorem decode_stage06Power1 : decodeRows product_stage05Rows = decodeRows product_stage05Rows ^ 1 := by simp

private theorem decode_stage06Power2 : decodeRows stage06Power2Rows = decodeRows product_stage05Rows ^ 2 := by
  rw [← stage06Power2, decode_packedMul, pow_two]

private theorem decode_stage06Power3 : decodeRows stage06Power3Rows = decodeRows product_stage05Rows ^ 3 := by
  rw [← stage06Power3, decode_packedMul, decode_stage06Power2, ← pow_succ]

private def stage06 : Model := stage05 ^ 3

private theorem decode_stage06 : decodeRows stage06Power3Rows = toMatrix stage06 := by
  change _ = toMatrix (stage05 ^ 3)
  rw [map_pow, ← decode_stage05]
  exact decode_stage06Power3

private theorem decode_stage07Power1 : decodeRows product_stage04Rows = decodeRows product_stage04Rows ^ 1 := by simp

private theorem decode_stage07Power2 : decodeRows stage07Power2Rows = decodeRows product_stage04Rows ^ 2 := by
  rw [← stage07Power2, decode_packedMul, pow_two]

private theorem decode_stage07Power4 : decodeRows stage07Power4Rows = decodeRows product_stage04Rows ^ 4 := by
  rw [← stage07Power4, decode_packedMul, decode_stage07Power2, ← pow_add]

private theorem decode_stage07Power5 : decodeRows stage07Power5Rows = decodeRows product_stage04Rows ^ 5 := by
  rw [← stage07Power5, decode_packedMul, decode_stage07Power4, ← pow_succ]

private theorem decode_stage07Power10 : decodeRows stage07Power10Rows = decodeRows product_stage04Rows ^ 10 := by
  rw [← stage07Power10, decode_packedMul, decode_stage07Power5, ← pow_add]

private theorem decode_stage07Power11 : decodeRows stage07Power11Rows = decodeRows product_stage04Rows ^ 11 := by
  rw [← stage07Power11, decode_packedMul, decode_stage07Power10, ← pow_succ]

private theorem decode_stage07Power22 : decodeRows stage07Power22Rows = decodeRows product_stage04Rows ^ 22 := by
  rw [← stage07Power22, decode_packedMul, decode_stage07Power11, ← pow_add]

private def stage07 : Model := stage04 ^ 22

private theorem decode_stage07 : decodeRows stage07Power22Rows = toMatrix stage07 := by
  change _ = toMatrix (stage04 ^ 22)
  rw [map_pow, ← decode_stage04]
  exact decode_stage07Power22

private theorem decode_stage08Power6 : decodeRows stage08Power6Rows = decodeRows product_stage01Rows ^ 6 := by
  rw [← stage08Power6, decode_packedMul, decode_stage02Power3, ← pow_add]

private theorem decode_stage08Power12 : decodeRows stage08Power12Rows = decodeRows product_stage01Rows ^ 12 := by
  rw [← stage08Power12, decode_packedMul, decode_stage08Power6, ← pow_add]

private theorem decode_stage08Power13 : decodeRows stage08Power13Rows = decodeRows product_stage01Rows ^ 13 := by
  rw [← stage08Power13, decode_packedMul, decode_stage08Power12, ← pow_succ]

private def stage08 : Model := stage01 ^ 13

private theorem decode_stage08 : decodeRows stage08Power13Rows = toMatrix stage08 := by
  change _ = toMatrix (stage01 ^ 13)
  rw [map_pow, ← decode_stage01]
  exact decode_stage08Power13

private def stage09 : Model := stage07 * stage08

private theorem decode_stage09 : decodeRows product_stage09Rows = toMatrix stage09 := by
  change _ = toMatrix (stage07 * stage08)
  simp only [map_mul, ← decode_stage07, ← decode_stage08]
  rw [← decode_packedMul, product_stage09]

private def stage10 : Model := stage04 * stage04

private theorem decode_stage10 : decodeRows product_stage10Rows = toMatrix stage10 := by
  change _ = toMatrix (stage04 * stage04)
  simp only [map_mul, ← decode_stage04, ← decode_stage04]
  rw [← decode_packedMul, product_stage10]

private def stage11 : Model := stage09⁻¹

private theorem decode_stage11 : decodeRows stage11Rows = toMatrix stage11 := by
  change _ = toMatrix (stage09⁻¹)
  apply left_inv_eq_right_inv (a := toMatrix stage09)
  · rw [← decode_stage09, ← decode_packedMul, product_stage11, decode_packedOne]
  · rw [← map_mul, mul_inv_cancel, map_one]

private def stage12 : Model := stage11 * stage06

private theorem decode_stage12 : decodeRows product_stage12Rows = toMatrix stage12 := by
  change _ = toMatrix (stage11 * stage06)
  simp only [map_mul, ← decode_stage11, ← decode_stage06]
  rw [← decode_packedMul, product_stage12]

private def stage13 : Model := stage06 * stage06

private theorem decode_stage13 : decodeRows product_stage13Rows = toMatrix stage13 := by
  change _ = toMatrix (stage06 * stage06)
  simp only [map_mul, ← decode_stage06, ← decode_stage06]
  rw [← decode_packedMul, product_stage13]

private def stage14 : Model := stage12 * stage09

private theorem decode_stage14 : decodeRows product_stage14Rows = toMatrix stage14 := by
  change _ = toMatrix (stage12 * stage09)
  simp only [map_mul, ← decode_stage12, ← decode_stage09]
  rw [← decode_packedMul, product_stage14]

private def stage15 : Model := stage10⁻¹

private theorem decode_stage15 : decodeRows stage15Rows = toMatrix stage15 := by
  change _ = toMatrix (stage10⁻¹)
  apply left_inv_eq_right_inv (a := toMatrix stage10)
  · rw [← decode_stage10, ← decode_packedMul, product_stage15, decode_packedOne]
  · rw [← map_mul, mul_inv_cancel, map_one]

private def stage16 : Model := stage15 * stage13

private theorem decode_stage16 : decodeRows product_stage16Rows = toMatrix stage16 := by
  change _ = toMatrix (stage15 * stage13)
  simp only [map_mul, ← decode_stage15, ← decode_stage13]
  rw [← decode_packedMul, product_stage16]

private def stage17 : Model := stage16 * stage10

private theorem decode_stage17 : decodeRows product_stage17Rows = toMatrix stage17 := by
  change _ = toMatrix (stage16 * stage10)
  simp only [map_mul, ← decode_stage16, ← decode_stage10]
  rw [← decode_packedMul, product_stage17]

/-- The first computed matrix is the literal first program output. -/
theorem first_matrix : toMatrix (first : Model) = decodeRows firstRows :=
  decode_stage17.symm

/-- The second computed matrix is the literal second program output. -/
theorem second_matrix : toMatrix (second : Model) = decodeRows secondRows :=
  decode_stage14.symm

theorem first_coordinates : coordinates first = decodeRows Coordinates.firstRows := by
  rw [coordinates, first_matrix, ← decode_packedMul, first_left,
    ← decode_packedMul, first_conjugate]

theorem second_coordinates : coordinates second = decodeRows Coordinates.secondRows := by
  rw [coordinates, second_matrix, ← decode_packedMul, second_left,
    ← decode_packedMul, second_conjugate]

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.NormalClosure
