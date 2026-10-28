module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.LiteralProducts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.Arithmetic

/-!
# A checked dense row of the literal first square

This is the densest first-generator row (951 nonzero entries). The numeric
check is converted to an equality of actual matrix entries. It certifies only
row 1531, not the full square or the other six ATLAS words. The measurement
and bounded alternatives are recorded in `source/README.md`.

Source: the unchanged ATLAS M24G1-f2r1792B0.m1, documented in
`../../source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792
open Thompson.BinaryMatrix
open Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty

set_option maxRecDepth 8192 in
private theorem dense_row_checked :
    row Data1792.firstRows[1531]! Data1792.firstRows.toList 0 = 2 ^ 1531 := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- The representative calculation, as a theorem on the literal ATLAS matrix. -/
theorem first_square_row1531 (j : Fin 1792) :
    (Data1792.first ^ 2) (1531 : Fin 1792) j =
      (1 : Matrix (Fin 1792) (Fin 1792) (ZMod 2)) (1531 : Fin 1792) j := by
  rw [pow_two, Matrix.mul_apply]
  simp only [Data1792.first, decode]
  have hi : (1531 : Fin 1792).val = 1531 := rfl
  simp only [hi]
  rw [← bit_row_array 1792 Data1792.firstRows (by decide +kernel), dense_row_checked]
  simp only [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff, hi]
  simp [eq_comm]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792
