module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT2

/-!
# A checked dense row of the terminal square

This applies the complete expansion bridge to row 1531 of the original T²
candidate, and proves the corresponding row of T²T² is the identity row.
It is a representative kernel check, not the full terminal matrix equation.
Source: ATLAS M24G1-P1; see `source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts

set_option maxRecDepth 8192 in
private theorem t2_numeric_row1531 :
    Arithmetic.row Data.t2Rows[1531]! WideT2.blocks = 2^1531 := by decide +kernel

/-- The original candidate product, on every column of row 1531. -/
theorem t_fourth_row1531 (j : Fin 1792) :
    (Data.t2 * Data.t2) ⟨1531, by decide⟩ j =
      (1 : Matrix (Fin 1792) (Fin 1792) (ZMod 2)) ⟨1531, by decide⟩ j := by
  have h := Arithmetic.matrix_row Data.t2Rows Data.t2Rows WideT2.blocks
    Data.t2Rows_length Data.t2Rows_length WideT2.bridge WideT2.blocks_lengths
    ⟨1531, by decide⟩ j
  change (Data.t2 * Data.t2) ⟨1531, by decide⟩ j =
    Thompson.BinaryMatrix.bit (Arithmetic.row Data.t2Rows[1531]! WideT2.blocks) j.val at h
  rw [t2_numeric_row1531] at h
  have hone (i k : Fin 1792) : Thompson.BinaryMatrix.bit (2^i.val) k.val =
      (1 : Matrix (Fin 1792) (Fin 1792) (ZMod 2)) i k := by
    simp [Thompson.BinaryMatrix.bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
  exact h.trans (hone ⟨1531, by decide⟩ j)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts
