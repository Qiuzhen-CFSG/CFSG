module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.LiteralProducts

/-!
# Four checked rows of the literal first square

Two one-coordinate inputs and two dense inputs exercise both branches of the
row checker. Row 967 is the densest row (663 nonzero entries); row 1238 has
638. Each check below yields equality of actual matrix entries. This certifies
only these four rows, not the complete square or all seven ATLAS equations.

Source: the original M24G1-f2r1242B0.m1, documented in
`../../source/README.md`. Measurements are in `source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
open Thompson.BinaryMatrix

private def input : List Nat := [nat_lit 0x2,nat_lit 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,nat_lit 0x1f10fe2da14937dce02f1cb1fd5af8e3012281dea2b346dbebdb6b3c8a6bd1fa9f3849a536f3d6f8e2d4078fce9054e91d290dedf12f72b417c74dbfde7f5f5a195efff5f19a945b21412b7eff4cf8175f29f6b758b74dcf19c0fb14faef910e0978d47fc885b1cf596ab9fedaad6407ed655d45b620aa5acb1803dd8b14ac15b2efc9bf9a799e50b88b26252ee70168591a702769d5121d2f2b198,nat_lit 0xd3f17231784ba76e081c790b070fdc74db7c2c6c761646243e35c14b99f8d4ea9525fd58a429ef6d8ef6a679e238961b365707ef4caa1e35fa9864248d4d88df9ea6d9cd219ec301a104d4ef4aadc38e78fa530e77f72c0b686fe1d92ea853dca1d3c785270632b010f2fb90d429cb32de64afc7ec3fedca449d29415b47a77a8ef7cbed540f5c6b04ce5190ee5017b37660c56b7f111b7f0d83db]
private def output : List Nat := [nat_lit 0x1,nat_lit 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,nat_lit 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,nat_lit 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
private def hints : List (Option Nat) := [some 1,some 661,none,none]
set_option maxRecDepth 8192 in
private theorem checked : check input Data1242.firstRows.toList output hints = true := by decide +kernel

private def sampleIndex : Fin 4 → Fin 1242 := ![0, 500, 967, 1238]

set_option maxRecDepth 8192 in
private theorem input_eq (k : Fin 4) : input[k.val]! = Data1242.firstRows[(sampleIndex k).val]! := by
  revert k
  decide +kernel

set_option maxRecDepth 8192 in
private theorem output_eq (k : Fin 4) : output[k.val]! = 2^(sampleIndex k).val := by
  revert k
  decide +kernel

private theorem sample_correct (k : Fin 4) (j : Fin 1242) :
    (Data1242.first ^ 2) (sampleIndex k) j =
      (1 : Matrix (Fin 1242) (Fin 1242) (ZMod 2)) (sampleIndex k) j := by
  rw [pow_two]
  have hp := entry_of_check 1242 Data1242.firstRows Data1242.firstRows input output hints
    checked (by decide +kernel) k.val (by exact k.isLt) (sampleIndex k) j (input_eq k)
  change (Data1242.first * Data1242.first) (sampleIndex k) j = _ at hp
  rw [hp, output_eq]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

/-- A one-coordinate input at the beginning of the original data. -/
theorem first_square_row0 (j : Fin 1242) :
    (Data1242.first ^ 2) (0 : Fin 1242) j =
      (1 : Matrix (Fin 1242) (Fin 1242) (ZMod 2)) (0 : Fin 1242) j :=
  sample_correct 0 j

/-- A one-coordinate input in the middle of the original data. -/
theorem first_square_row500 (j : Fin 1242) :
    (Data1242.first ^ 2) (500 : Fin 1242) j =
      (1 : Matrix (Fin 1242) (Fin 1242) (ZMod 2)) (500 : Fin 1242) j :=
  sample_correct 1 j

/-- The densest input row, checked against the literal untransposed matrix. -/
theorem first_square_row967 (j : Fin 1242) :
    (Data1242.first ^ 2) (967 : Fin 1242) j =
      (1 : Matrix (Fin 1242) (Fin 1242) (ZMod 2)) (967 : Fin 1242) j :=
  sample_correct 2 j

/-- A second dense input row, near the end of the original data. -/
theorem first_square_row1238 (j : Fin 1242) :
    (Data1242.first ^ 2) (1238 : Fin 1242) j =
      (1 : Matrix (Fin 1242) (Fin 1242) (ZMod 2)) (1238 : Fin 1242) j :=
  sample_correct 3 j

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
