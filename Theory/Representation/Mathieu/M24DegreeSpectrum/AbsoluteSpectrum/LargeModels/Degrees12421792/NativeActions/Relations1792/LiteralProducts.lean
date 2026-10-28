module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792

/-!
# The packed checker applied to the literal degree-1792 matrices

`first_square_of_chunks` applies the carry-free checker to the unchanged ATLAS
first matrix. Its premises are explicit natural-number certificate equations;
no action, density, or presentation-exactness premise is used. The concrete
certificate producer must still discharge those equations. This is an adapter
for the first of the seven equations, not an assertion of all the relations.

Source: ATLAS M24G1-P1 and M24G1-f2r1792B0.m1; see
`../../source/README.md` and `../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792
open Arithmetic

/-- Packed binary rows of the identity, in the original row convention. -/
def identityRows (n : Nat) : List Nat := List.ofFn (fun i : Fin n => 2 ^ i.val)

theorem decode_identityRows (n : Nat) : decodeRows n (identityRows n) = 1 := by
  ext i j
  simp [decodeRows, identityRows, Thompson.BinaryMatrix.bit,
    Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

/-- The literal first ATLAS word follows from the two computational checks.
The producer owns both premises, including the connection to the original data. -/
theorem first_square_of_chunks (wide : List (List Nat))
    (hw : wide.flatten = Data1792.firstRows.toList.map (expandBlocks 32 56))
    (h : Data1792.firstRows.toList.map
      (fun a => compressBlocks 32 56 (accumChunks a wide)) = identityRows 1792) :
    Data1792.first ^ 2 = 1 := by
  have hs : Data1792.firstRows.toList.length = 32 * 56 := by decide +kernel
  have hp := product_chunks 32 56 (by decide) Data1792.firstRows.toList
    Data1792.firstRows.toList (identityRows 1792) wide hs hs hw h
  change decodeRows 1792 Data1792.firstRows.toList *
    decodeRows 1792 Data1792.firstRows.toList = decodeRows 1792 (identityRows 1792) at hp
  rw [decodeRows_array, decode_identityRows] at hp
  simpa only [pow_two, Data1792.first] using hp

/-- Application to the exact first source word; the numeric checks remain explicit. -/
theorem first_word_of_chunks (wide : List (List Nat))
    (hw : wide.flatten = Data1792.firstRows.toList.map (expandBlocks 32 56))
    (h : Data1792.firstRows.toList.map
      (fun a => compressBlocks 32 56 (accumChunks a wide)) = identityRows 1792) :
    Presentation.rowRelatorValues Data1792.first Data1792.second 0 = 1 := by
  simpa only [Presentation.rowRelatorValues, Matrix.cons_val_zero] using
    first_square_of_chunks wide hw h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792
