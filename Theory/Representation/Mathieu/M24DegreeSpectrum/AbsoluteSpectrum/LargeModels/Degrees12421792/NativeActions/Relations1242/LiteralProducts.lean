module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1242

/-!
# Row checks for the literal degree-1242 ATLAS generators

These adapters connect checked packed rows to actual matrix entries and to the
first positive source word. Certificate premises are numerical equations and
must be discharged by the concrete producers. They are not native-action,
density, or presentation-exactness assumptions.

Source: ATLAS M24G1-P1 and M24G1-f2r1242B0.m1, with conventions and provenance
in `../../source/README.md` and `../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
open Thompson.BinaryMatrix
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair

/-- Packed identity rows, with column j in bit j. -/
def identityRows (n : Nat) : List Nat := List.ofFn (fun i : Fin n => 2 ^ i.val)

theorem decode_identityRows (n : Nat) : decode n (identityRows n).toArray = 1 := by
  ext i j
  simp [decode, identityRows, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

/-- A packed check gives an equality of actual entries, including a selected
row from a larger matrix. The input and output row identifications are explicit. -/
theorem entry_of_check (n : Nat) (a b : Array Nat) (xs ys : List Nat)
    (hs : List (Option Nat)) (h : check xs b.toList ys hs = true)
    (hb : b.size = n) (k : Nat) (hk : k < xs.length) (i j : Fin n)
    (hi : xs[k]! = a[i.val]!) :
    (decode n a * decode n b) i j = bit ys[k]! j.val := by
  have hh := checkRows_get xs b.toList ys (check_sound xs b.toList ys hs h) k hk
  rw [hi, shiftRow_eq_row] at hh
  change (∑ t : Fin n, bit a[i.val]! t.val * bit b[t.val]! j.val) = _
  rw [← bit_row_array n b hb, hh]

/-- The first source equation follows from a complete row certificate. -/
theorem first_square_of_check (hs : List (Option Nat))
    (h : check Data1242.firstRows.toList Data1242.firstRows.toList
      (identityRows 1242) hs = true) : Data1242.first ^ 2 = 1 := by
  have hn : Data1242.firstRows.toList.length = 1242 := by decide +kernel
  have hp := product 1242 Data1242.firstRows.toList Data1242.firstRows.toList
    (identityRows 1242) hs hn hn h
  rw [Array.toArray_toList, decode_identityRows] at hp
  simpa only [pow_two, Data1242.first] using hp

/-- The exact first positive ATLAS word, retaining its numerical certificate
premise until the concrete producer supplies it. -/
theorem first_word_of_check (hs : List (Option Nat))
    (h : check Data1242.firstRows.toList Data1242.firstRows.toList
      (identityRows 1242) hs = true) :
    Presentation.rowRelatorValues Data1242.first Data1242.second 0 = 1 := by
  simpa only [Presentation.rowRelatorValues, Matrix.cons_val_zero] using
    first_square_of_check hs h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
