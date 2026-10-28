module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Data

/-!
# Checked packed inputs for the second compound matrix

Every bit of all 55 input masks is checked against the literal native code
matrix and the published five-subset enumeration. The packed Laplace evaluator
therefore computes exactly `compoundBit true i j` at bit j of row i.
The row index divides the 462 output checks into eleven batches of 42.

Source and column conventions: `NativeActions/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second

def spread (r : Fin 11) (k : Fin 5) : ℕ := (spreadRows[r.val]!)[k.val]!

lemma spread_testBit : ∀ (r : Fin 11) (k : Fin 5) (j : Fin 462),
    (spread r k).testBit j.val = codeBit true r (fiveTuple j k) := by
  decide +kernel

def packedRow (i : Fin 462) : ℕ :=
  packedDet (2^462 - 1) 5 (fun k l => spread (fiveTuple i k) l)

def rowIndex (b : Fin 11) (i : Fin 42) : Fin 462 :=
  ⟨42 * b.val + i.val, by omega⟩

lemma mask_testBit : ∀ j : Fin 462, (2^462 - 1 : ℕ).testBit j.val = true := by
  decide +kernel

lemma packedRow_testBit (i j : Fin 462) :
    (packedRow i).testBit j.val = compoundBit true i j := by
  rw [packedRow, packedDet_testBit _ _ _ _ (mask_testBit j)]
  unfold compoundBit
  congr 1
  funext k l
  exact spread_testBit (fiveTuple i k) l j

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second
