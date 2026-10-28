module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Assemble scalar table checks into packed matrix equalities

The row checks provide the two packed products and successor bounds. The native
checks provide all source indices and literal right-generator transitions.
Coordinate induction on the twelve-bit slots combines these into precisely
`Packed.Certificate`. `Table` discharges both check families exhaustively.
This construction does not assume packed-arithmetic correctness.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem image_rightA_of_checks (hr : ∀ n, n < 2808 → RowGood n)
    (hn : ∀ c, NativeGood c) (c : Matrix.PSL3Three.MatrixCode)
    (hc : Matrix.PSL3Three.codeDet c = 1) :
    image (Matrix.PSL3Three.matrixCodeEquiv
      (Matrix.PSL3Three.decodeMatrix c * nativeA.val)) = mul (image c) generatorA := by
  obtain ⟨ha, _, hb⟩ := hn c hc
  apply Vector.ext
  intro i hi
  have hri := slot_lt_of_bounded 16 i (packedIndices c) hi hb
  have hrow := hr (slot i (packedIndices c)) hri
  have hcoord :
      rowValue (slot i (packedIndices (Matrix.PSL3Three.matrixCodeEquiv
        (Matrix.PSL3Three.decodeMatrix c * nativeA.val)))) =
      row (rowValue (slot i (packedIndices c))) generatorA := by
    rw [ha, slot_mapSlots _ 16 i _ hi, Nat.mod_eq_of_lt hrow.2.2.1]
    exact hrow.1.symm
  simpa [image, indices, mul, Vector.get, slot_eq, Fin.cast] using hcoord

theorem image_rightB_of_checks (hr : ∀ n, n < 2808 → RowGood n)
    (hn : ∀ c, NativeGood c) (c : Matrix.PSL3Three.MatrixCode)
    (hc : Matrix.PSL3Three.codeDet c = 1) :
    image (Matrix.PSL3Three.matrixCodeEquiv
      (Matrix.PSL3Three.decodeMatrix c * nativeB.val)) = mul (image c) generatorB := by
  obtain ⟨_, hb, hbounds⟩ := hn c hc
  apply Vector.ext
  intro i hi
  have hri := slot_lt_of_bounded 16 i (packedIndices c) hi hbounds
  have hrow := hr (slot i (packedIndices c)) hri
  have hcoord :
      rowValue (slot i (packedIndices (Matrix.PSL3Three.matrixCodeEquiv
        (Matrix.PSL3Three.decodeMatrix c * nativeB.val)))) =
      row (rowValue (slot i (packedIndices c))) generatorB := by
    rw [hb, slot_mapSlots _ 16 i _ hi, Nat.mod_eq_of_lt hrow.2.2.2]
    exact hrow.2.1.symm
  simpa [image, indices, mul, Vector.get, slot_eq, Fin.cast] using hcoord

theorem image_one : image (Matrix.PSL3Three.matrixCodeEquiv 1) = one := by
  have h : ∀ j : Fin 16,
      rowValue (packedIndices (Matrix.PSL3Three.matrixCodeEquiv 1) / 4096 ^ j.val % 4096) = one.get j := by
    decide +kernel
  apply Vector.ext
  intro i hi
  simpa [image, indices, Vector.get, Fin.cast] using h ⟨i, hi⟩

/-- Assemble the two exhaustive numerical check families. -/
def certificateOfChecks (hr : ∀ n, n < 2808 → RowGood n) (hn : ∀ c, NativeGood c) : Certificate where
  image := image
  one := image_one
  rightA := image_rightA_of_checks hr hn
  rightB := image_rightB_of_checks hr hn

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
