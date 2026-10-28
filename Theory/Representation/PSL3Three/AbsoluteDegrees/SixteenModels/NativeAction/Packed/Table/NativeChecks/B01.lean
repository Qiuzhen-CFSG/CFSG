module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 1

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk9 : ∀ i : Fin 81, NativeGood (⟨9 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk10 : ∀ i : Fin 81, NativeGood (⟨10 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk11 : ∀ i : Fin 81, NativeGood (⟨11 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk12 : ∀ i : Fin 81, NativeGood (⟨12 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk13 : ∀ i : Fin 81, NativeGood (⟨13 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk14 : ∀ i : Fin 81, NativeGood (⟨14 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk15 : ∀ i : Fin 81, NativeGood (⟨15 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk16 : ∀ i : Fin 81, NativeGood (⟨16 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk17 : ∀ i : Fin 81, NativeGood (⟨17 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock1 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(1 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk9
  · exact nativeChunk10
  · exact nativeChunk11
  · exact nativeChunk12
  · exact nativeChunk13
  · exact nativeChunk14
  · exact nativeChunk15
  · exact nativeChunk16
  · exact nativeChunk17

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
