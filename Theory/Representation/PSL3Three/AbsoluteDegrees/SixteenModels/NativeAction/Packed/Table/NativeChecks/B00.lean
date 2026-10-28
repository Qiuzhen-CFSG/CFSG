module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 0

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk0 : ∀ i : Fin 81, NativeGood (⟨0 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk1 : ∀ i : Fin 81, NativeGood (⟨1 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk2 : ∀ i : Fin 81, NativeGood (⟨2 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk3 : ∀ i : Fin 81, NativeGood (⟨3 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk4 : ∀ i : Fin 81, NativeGood (⟨4 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk5 : ∀ i : Fin 81, NativeGood (⟨5 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk6 : ∀ i : Fin 81, NativeGood (⟨6 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk7 : ∀ i : Fin 81, NativeGood (⟨7 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk8 : ∀ i : Fin 81, NativeGood (⟨8 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock0 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(0 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk0
  · exact nativeChunk1
  · exact nativeChunk2
  · exact nativeChunk3
  · exact nativeChunk4
  · exact nativeChunk5
  · exact nativeChunk6
  · exact nativeChunk7
  · exact nativeChunk8

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
