module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 2

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk18 : ∀ i : Fin 81, NativeGood (⟨18 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk19 : ∀ i : Fin 81, NativeGood (⟨19 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk20 : ∀ i : Fin 81, NativeGood (⟨20 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk21 : ∀ i : Fin 81, NativeGood (⟨21 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk22 : ∀ i : Fin 81, NativeGood (⟨22 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk23 : ∀ i : Fin 81, NativeGood (⟨23 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk24 : ∀ i : Fin 81, NativeGood (⟨24 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk25 : ∀ i : Fin 81, NativeGood (⟨25 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk26 : ∀ i : Fin 81, NativeGood (⟨26 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock2 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(2 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk18
  · exact nativeChunk19
  · exact nativeChunk20
  · exact nativeChunk21
  · exact nativeChunk22
  · exact nativeChunk23
  · exact nativeChunk24
  · exact nativeChunk25
  · exact nativeChunk26

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
