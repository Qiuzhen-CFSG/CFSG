module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 9

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk81 : ∀ i : Fin 81, NativeGood (⟨81 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk82 : ∀ i : Fin 81, NativeGood (⟨82 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk83 : ∀ i : Fin 81, NativeGood (⟨83 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk84 : ∀ i : Fin 81, NativeGood (⟨84 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk85 : ∀ i : Fin 81, NativeGood (⟨85 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk86 : ∀ i : Fin 81, NativeGood (⟨86 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk87 : ∀ i : Fin 81, NativeGood (⟨87 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk88 : ∀ i : Fin 81, NativeGood (⟨88 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk89 : ∀ i : Fin 81, NativeGood (⟨89 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock9 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(9 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk81
  · exact nativeChunk82
  · exact nativeChunk83
  · exact nativeChunk84
  · exact nativeChunk85
  · exact nativeChunk86
  · exact nativeChunk87
  · exact nativeChunk88
  · exact nativeChunk89

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
