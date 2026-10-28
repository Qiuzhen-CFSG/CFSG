module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 5

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk45 : ∀ i : Fin 81, NativeGood (⟨45 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk46 : ∀ i : Fin 81, NativeGood (⟨46 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk47 : ∀ i : Fin 81, NativeGood (⟨47 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk48 : ∀ i : Fin 81, NativeGood (⟨48 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk49 : ∀ i : Fin 81, NativeGood (⟨49 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk50 : ∀ i : Fin 81, NativeGood (⟨50 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk51 : ∀ i : Fin 81, NativeGood (⟨51 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk52 : ∀ i : Fin 81, NativeGood (⟨52 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk53 : ∀ i : Fin 81, NativeGood (⟨53 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock5 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(5 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk45
  · exact nativeChunk46
  · exact nativeChunk47
  · exact nativeChunk48
  · exact nativeChunk49
  · exact nativeChunk50
  · exact nativeChunk51
  · exact nativeChunk52
  · exact nativeChunk53

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
