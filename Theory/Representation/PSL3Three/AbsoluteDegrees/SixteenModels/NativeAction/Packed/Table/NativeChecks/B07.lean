module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 7

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk63 : ∀ i : Fin 81, NativeGood (⟨63 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk64 : ∀ i : Fin 81, NativeGood (⟨64 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk65 : ∀ i : Fin 81, NativeGood (⟨65 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk66 : ∀ i : Fin 81, NativeGood (⟨66 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk67 : ∀ i : Fin 81, NativeGood (⟨67 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk68 : ∀ i : Fin 81, NativeGood (⟨68 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk69 : ∀ i : Fin 81, NativeGood (⟨69 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk70 : ∀ i : Fin 81, NativeGood (⟨70 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk71 : ∀ i : Fin 81, NativeGood (⟨71 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock7 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(7 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk63
  · exact nativeChunk64
  · exact nativeChunk65
  · exact nativeChunk66
  · exact nativeChunk67
  · exact nativeChunk68
  · exact nativeChunk69
  · exact nativeChunk70
  · exact nativeChunk71

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
