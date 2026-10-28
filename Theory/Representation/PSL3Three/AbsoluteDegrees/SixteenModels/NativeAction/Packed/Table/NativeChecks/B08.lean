module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 8

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk72 : ∀ i : Fin 81, NativeGood (⟨72 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk73 : ∀ i : Fin 81, NativeGood (⟨73 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk74 : ∀ i : Fin 81, NativeGood (⟨74 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk75 : ∀ i : Fin 81, NativeGood (⟨75 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk76 : ∀ i : Fin 81, NativeGood (⟨76 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk77 : ∀ i : Fin 81, NativeGood (⟨77 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk78 : ∀ i : Fin 81, NativeGood (⟨78 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk79 : ∀ i : Fin 81, NativeGood (⟨79 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk80 : ∀ i : Fin 81, NativeGood (⟨80 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock8 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(8 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk72
  · exact nativeChunk73
  · exact nativeChunk74
  · exact nativeChunk75
  · exact nativeChunk76
  · exact nativeChunk77
  · exact nativeChunk78
  · exact nativeChunk79
  · exact nativeChunk80

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
