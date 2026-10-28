module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 12

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk108 : ∀ i : Fin 81, NativeGood (⟨108 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk109 : ∀ i : Fin 81, NativeGood (⟨109 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk110 : ∀ i : Fin 81, NativeGood (⟨110 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk111 : ∀ i : Fin 81, NativeGood (⟨111 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk112 : ∀ i : Fin 81, NativeGood (⟨112 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk113 : ∀ i : Fin 81, NativeGood (⟨113 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk114 : ∀ i : Fin 81, NativeGood (⟨114 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk115 : ∀ i : Fin 81, NativeGood (⟨115 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk116 : ∀ i : Fin 81, NativeGood (⟨116 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock12 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(12 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk108
  · exact nativeChunk109
  · exact nativeChunk110
  · exact nativeChunk111
  · exact nativeChunk112
  · exact nativeChunk113
  · exact nativeChunk114
  · exact nativeChunk115
  · exact nativeChunk116

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
