module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 13

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk117 : ∀ i : Fin 81, NativeGood (⟨117 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk118 : ∀ i : Fin 81, NativeGood (⟨118 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk119 : ∀ i : Fin 81, NativeGood (⟨119 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk120 : ∀ i : Fin 81, NativeGood (⟨120 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk121 : ∀ i : Fin 81, NativeGood (⟨121 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk122 : ∀ i : Fin 81, NativeGood (⟨122 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk123 : ∀ i : Fin 81, NativeGood (⟨123 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk124 : ∀ i : Fin 81, NativeGood (⟨124 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk125 : ∀ i : Fin 81, NativeGood (⟨125 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock13 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(13 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk117
  · exact nativeChunk118
  · exact nativeChunk119
  · exact nativeChunk120
  · exact nativeChunk121
  · exact nativeChunk122
  · exact nativeChunk123
  · exact nativeChunk124
  · exact nativeChunk125

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
