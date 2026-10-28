module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 15

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk135 : ∀ i : Fin 81, NativeGood (⟨135 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk136 : ∀ i : Fin 81, NativeGood (⟨136 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk137 : ∀ i : Fin 81, NativeGood (⟨137 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk138 : ∀ i : Fin 81, NativeGood (⟨138 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk139 : ∀ i : Fin 81, NativeGood (⟨139 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk140 : ∀ i : Fin 81, NativeGood (⟨140 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk141 : ∀ i : Fin 81, NativeGood (⟨141 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk142 : ∀ i : Fin 81, NativeGood (⟨142 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk143 : ∀ i : Fin 81, NativeGood (⟨143 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock15 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(15 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk135
  · exact nativeChunk136
  · exact nativeChunk137
  · exact nativeChunk138
  · exact nativeChunk139
  · exact nativeChunk140
  · exact nativeChunk141
  · exact nativeChunk142
  · exact nativeChunk143

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
