module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 17

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk153 : ∀ i : Fin 81, NativeGood (⟨153 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk154 : ∀ i : Fin 81, NativeGood (⟨154 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk155 : ∀ i : Fin 81, NativeGood (⟨155 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk156 : ∀ i : Fin 81, NativeGood (⟨156 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk157 : ∀ i : Fin 81, NativeGood (⟨157 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk158 : ∀ i : Fin 81, NativeGood (⟨158 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk159 : ∀ i : Fin 81, NativeGood (⟨159 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk160 : ∀ i : Fin 81, NativeGood (⟨160 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk161 : ∀ i : Fin 81, NativeGood (⟨161 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock17 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(17 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk153
  · exact nativeChunk154
  · exact nativeChunk155
  · exact nativeChunk156
  · exact nativeChunk157
  · exact nativeChunk158
  · exact nativeChunk159
  · exact nativeChunk160
  · exact nativeChunk161

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
