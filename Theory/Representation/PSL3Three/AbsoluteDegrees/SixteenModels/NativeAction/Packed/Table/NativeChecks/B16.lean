module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 16

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk144 : ∀ i : Fin 81, NativeGood (⟨144 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk145 : ∀ i : Fin 81, NativeGood (⟨145 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk146 : ∀ i : Fin 81, NativeGood (⟨146 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk147 : ∀ i : Fin 81, NativeGood (⟨147 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk148 : ∀ i : Fin 81, NativeGood (⟨148 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk149 : ∀ i : Fin 81, NativeGood (⟨149 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk150 : ∀ i : Fin 81, NativeGood (⟨150 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk151 : ∀ i : Fin 81, NativeGood (⟨151 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk152 : ∀ i : Fin 81, NativeGood (⟨152 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock16 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(16 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk144
  · exact nativeChunk145
  · exact nativeChunk146
  · exact nativeChunk147
  · exact nativeChunk148
  · exact nativeChunk149
  · exact nativeChunk150
  · exact nativeChunk151
  · exact nativeChunk152

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
