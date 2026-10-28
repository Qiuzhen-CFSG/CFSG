module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 10

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk90 : ∀ i : Fin 81, NativeGood (⟨90 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk91 : ∀ i : Fin 81, NativeGood (⟨91 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk92 : ∀ i : Fin 81, NativeGood (⟨92 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk93 : ∀ i : Fin 81, NativeGood (⟨93 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk94 : ∀ i : Fin 81, NativeGood (⟨94 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk95 : ∀ i : Fin 81, NativeGood (⟨95 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk96 : ∀ i : Fin 81, NativeGood (⟨96 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk97 : ∀ i : Fin 81, NativeGood (⟨97 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk98 : ∀ i : Fin 81, NativeGood (⟨98 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock10 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(10 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk90
  · exact nativeChunk91
  · exact nativeChunk92
  · exact nativeChunk93
  · exact nativeChunk94
  · exact nativeChunk95
  · exact nativeChunk96
  · exact nativeChunk97
  · exact nativeChunk98

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
