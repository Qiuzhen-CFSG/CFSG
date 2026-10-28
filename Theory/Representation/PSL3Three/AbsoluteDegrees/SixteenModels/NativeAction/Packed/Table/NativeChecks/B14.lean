module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 14

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk126 : ∀ i : Fin 81, NativeGood (⟨126 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk127 : ∀ i : Fin 81, NativeGood (⟨127 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk128 : ∀ i : Fin 81, NativeGood (⟨128 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk129 : ∀ i : Fin 81, NativeGood (⟨129 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk130 : ∀ i : Fin 81, NativeGood (⟨130 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk131 : ∀ i : Fin 81, NativeGood (⟨131 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk132 : ∀ i : Fin 81, NativeGood (⟨132 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk133 : ∀ i : Fin 81, NativeGood (⟨133 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk134 : ∀ i : Fin 81, NativeGood (⟨134 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock14 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(14 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk126
  · exact nativeChunk127
  · exact nativeChunk128
  · exact nativeChunk129
  · exact nativeChunk130
  · exact nativeChunk131
  · exact nativeChunk132
  · exact nativeChunk133
  · exact nativeChunk134

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
