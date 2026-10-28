module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 6

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk54 : ∀ i : Fin 81, NativeGood (⟨54 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk55 : ∀ i : Fin 81, NativeGood (⟨55 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk56 : ∀ i : Fin 81, NativeGood (⟨56 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk57 : ∀ i : Fin 81, NativeGood (⟨57 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk58 : ∀ i : Fin 81, NativeGood (⟨58 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk59 : ∀ i : Fin 81, NativeGood (⟨59 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk60 : ∀ i : Fin 81, NativeGood (⟨60 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk61 : ∀ i : Fin 81, NativeGood (⟨61 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk62 : ∀ i : Fin 81, NativeGood (⟨62 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock6 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(6 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk54
  · exact nativeChunk55
  · exact nativeChunk56
  · exact nativeChunk57
  · exact nativeChunk58
  · exact nativeChunk59
  · exact nativeChunk60
  · exact nativeChunk61
  · exact nativeChunk62

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
