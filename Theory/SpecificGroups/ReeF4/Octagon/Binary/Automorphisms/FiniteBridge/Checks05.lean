module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks04

/-! Checked line-tree rows 1280–1535;
each reduction covers at most 32 rows and uses the literal certified point table. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
private theorem block1280 : ∀ j : Fin 32, Valid ⟨1280+j.val, by omega⟩ := by
  decide +kernel
private theorem block1312 : ∀ j : Fin 32, Valid ⟨1312+j.val, by omega⟩ := by
  decide +kernel
private theorem block1344 : ∀ j : Fin 32, Valid ⟨1344+j.val, by omega⟩ := by
  decide +kernel
private theorem block1376 : ∀ j : Fin 32, Valid ⟨1376+j.val, by omega⟩ := by
  decide +kernel
private theorem block1408 : ∀ j : Fin 32, Valid ⟨1408+j.val, by omega⟩ := by
  decide +kernel
private theorem block1440 : ∀ j : Fin 32, Valid ⟨1440+j.val, by omega⟩ := by
  decide +kernel
private theorem block1472 : ∀ j : Fin 32, Valid ⟨1472+j.val, by omega⟩ := by
  decide +kernel
private theorem block1504 : ∀ j : Fin 32, Valid ⟨1504+j.val, by omega⟩ := by
  decide +kernel
theorem valid1280 : ∀ i : Fin 2925, 1280 ≤ i.val → i.val < 1536 → Valid i :=
  (interval_join (interval_join (interval_join (interval_of_block (by omega) block1280) (interval_of_block (by omega) block1312)) (interval_join (interval_of_block (by omega) block1344) (interval_of_block (by omega) block1376))) (interval_join (interval_join (interval_of_block (by omega) block1408) (interval_of_block (by omega) block1440)) (interval_join (interval_of_block (by omega) block1472) (interval_of_block (by omega) block1504))))
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
