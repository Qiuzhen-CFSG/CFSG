module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks03

/-! Checked line-tree rows 1024–1279;
each reduction covers at most 32 rows and uses the literal certified point table. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
private theorem block1024 : ∀ j : Fin 32, Valid ⟨1024+j.val, by omega⟩ := by
  decide +kernel
private theorem block1056 : ∀ j : Fin 32, Valid ⟨1056+j.val, by omega⟩ := by
  decide +kernel
private theorem block1088 : ∀ j : Fin 32, Valid ⟨1088+j.val, by omega⟩ := by
  decide +kernel
private theorem block1120 : ∀ j : Fin 32, Valid ⟨1120+j.val, by omega⟩ := by
  decide +kernel
private theorem block1152 : ∀ j : Fin 32, Valid ⟨1152+j.val, by omega⟩ := by
  decide +kernel
private theorem block1184 : ∀ j : Fin 32, Valid ⟨1184+j.val, by omega⟩ := by
  decide +kernel
private theorem block1216 : ∀ j : Fin 32, Valid ⟨1216+j.val, by omega⟩ := by
  decide +kernel
private theorem block1248 : ∀ j : Fin 32, Valid ⟨1248+j.val, by omega⟩ := by
  decide +kernel
theorem valid1024 : ∀ i : Fin 2925, 1024 ≤ i.val → i.val < 1280 → Valid i :=
  (interval_join (interval_join (interval_join (interval_of_block (by omega) block1024) (interval_of_block (by omega) block1056)) (interval_join (interval_of_block (by omega) block1088) (interval_of_block (by omega) block1120))) (interval_join (interval_join (interval_of_block (by omega) block1152) (interval_of_block (by omega) block1184)) (interval_join (interval_of_block (by omega) block1216) (interval_of_block (by omega) block1248))))
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
