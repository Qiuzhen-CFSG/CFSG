module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks05

/-! Checked line-tree rows 1536–1791;
each reduction covers at most 32 rows and uses the literal certified point table. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
private theorem block1536 : ∀ j : Fin 32, Valid ⟨1536+j.val, by omega⟩ := by
  decide +kernel
private theorem block1568 : ∀ j : Fin 32, Valid ⟨1568+j.val, by omega⟩ := by
  decide +kernel
private theorem block1600 : ∀ j : Fin 32, Valid ⟨1600+j.val, by omega⟩ := by
  decide +kernel
private theorem block1632 : ∀ j : Fin 32, Valid ⟨1632+j.val, by omega⟩ := by
  decide +kernel
private theorem block1664 : ∀ j : Fin 32, Valid ⟨1664+j.val, by omega⟩ := by
  decide +kernel
private theorem block1696 : ∀ j : Fin 32, Valid ⟨1696+j.val, by omega⟩ := by
  decide +kernel
private theorem block1728 : ∀ j : Fin 32, Valid ⟨1728+j.val, by omega⟩ := by
  decide +kernel
private theorem block1760 : ∀ j : Fin 32, Valid ⟨1760+j.val, by omega⟩ := by
  decide +kernel
theorem valid1536 : ∀ i : Fin 2925, 1536 ≤ i.val → i.val < 1792 → Valid i :=
  (interval_join (interval_join (interval_join (interval_of_block (by omega) block1536) (interval_of_block (by omega) block1568)) (interval_join (interval_of_block (by omega) block1600) (interval_of_block (by omega) block1632))) (interval_join (interval_join (interval_of_block (by omega) block1664) (interval_of_block (by omega) block1696)) (interval_join (interval_of_block (by omega) block1728) (interval_of_block (by omega) block1760))))
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
