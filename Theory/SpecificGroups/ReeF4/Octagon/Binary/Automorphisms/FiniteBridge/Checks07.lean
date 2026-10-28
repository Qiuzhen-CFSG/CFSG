module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks06

/-! Checked line-tree rows 1792–2047;
each reduction covers at most 32 rows and uses the literal certified point table. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
private theorem block1792 : ∀ j : Fin 32, Valid ⟨1792+j.val, by omega⟩ := by
  decide +kernel
private theorem block1824 : ∀ j : Fin 32, Valid ⟨1824+j.val, by omega⟩ := by
  decide +kernel
private theorem block1856 : ∀ j : Fin 32, Valid ⟨1856+j.val, by omega⟩ := by
  decide +kernel
private theorem block1888 : ∀ j : Fin 32, Valid ⟨1888+j.val, by omega⟩ := by
  decide +kernel
private theorem block1920 : ∀ j : Fin 32, Valid ⟨1920+j.val, by omega⟩ := by
  decide +kernel
private theorem block1952 : ∀ j : Fin 32, Valid ⟨1952+j.val, by omega⟩ := by
  decide +kernel
private theorem block1984 : ∀ j : Fin 32, Valid ⟨1984+j.val, by omega⟩ := by
  decide +kernel
private theorem block2016 : ∀ j : Fin 32, Valid ⟨2016+j.val, by omega⟩ := by
  decide +kernel
theorem valid1792 : ∀ i : Fin 2925, 1792 ≤ i.val → i.val < 2048 → Valid i :=
  (interval_join (interval_join (interval_join (interval_of_block (by omega) block1792) (interval_of_block (by omega) block1824)) (interval_join (interval_of_block (by omega) block1856) (interval_of_block (by omega) block1888))) (interval_join (interval_join (interval_of_block (by omega) block1920) (interval_of_block (by omega) block1952)) (interval_join (interval_of_block (by omega) block1984) (interval_of_block (by omega) block2016))))
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
