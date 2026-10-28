module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.CheckSupport

/-! Checked line-tree rows 0–255;
each reduction covers at most 32 rows and uses the literal certified point table. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
private theorem block0000 : ∀ j : Fin 32, Valid ⟨0+j.val, by omega⟩ := by
  decide +kernel
private theorem block0032 : ∀ j : Fin 32, Valid ⟨32+j.val, by omega⟩ := by
  decide +kernel
private theorem block0064 : ∀ j : Fin 32, Valid ⟨64+j.val, by omega⟩ := by
  decide +kernel
private theorem block0096 : ∀ j : Fin 32, Valid ⟨96+j.val, by omega⟩ := by
  decide +kernel
private theorem block0128 : ∀ j : Fin 32, Valid ⟨128+j.val, by omega⟩ := by
  decide +kernel
private theorem block0160 : ∀ j : Fin 32, Valid ⟨160+j.val, by omega⟩ := by
  decide +kernel
private theorem block0192 : ∀ j : Fin 32, Valid ⟨192+j.val, by omega⟩ := by
  decide +kernel
private theorem block0224 : ∀ j : Fin 32, Valid ⟨224+j.val, by omega⟩ := by
  decide +kernel
theorem valid0000 : ∀ i : Fin 2925, 0 ≤ i.val → i.val < 256 → Valid i :=
  (interval_join (interval_join (interval_join (interval_of_block (by omega) block0000) (interval_of_block (by omega) block0032)) (interval_join (interval_of_block (by omega) block0064) (interval_of_block (by omega) block0096))) (interval_join (interval_join (interval_of_block (by omega) block0128) (interval_of_block (by omega) block0160)) (interval_join (interval_of_block (by omega) block0192) (interval_of_block (by omega) block0224))))
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
