module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks01

/-! Checked line-tree rows 512–767;
each reduction covers at most 32 rows and uses the literal certified point table. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
private theorem block0512 : ∀ j : Fin 32, Valid ⟨512+j.val, by omega⟩ := by
  decide +kernel
private theorem block0544 : ∀ j : Fin 32, Valid ⟨544+j.val, by omega⟩ := by
  decide +kernel
private theorem block0576 : ∀ j : Fin 32, Valid ⟨576+j.val, by omega⟩ := by
  decide +kernel
private theorem block0608 : ∀ j : Fin 32, Valid ⟨608+j.val, by omega⟩ := by
  decide +kernel
private theorem block0640 : ∀ j : Fin 32, Valid ⟨640+j.val, by omega⟩ := by
  decide +kernel
private theorem block0672 : ∀ j : Fin 32, Valid ⟨672+j.val, by omega⟩ := by
  decide +kernel
private theorem block0704 : ∀ j : Fin 32, Valid ⟨704+j.val, by omega⟩ := by
  decide +kernel
private theorem block0736 : ∀ j : Fin 32, Valid ⟨736+j.val, by omega⟩ := by
  decide +kernel
theorem valid0512 : ∀ i : Fin 2925, 512 ≤ i.val → i.val < 768 → Valid i :=
  (interval_join (interval_join (interval_join (interval_of_block (by omega) block0512) (interval_of_block (by omega) block0544)) (interval_join (interval_of_block (by omega) block0576) (interval_of_block (by omega) block0608))) (interval_join (interval_join (interval_of_block (by omega) block0640) (interval_of_block (by omega) block0672)) (interval_join (interval_of_block (by omega) block0704) (interval_of_block (by omega) block0736))))
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
