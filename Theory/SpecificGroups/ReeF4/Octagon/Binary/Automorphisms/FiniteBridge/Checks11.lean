module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks10

/-! Checked line-tree rows 2816–2924;
each reduction covers at most 32 rows and uses the literal certified point table. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
private theorem block2816 : ∀ j : Fin 32, Valid ⟨2816+j.val, by omega⟩ := by
  decide +kernel
private theorem block2848 : ∀ j : Fin 32, Valid ⟨2848+j.val, by omega⟩ := by
  decide +kernel
private theorem block2880 : ∀ j : Fin 32, Valid ⟨2880+j.val, by omega⟩ := by
  decide +kernel
private theorem block2912 : ∀ j : Fin 13, Valid ⟨2912+j.val, by omega⟩ := by
  decide +kernel
theorem valid2816 : ∀ i : Fin 2925, 2816 ≤ i.val → i.val < 2925 → Valid i :=
  (interval_join (interval_join (interval_of_block (by omega) block2816) (interval_of_block (by omega) block2848)) (interval_join (interval_of_block (by omega) block2880) (interval_of_block (by omega) block2912)))
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
