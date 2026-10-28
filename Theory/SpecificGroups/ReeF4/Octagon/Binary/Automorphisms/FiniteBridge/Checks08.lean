module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks07

/-! Checked line-tree rows 2048–2303;
each reduction covers at most 32 rows and uses the literal certified point table. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
private theorem block2048 : ∀ j : Fin 32, Valid ⟨2048+j.val, by omega⟩ := by
  decide +kernel
private theorem block2080 : ∀ j : Fin 32, Valid ⟨2080+j.val, by omega⟩ := by
  decide +kernel
private theorem block2112 : ∀ j : Fin 32, Valid ⟨2112+j.val, by omega⟩ := by
  decide +kernel
private theorem block2144 : ∀ j : Fin 32, Valid ⟨2144+j.val, by omega⟩ := by
  decide +kernel
private theorem block2176 : ∀ j : Fin 32, Valid ⟨2176+j.val, by omega⟩ := by
  decide +kernel
private theorem block2208 : ∀ j : Fin 32, Valid ⟨2208+j.val, by omega⟩ := by
  decide +kernel
private theorem block2240 : ∀ j : Fin 32, Valid ⟨2240+j.val, by omega⟩ := by
  decide +kernel
private theorem block2272 : ∀ j : Fin 32, Valid ⟨2272+j.val, by omega⟩ := by
  decide +kernel
theorem valid2048 : ∀ i : Fin 2925, 2048 ≤ i.val → i.val < 2304 → Valid i :=
  (interval_join (interval_join (interval_join (interval_of_block (by omega) block2048) (interval_of_block (by omega) block2080)) (interval_join (interval_of_block (by omega) block2112) (interval_of_block (by omega) block2144))) (interval_join (interval_join (interval_of_block (by omega) block2176) (interval_of_block (by omega) block2208)) (interval_join (interval_of_block (by omega) block2240) (interval_of_block (by omega) block2272))))
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
