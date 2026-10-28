module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks08

/-! Checked line-tree rows 2304–2559;
each reduction covers at most 32 rows and uses the literal certified point table. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
private theorem block2304 : ∀ j : Fin 32, Valid ⟨2304+j.val, by omega⟩ := by
  decide +kernel
private theorem block2336 : ∀ j : Fin 32, Valid ⟨2336+j.val, by omega⟩ := by
  decide +kernel
private theorem block2368 : ∀ j : Fin 32, Valid ⟨2368+j.val, by omega⟩ := by
  decide +kernel
private theorem block2400 : ∀ j : Fin 32, Valid ⟨2400+j.val, by omega⟩ := by
  decide +kernel
private theorem block2432 : ∀ j : Fin 32, Valid ⟨2432+j.val, by omega⟩ := by
  decide +kernel
private theorem block2464 : ∀ j : Fin 32, Valid ⟨2464+j.val, by omega⟩ := by
  decide +kernel
private theorem block2496 : ∀ j : Fin 32, Valid ⟨2496+j.val, by omega⟩ := by
  decide +kernel
private theorem block2528 : ∀ j : Fin 32, Valid ⟨2528+j.val, by omega⟩ := by
  decide +kernel
theorem valid2304 : ∀ i : Fin 2925, 2304 ≤ i.val → i.val < 2560 → Valid i :=
  (interval_join (interval_join (interval_join (interval_of_block (by omega) block2304) (interval_of_block (by omega) block2336)) (interval_join (interval_of_block (by omega) block2368) (interval_of_block (by omega) block2400))) (interval_join (interval_join (interval_of_block (by omega) block2432) (interval_of_block (by omega) block2464)) (interval_join (interval_of_block (by omega) block2496) (interval_of_block (by omega) block2528))))
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
