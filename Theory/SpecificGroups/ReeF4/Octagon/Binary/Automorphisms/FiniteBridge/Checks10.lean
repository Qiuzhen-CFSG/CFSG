module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks09

/-! Checked line-tree rows 2560–2815;
each reduction covers at most 32 rows and uses the literal certified point table. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
private theorem block2560 : ∀ j : Fin 32, Valid ⟨2560+j.val, by omega⟩ := by
  decide +kernel
private theorem block2592 : ∀ j : Fin 32, Valid ⟨2592+j.val, by omega⟩ := by
  decide +kernel
private theorem block2624 : ∀ j : Fin 32, Valid ⟨2624+j.val, by omega⟩ := by
  decide +kernel
private theorem block2656 : ∀ j : Fin 32, Valid ⟨2656+j.val, by omega⟩ := by
  decide +kernel
private theorem block2688 : ∀ j : Fin 32, Valid ⟨2688+j.val, by omega⟩ := by
  decide +kernel
private theorem block2720 : ∀ j : Fin 32, Valid ⟨2720+j.val, by omega⟩ := by
  decide +kernel
private theorem block2752 : ∀ j : Fin 32, Valid ⟨2752+j.val, by omega⟩ := by
  decide +kernel
private theorem block2784 : ∀ j : Fin 32, Valid ⟨2784+j.val, by omega⟩ := by
  decide +kernel
theorem valid2560 : ∀ i : Fin 2925, 2560 ≤ i.val → i.val < 2816 → Valid i :=
  (interval_join (interval_join (interval_join (interval_of_block (by omega) block2560) (interval_of_block (by omega) block2592)) (interval_join (interval_of_block (by omega) block2624) (interval_of_block (by omega) block2656))) (interval_join (interval_join (interval_of_block (by omega) block2688) (interval_of_block (by omega) block2720)) (interval_join (interval_of_block (by omega) block2752) (interval_of_block (by omega) block2784))))
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
