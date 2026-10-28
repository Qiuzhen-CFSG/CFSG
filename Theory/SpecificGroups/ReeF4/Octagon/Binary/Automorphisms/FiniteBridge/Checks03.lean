module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks02

/-! Checked line-tree rows 768–1023;
each reduction covers at most 32 rows and uses the literal certified point table. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
private theorem block0768 : ∀ j : Fin 32, Valid ⟨768+j.val, by omega⟩ := by
  decide +kernel
private theorem block0800 : ∀ j : Fin 32, Valid ⟨800+j.val, by omega⟩ := by
  decide +kernel
private theorem block0832 : ∀ j : Fin 32, Valid ⟨832+j.val, by omega⟩ := by
  decide +kernel
private theorem block0864 : ∀ j : Fin 32, Valid ⟨864+j.val, by omega⟩ := by
  decide +kernel
private theorem block0896 : ∀ j : Fin 32, Valid ⟨896+j.val, by omega⟩ := by
  decide +kernel
private theorem block0928 : ∀ j : Fin 32, Valid ⟨928+j.val, by omega⟩ := by
  decide +kernel
private theorem block0960 : ∀ j : Fin 32, Valid ⟨960+j.val, by omega⟩ := by
  decide +kernel
private theorem block0992 : ∀ j : Fin 32, Valid ⟨992+j.val, by omega⟩ := by
  decide +kernel
theorem valid0768 : ∀ i : Fin 2925, 768 ≤ i.val → i.val < 1024 → Valid i :=
  (interval_join (interval_join (interval_join (interval_of_block (by omega) block0768) (interval_of_block (by omega) block0800)) (interval_join (interval_of_block (by omega) block0832) (interval_of_block (by omega) block0864))) (interval_join (interval_join (interval_of_block (by omega) block0896) (interval_of_block (by omega) block0928)) (interval_join (interval_of_block (by omega) block0960) (interval_of_block (by omega) block0992))))
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
