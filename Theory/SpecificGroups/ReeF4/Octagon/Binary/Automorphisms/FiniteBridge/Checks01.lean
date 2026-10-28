module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks00

/-! Checked line-tree rows 256–511;
each reduction covers at most 32 rows and uses the literal certified point table. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
private theorem block0256 : ∀ j : Fin 32, Valid ⟨256+j.val, by omega⟩ := by
  decide +kernel
private theorem block0288 : ∀ j : Fin 32, Valid ⟨288+j.val, by omega⟩ := by
  decide +kernel
private theorem block0320 : ∀ j : Fin 32, Valid ⟨320+j.val, by omega⟩ := by
  decide +kernel
private theorem block0352 : ∀ j : Fin 32, Valid ⟨352+j.val, by omega⟩ := by
  decide +kernel
private theorem block0384 : ∀ j : Fin 32, Valid ⟨384+j.val, by omega⟩ := by
  decide +kernel
private theorem block0416 : ∀ j : Fin 32, Valid ⟨416+j.val, by omega⟩ := by
  decide +kernel
private theorem block0448 : ∀ j : Fin 32, Valid ⟨448+j.val, by omega⟩ := by
  decide +kernel
private theorem block0480 : ∀ j : Fin 32, Valid ⟨480+j.val, by omega⟩ := by
  decide +kernel
theorem valid0256 : ∀ i : Fin 2925, 256 ≤ i.val → i.val < 512 → Valid i :=
  (interval_join (interval_join (interval_join (interval_of_block (by omega) block0256) (interval_of_block (by omega) block0288)) (interval_join (interval_of_block (by omega) block0320) (interval_of_block (by omega) block0352))) (interval_join (interval_join (interval_of_block (by omega) block0384) (interval_of_block (by omega) block0416)) (interval_join (interval_of_block (by omega) block0448) (interval_of_block (by omega) block0480))))
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
