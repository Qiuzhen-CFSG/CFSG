module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData

/-! Interval assembly for the kernel-checked finite line-tree certificate. -/
public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
theorem interval_join {lo mid hi : ℕ}
    (left : ∀ i : Fin 2925, lo ≤ i.val → i.val < mid → Valid i)
    (right : ∀ i : Fin 2925, mid ≤ i.val → i.val < hi → Valid i) :
    ∀ i : Fin 2925, lo ≤ i.val → i.val < hi → Valid i := by
  intro i hlo hhi
  by_cases hm : i.val < mid
  · exact left i hlo hm
  · exact right i (by omega) hhi

theorem interval_of_block {lo n : ℕ} (hn : lo+n ≤ 2925)
    (h : ∀ j : Fin n, Valid ⟨lo+j.val, by omega⟩) :
    ∀ i : Fin 2925, lo ≤ i.val → i.val < lo+n → Valid i := by
  intro i hlo hhi
  have hh := h ⟨i.val-lo, by omega⟩
  convert hh using 1
  apply Fin.ext
  change i.val = lo+(i.val-lo)
  omega
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData
