module
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry.WordCertificate
/-! The short-word certificate verifies normalization and centralization of the
marked elementary eight, without an assumption about the two-core. -/
@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.SylowEnumeration
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

private theorem localGenerator_normalizes (i : Fin 5) :
    localGenerator i ∈ Subgroup.normalizer (elementary : Set M12) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  rw [elementary_eq_range] at hx ⊢
  obtain ⟨b,rfl⟩ := hx
  have h : ∀ i : Fin 5, ∀ b : ElementaryCoordinates,
      ∃ c : ElementaryCoordinates,
        elementaryEmbedding c = localGenerator i * elementaryEmbedding b *
          (localGenerator i)⁻¹ := by decide +kernel
  exact h i b

private theorem localWord_normalizes (w : List (Fin 5)) :
    localWord w ∈ Subgroup.normalizer (elementary : Set M12) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i is ih => exact Subgroup.mul_mem _ (localGenerator_normalizes i) ih

theorem word_normalizes_elementary (i : Fin 192) (b : ElementaryCoordinates) :
    ∃ c : ElementaryCoordinates,
      wordElement i * elementaryEmbedding b * (wordElement i)⁻¹ = elementaryEmbedding c := by
  have h := (Subgroup.mem_set_normalizer_iff.mp (localWord_normalizes
    (wordTable[i.val]'(by rw [wordTable_size]; exact i.isLt))) (elementaryEmbedding b)).mp
    (show elementaryEmbedding b ∈ elementary by rw [elementary_eq_range]; exact ⟨b,rfl⟩)
  rw [elementary_eq_range] at h
  obtain ⟨c,hc⟩ := h
  exact ⟨c,hc.symm⟩

theorem word_centralizer_elementary : ∀ i : Fin 192,
    let g := wordElement i
    g * z = z * g → g * v = v * g → g * third = third * g →
      ∃ c : ElementaryCoordinates, elementaryEmbedding c = g := by
  decide +kernel
end Sporadic.Mathieu.M12SmallPair.SylowEnumeration
