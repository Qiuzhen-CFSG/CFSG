module

public import Theory.Mathieu.M11.WittUniqueness
public import Theory.Mathieu.M12.Recognition.WittUniqueness.Coordinates
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Theory.GroupTheory.SteinerSystem.Transport

/-!
# Normalizing the derived eleven-point Witt design

Remove point `0` from every block containing it and use explicit point
coordinates to label the remaining points by `Fin 11`. The resulting system is
`S(4,5,11)`, so small Witt uniqueness supplies a permutation. Extending that
permutation while fixing `0` normalizes all 66 blocks through `0`.

This is the geometric extension step used for degree-twelve recognition in
Aschbacher, *Sporadic Groups*, Exercise 6.6(6–7), printed p. 95, cited by
*A 2-local characterization of M12*, Lemma 4.11. No invariance hypothesis is
needed for this normalization.
-/

open Theory.GroupTheory
open scoped Pointwise
namespace Sporadic.Mathieu.M12WittUniqueness

private abbrev emb := pointEmbedding
private def augment (B : Finset (Fin 11)) : Finset (Fin 12) := insert 0 (B.map emb)

private theorem emb_ne_zero (x : Fin 11) : emb x ≠ 0 :=
  pointEmbedding_ne_zero x

private theorem emb_surj (x : Fin 12) (hx : x ≠ 0) : ∃ y, emb y = x :=
  pointEmbedding_surjective x hx

private theorem zero_not_map (B : Finset (Fin 11)) : (0 : Fin 12) ∉ B.map emb := by
  simp only [Finset.mem_map]
  rintro ⟨x, _, hx⟩
  exact emb_ne_zero x hx

private theorem augment_card (B : Finset (Fin 11)) : (augment B).card = B.card + 1 := by
  rw [augment, Finset.card_insert_of_notMem (zero_not_map B), Finset.card_map]

private theorem emb_mem_augment (B : Finset (Fin 11)) (x : Fin 11) :
    emb x ∈ augment B ↔ x ∈ B := by
  simp [augment, emb_ne_zero]

private theorem augment_subset_iff (B C : Finset (Fin 11)) :
    augment B ⊆ augment C ↔ B ⊆ C := by
  constructor
  · intro h x hx
    exact (emb_mem_augment C x).mp (h ((emb_mem_augment B x).mpr hx))
  · intro h
    exact Finset.insert_subset_insert _ (Finset.map_subset_map.mpr h)

private theorem augment_injective : Function.Injective augment := by
  intro B C h
  apply Finset.Subset.antisymm
  · exact (augment_subset_iff B C).mp (Finset.subset_of_eq h)
  · exact (augment_subset_iff C B).mp (Finset.subset_of_eq h.symm)

private def restrict (B : Finset (Fin 12)) : Finset (Fin 11) :=
  Finset.univ.filter (fun x => emb x ∈ B)

private theorem augment_restrict (B : Finset (Fin 12)) (hB : 0 ∈ B) :
    augment (restrict B) = B := by
  ext x
  by_cases hx : x = 0
  · subst x
    simp [augment, hB]
  · obtain ⟨y, rfl⟩ := emb_surj x hx
    simp [emb_mem_augment, restrict]

private def derived (D : SteinerSystem (Fin 12) 5 6) : SteinerSystem (Fin 11) 4 5 where
  blocks := Finset.univ.filter (fun B => augment B ∈ D.blocks)
  block_card := by
    intro B hB
    have h := D.block_card _ (Finset.mem_filter.mp hB).2
    rw [augment_card] at h
    omega
  steiner := by
    intro S hS
    obtain ⟨B, ⟨hB, hSB⟩, huniq⟩ := D.existsUnique_block (augment S) (by
      rw [augment_card, hS])
    have hzero : 0 ∈ B := hSB (Finset.mem_insert_self _ _)
    have hrestore := augment_restrict B hzero
    apply Finset.card_eq_one_iff_existsUnique.mpr
    refine ⟨restrict B, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rwa [hrestore], (augment_subset_iff _ _).mp (by rwa [hrestore])⟩
    · intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
      apply augment_injective
      rw [hrestore]
      exact huniq _ ⟨hC.1, (augment_subset_iff _ _).mpr hC.2⟩

private theorem augment_smul (e : Equiv.Perm (Fin 11)) (B : Finset (Fin 11)) :
    (e.viaEmbedding emb) • augment B = augment (e • B) := by
  have hfix : e.viaEmbedding emb 0 = 0 := by
    apply Equiv.Perm.viaEmbedding_apply_of_notMem
    rintro ⟨x, hx⟩
    exact emb_ne_zero x hx
  rw [augment, Finset.smul_finset_insert]
  change insert (e.viaEmbedding emb 0) ((e.viaEmbedding emb) • B.map emb) = _
  rw [hfix]
  congr 1
  ext x
  simp only [Finset.mem_smul_finset, Finset.mem_map, Equiv.Perm.smul_def]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨e y, ⟨y, hy, rfl⟩, (Equiv.Perm.viaEmbedding_apply _ _ _).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨emb y, ⟨y, hy, rfl⟩, Equiv.Perm.viaEmbedding_apply _ _ _⟩

/-- Every twelve-point Witt design can be relabeled so that its blocks through
zero include all augmented blocks of the concrete eleven-point Witt design. -/
public theorem exists_relabel_augmented (D : SteinerSystem (Fin 12) 5 6) :
    ∃ e : Equiv.Perm (Fin 12), ∀ B ∈ m11Blocks,
      insert 0 (B.map pointEmbedding) ∈ (D.relabel e).blocks := by
  obtain ⟨e, he⟩ := m11WittDesign_unique (derived D)
  have he' : e • (derived D).blocks = m11Blocks := by
    apply Finset.coe_injective
    simpa only [Finset.coe_smul_finset, m11WittDesign_blocks] using he
  refine ⟨e.viaEmbedding emb, ?_⟩
  intro B hB
  rw [← he'] at hB
  obtain ⟨C, hC, rfl⟩ := Finset.mem_smul_finset.mp hB
  change augment (e • C) ∈ (D.relabel (e.viaEmbedding emb)).blocks
  rw [← augment_smul]
  apply Finset.smul_mem_smul_finset
  exact (Finset.mem_filter.mp hC).2

end Sporadic.Mathieu.M12WittUniqueness
