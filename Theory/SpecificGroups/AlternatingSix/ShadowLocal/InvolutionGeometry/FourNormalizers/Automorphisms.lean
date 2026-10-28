module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.Geometry
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The marked four-group normalizer in Aut(A₆)

Natural permutations normalize the marked four-group exactly when they commute
with (56). The exceptional automorphism exchanges the two four-group classes,
so no automorphism outside the natural S₆ normalizes this four-group. Parity
then splits its full normalizer into its inner A₆ normalizer and the commuting
outer involution induced by (56), with trivial intersection.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, printed pp.567–570.
-/

@[expose] public section

open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal.FourNormalizers
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 4096

theorem inner_map_transport (F : Subgroup A6) (α : AutA6) :
    (F.map (MulAut.conj : A6 →* AutA6)).map (MulAut.conj α).toMonoidHom =
      (F.map α.toMonoidHom).map (MulAut.conj : A6 →* AutA6) := by
  rw [map_map, map_map]
  congr 1
  ext a x
  simp

theorem mem_inner_normalizer_iff (F : Subgroup A6) (β : AutA6) :
    β ∈ normalizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6) ↔
      F.map β.toMonoidHom = F := by
  rw [mem_normalizer_iff_map_conj_eq]
  change (F.map (MulAut.conj : A6 →* AutA6)).map (MulAut.conj β).toMonoidHom = _ ↔ _
  rw [inner_map_transport]
  exact (Subgroup.map_injective inner_injective).eq_iff

private theorem no_natural_class_swap (σ : Equiv.Perm (Fin 6)) :
    standardFour.map (permutationAction σ).toMonoidHom ≠ secondFour := by
  intro h
  have he (i : V) : ∃ j : V, secondEmbedding j = permutationAction σ (standardEmbedding i) := by
    change permutationAction σ (standardEmbedding i) ∈ secondFour
    rw [← h]
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  have table : ∀ σ : Equiv.Perm (Fin 6), ¬ ∀ i : V, ∃ j : V,
      (secondEmbedding j).val = σ * (standardEmbedding i).val * σ⁻¹ := by decide +kernel
  apply table σ
  intro i
  obtain ⟨j, hj⟩ := he i
  exact ⟨j, congrArg Subtype.val hj⟩

theorem classSwap_not_natural : classSwap ∉ natural := by
  rintro ⟨σ, hσ⟩
  apply no_natural_class_swap σ
  change permutationAction σ = classSwap at hσ
  rw [hσ, classSwap_standardFour]

theorem standard_stabilizer_le_natural (β : AutA6)
    (hβ : standardFour.map β.toMonoidHom = standardFour) : β ∈ natural := by
  by_contra hn
  have hm : classSwap * β⁻¹ ∈ natural := by
    rw [Subgroup.mul_mem_iff_of_index_two naturalAlternatingAutomorphismSubgroup_index]
    simp [classSwap_not_natural, hn]
  obtain ⟨σ, hσ⟩ := hm
  change permutationAction σ = classSwap * β⁻¹ at hσ
  have hβi : standardFour.map β.symm.toMonoidHom = standardFour :=
    (map_symm_eq_iff_map_eq standardFour (e := β)).mpr hβ
  apply no_natural_class_swap σ
  rw [hσ]
  change standardFour.map (classSwap.toMonoidHom.comp β.symm.toMonoidHom) = secondFour
  rw [← map_map, hβi, classSwap_standardFour]

theorem tailSwap_order : orderOf (permutationAction tailSwap) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow]
    have h : tailSwap ^ 2 = 1 := by decide +kernel
    rw [h, map_one]
  · intro h
    have he := permutationAction_injective (h.trans (map_one permutationAction).symm)
    exact (by decide +kernel : tailSwap ≠ 1) he

theorem tailSwap_not_inner : permutationAction tailSwap ∉ inner := by
  rintro ⟨g, hg⟩
  have he : g.val = tailSwap := permutationAction_injective ((permutationAction_coe g).trans hg)
  have hg' := g.property
  rw [he] at hg'
  exact (by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel : tailSwap ∉ alternatingGroup (Fin 6)) hg'

theorem tailSwap_fixes_normalizer (g : A6) (hg : g ∈ normalizer (standardFour : Set A6)) :
    permutationAction tailSwap g = g := by
  rwa [standard_normalizer_eq_fixed] at hg

private theorem natural_normalizer_decomposition (σ : Equiv.Perm (Fin 6))
    (hσ : σ * tailSwap = tailSwap * σ) :
    ∃ g : A6, g.val * tailSwap = tailSwap * g.val ∧
      (σ = g.val ∨ σ = g.val * tailSwap) := by
  have heven : σ ∈ alternatingGroup (Fin 6) ∨ σ * tailSwap ∈ alternatingGroup (Fin 6) := by
    simp only [Equiv.Perm.mem_alternatingGroup]
    revert σ
    decide +kernel
  rcases heven with h | h
  · exact ⟨⟨σ, h⟩, hσ, Or.inl rfl⟩
  · refine ⟨⟨σ * tailSwap, h⟩, ?_, Or.inr ?_⟩
    · change (σ * tailSwap) * tailSwap = tailSwap * (σ * tailSwap)
      rw [← mul_assoc tailSwap, ← hσ]
    · change σ = (σ * tailSwap) * tailSwap
      have ht : tailSwap * tailSwap = 1 := by decide +kernel
      rw [mul_assoc, ht, mul_one]

theorem standard_aut_normalizer_eq :
    normalizer (standardFour.map (MulAut.conj : A6 →* AutA6) : Set AutA6) =
      (normalizer (standardFour : Set A6)).map (MulAut.conj : A6 →* AutA6) ⊔
        zpowers (permutationAction tailSwap) := by
  apply le_antisymm
  · intro β hβ
    have hstab := (mem_inner_normalizer_iff standardFour β).mp hβ
    obtain ⟨σ, hσ⟩ := standard_stabilizer_le_natural β hstab
    change permutationAction σ = β at hσ
    subst β
    have hc := (natural_stabilizes_standard_iff σ).mp hstab
    obtain ⟨g, hg, h | h⟩ := natural_normalizer_decomposition σ hc
    have hgN : g ∈ normalizer (standardFour : Set A6) := by
      rw [mem_normalizer_iff_map_conj_eq, ← permutationAction_coe g]
      exact (natural_stabilizes_standard_iff _).mpr hg
    · rw [h, permutationAction_coe]
      exact mem_sup_left ⟨g, hgN, rfl⟩
    · have hgN : g ∈ normalizer (standardFour : Set A6) := by
        rw [mem_normalizer_iff_map_conj_eq, ← permutationAction_coe g]
        exact (natural_stabilizes_standard_iff _).mpr hg
      rw [h, map_mul, permutationAction_coe]
      apply Subgroup.mul_mem
      · exact mem_sup_left ⟨g, hgN, rfl⟩
      · exact mem_sup_right (mem_zpowers _)
  · apply sup_le
    · exact (standardFour.le_normalizer_map (MulAut.conj : A6 →* AutA6))
    · apply zpowers_le.mpr
      rw [mem_inner_normalizer_iff, natural_stabilizes_standard_iff]

private theorem mem_zpowers_two {G : Type*} [Group G] [Finite G]
    {t x : G} (ht : orderOf t = 2) : x ∈ zpowers t ↔ x = 1 ∨ x = t := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ht]
  constructor
  · intro hw
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
    · exact Finset.mem_image.mpr ⟨1, by simp, by simp⟩

theorem standard_complement_disjoint :
    Disjoint ((normalizer (standardFour : Set A6)).map (MulAut.conj : A6 →* AutA6))
      (zpowers (permutationAction tailSwap)) := by
  rw [Subgroup.disjoint_def]
  intro β hβ hz
  rcases (mem_zpowers_two tailSwap_order).mp hz with h | h
  · exact h
  · subst β
    exact (tailSwap_not_inner (map_le_range _ _ hβ)).elim

theorem standard_complement_centralizes :
    (normalizer (standardFour : Set A6)).map (MulAut.conj : A6 →* AutA6) ≤
      centralizer (zpowers (permutationAction tailSwap) : Set AutA6) := by
  rintro _ ⟨g, hg, rfl⟩
  intro z hz
  rcases (mem_zpowers_two tailSwap_order).mp hz with rfl | rfl
  · simp
  · have h := aut_conj_inner (permutationAction tailSwap) g
    rw [tailSwap_fixes_normalizer g hg, mul_inv_eq_iff_eq_mul] at h
    exact h
end AlternatingSix.ShadowLocal.FourNormalizers
