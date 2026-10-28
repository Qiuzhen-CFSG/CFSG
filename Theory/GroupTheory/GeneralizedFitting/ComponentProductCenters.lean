module

public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# Centers in a semisimple group and a commuting product

The embedded center of a component centralizes every component, hence is
central when the layer generates the group. For two commuting subgroups
which generate the group, decomposing a central element into its two
factors proves that the center is the product of the embedded factor
centers. These literal inclusions retain the subgroup maps.

Source: the central-product calculation in Aschbacher–Smith A.2.11–12,
printed pp.35–37.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem IsComponent.center_map_le_center_of_semisimple
    (hG : componentLayer G = ⊤) {L : Subgroup G} (hL : IsComponent G L) :
    (center L).map L.subtype ≤ center G := by
  have hc : componentLayer G ≤ centralizer ((center L).map L.subtype : Set G) := by
    apply sSup_le
    intro C hC
    by_cases he : C = L
    · subst C
      intro x hx
      apply mem_centralizer_iff.mpr
      rintro y ⟨z, hz, rfl⟩
      exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩)).symm
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (hC.commutator_eq_bot_of_ne hL he)).trans (centralizer_le (map_subtype_le _))
  rw [hG] at hc
  simpa only [coe_top, centralizer_univ] using le_centralizer_iff.mp hc

theorem center_eq_sup_center_of_commuting (A B : Subgroup G)
    (hc : A ≤ centralizer (B : Set G)) (hg : A ⊔ B = ⊤) :
    center G = (center A).map A.subtype ⊔ (center B).map B.subtype := by
  have hc' : B ≤ centralizer (A : Set G) := le_centralizer_iff.mp hc
  have hBN : B.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hg]
    exact sup_le (hc.trans (centralizer_le_normalizer _)) B.le_normalizer
  let := hBN
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.mp (hg ▸ mem_top x)
    have haC : a ∈ centralizer (A : Set G) :=
      (centralizer (A : Set G)).mul_mem_cancel_right (hc' hb) |>.mp
        ((center_le_centralizer (A : Set G)) hx)
    have hbC : b ∈ centralizer (B : Set G) :=
      (centralizer (B : Set G)).mul_mem_cancel_left (hc ha) |>.mp
        ((center_le_centralizer (B : Set G)) hx)
    apply mul_mem
    · apply mem_sup_left
      exact ⟨⟨a, ha⟩, mem_center_iff.mpr (fun c => Subtype.ext (haC c c.property)), rfl⟩
    · apply mem_sup_right
      exact ⟨⟨b, hb⟩, mem_center_iff.mpr (fun c => Subtype.ext (hbC c c.property)), rfl⟩
  · apply sup_le
    · rintro x ⟨a, ha, rfl⟩
      have hcentral : A ⊔ B ≤ centralizer ({(a : G)} : Set G) := by
        apply sup_le
        · intro y hy
          simp only [mem_centralizer_singleton_iff]
          exact (congrArg Subtype.val (mem_center_iff.mp ha ⟨y, hy⟩))
        · intro y hy
          simp only [mem_centralizer_singleton_iff]
          exact hc a.property y hy
      rw [hg] at hcentral
      apply mem_center_iff.mpr
      intro y
      exact (mem_centralizer_singleton_iff.mp (hcentral trivial))
    · rintro x ⟨b, hb, rfl⟩
      have hcentral : A ⊔ B ≤ centralizer ({(b : G)} : Set G) := by
        apply sup_le
        · intro y hy
          simp only [mem_centralizer_singleton_iff]
          exact hc' b.property y hy
        · intro y hy
          simp only [mem_centralizer_singleton_iff]
          exact (congrArg Subtype.val (mem_center_iff.mp hb ⟨y, hy⟩))
      rw [hg] at hcentral
      apply mem_center_iff.mpr
      intro y
      exact (mem_centralizer_singleton_iff.mp (hcentral trivial))
end Theory.GroupTheory
