module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeQuotient

/-!
# Exact root products in the arbitrary-degree small-mover family

An order-q, index-q actor is a full transvection root. The join of two
such roots is itself a small mover. If the maximum-small-mover join is
contained in their product, maximality therefore identifies its entire
image with that root join. Kernel saturation lifts the equality to the
original groups, including all central attachments.

This supplies the literal root configuration preceding the rank-one
construction in MS93 (5.1), printed p.913. The actual replacement consumer
is NonbinarySymplectic.CriticalReduction.RootProductGeometry.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

theorem eq_rootFamily_of_field_indices (E : Subgroup (unipotent (F := F)))
    (hc : Nat.card E = Nat.card F) (hm : movingIndex E = Nat.card F) :
    ∃ s : Option F, E = rootFamily s := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqq : Nat.card F < Nat.card F ^ 2 := by nlinarith
  have hs : Small E := ⟨by omega,by omega⟩
  rcases small_classification E hs with hbot | hroot | ⟨_,hlarge⟩ | ⟨l,he⟩
  · rw [hbot,card_bot] at hc
    omega
  · exact hroot
  · omega
  · rw [he,card_finitePlane] at hc
    omega

theorem small_rootFamily_sup (s t : Option F) : Small (rootFamily s ⊔ rootFamily t) := by
  by_cases he : s = t
  · subst t
    rw [sup_idem]
    exact ⟨by rw [movingIndex_rootFamily,card_rootFamily],by
      rw [movingIndex_rootFamily]
      exact Nat.le_self_pow (by decide) _⟩
  · exact small_of_le_wing_of_large _
      (sup_le (rootFamily_le_wing s) (rootFamily_le_wing t)) (rootFamily_sup_card he).ge

theorem join_eq_root_sup_of_subset_product
    (T A B : Subgroup (unipotent (F := F))) (hAT : A ≤ T) (hBT : B ≤ T)
    (hAc : Nat.card A = Nat.card F) (hAm : movingIndex A = Nat.card F)
    (hBc : Nat.card B = Nat.card F) (hBm : movingIndex B = Nat.card F)
    (hp : (join T : Set (unipotent (F := F))) ⊆ (A : Set _) * (B : Set _)) :
    ∃ s t : Option F, A = rootFamily s ∧ B = rootFamily t ∧ join T = A ⊔ B := by
  obtain ⟨s,hs⟩ := eq_rootFamily_of_field_indices A hAc hAm
  obtain ⟨t,ht⟩ := eq_rootFamily_of_field_indices B hBc hBm
  have hsmall : Small (A ⊔ B) := by rw [hs,ht]; exact small_rootFamily_sup s t
  have hle : join T ≤ A ⊔ B := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hp hx
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
  obtain ⟨E,hE⟩ := maximal_nonempty T
  have hEE : E = A ⊔ B := maximal_eq_of_le hE (sup_le hAT hBT) hsmall
    ((le_sSup hE).trans hle)
  exact ⟨s,t,hs,ht,le_antisymm hle (hEE ▸ le_sSup hE)⟩

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree

namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree.Quotient
variable {F G D : Type*} [Field F] [CharP F 2] [Finite F]
  [Group G] [Finite G] [Group D]
variable (U T : Subgroup G) (q : G →* D) (i : unipotent (F := F) →* D)
  (hi : Function.Injective i)
  (hkT : q.ker ≤ T) (hUT : U ≤ centralizer (q.ker : Set G))
  (hTi : T.map q ≤ i.range)
  (hindex : ∀ E : Subgroup G, E ≤ T →
    (centralizer (E : Set G)).relIndex U = movingIndex (coordinates q i E))

include hi hkT hUT hTi hindex in
theorem root_product_join_eq
    (A B : Subgroup G) (hAT : A ≤ T) (hBT : B ≤ T)
    (hAc : q.ker.relIndex A = Nat.card F)
    (hAm : (centralizer (A : Set G)).relIndex U = Nat.card F)
    (hBc : q.ker.relIndex B = Nat.card F)
    (hBm : (centralizer (B : Set G)).relIndex U = Nat.card F)
    (hp : (Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2) : Set G) ⊆
      (A : Set G) * (B : Set G)) :
    ∃ s t : Option F,
      coordinates q i A = rootFamily s ∧ coordinates q i B = rootFamily t ∧
      coordinates q i (Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2)) =
        rootFamily s ⊔ rootFamily t ∧
      Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2) = A ⊔ B := by
  let J := Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2)
  have hj := coordinates_join U T q i hi hkT hUT hTi hindex
  have hAi := (map_mono hAT).trans hTi
  have hBi := (map_mono hBT).trans hTi
  have hJi : J.map q ≤ i.range := (map_mono (Subgroup.SmallMover.join_le U q.ker T _)).trans hTi
  have hc (E : Subgroup G) (hEi : E.map q ≤ i.range) :
      Nat.card (coordinates q i E) = q.ker.relIndex E := by
    rw [relIndex_ker,←coordinates_map q i E hEi,card_map_of_injective hi]
  have hp' : (Degree.join (coordinates q i T) : Set (unipotent (F := F))) ⊆
      (coordinates q i A : Set _) * (coordinates q i B : Set _) := by
    rw [←hj]
    intro x hx
    obtain ⟨j,hjJ,he⟩ := hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hp hjJ
    obtain ⟨a',ha'⟩ := hAi (mem_map_of_mem q ha)
    obtain ⟨b',hb'⟩ := hBi (mem_map_of_mem q hb)
    refine ⟨a',?_,b',?_,?_⟩
    · change i a' ∈ A.map q
      rw [ha']
      exact mem_map_of_mem q ha
    · change i b' ∈ B.map q
      rw [hb']
      exact mem_map_of_mem q hb
    · apply hi
      rw [map_mul,ha',hb',←map_mul,he]
  obtain ⟨s,t,hs,ht,hj'⟩ := Degree.join_eq_root_sup_of_subset_product
    (coordinates q i T) (coordinates q i A) (coordinates q i B)
    (comap_mono (map_mono hAT)) (comap_mono (map_mono hBT))
    ((hc A hAi).trans hAc) ((hindex A hAT).symm.trans hAm)
    ((hc B hBi).trans hBc) ((hindex B hBT).symm.trans hBm) hp'
  have hJle : J ≤ A ⊔ B := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hp hx
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
  have hm := congrArg (fun E => E.map i) (hj.trans hj')
  rw [coordinates_map q i J hJi,Subgroup.map_sup,
    coordinates_map q i A hAi,coordinates_map q i B hBi,←Subgroup.map_sup] at hm
  have hkJ : q.ker ≤ J := Subgroup.SmallMover.kernel_le_join U q.ker T _
    (Nat.one_le_pow _ _ Nat.card_pos) hkT hUT
  have hle : A ⊔ B ≤ J := by
    have hh := (map_le_map_iff.mp hm.ge)
    exact hh.trans (sup_le le_rfl hkJ)
  exact ⟨s,t,hs,ht,by rw [hj,hj',hs,ht],le_antisymm hJle hle⟩

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree.Quotient
