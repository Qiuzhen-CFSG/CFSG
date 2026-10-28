module
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.AmalgamModel.Geometry

/-!
# An outside involution in the local core centralizer

The join EF has order sixteen. Since t is outside F and C_G(F) = F,
EF cannot equal C_Q(t); the extraspecial centralizer bound therefore gives
x in C_Q(t) outside EF. If x² = z, self-centrality of E gives e in E
with [x,e] = z. Then (xe)² = 1. The adjustment remains in C_Q(t) and
outside EF, and so supplies the reflection needed for the split extension.
This construction needs neither an ambient order nor a centralizer model.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, the reflection in Lemma 4.1(3), pp.38–39.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer.Amalgam
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {z : G}

public theorem eight_fusion_sup_card (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) :
    Nat.card (coreIntersection z a.g ⊔ fusionCore z : Subgroup G) = 16 := by
  have hn : fusionCore z ≤ normalizer (coreIntersection z a.g : Set G) :=
    (fusionCore_le z).trans
      (NonnormalRecognition.core_normalizes_intersection h a.g a.fused_mem a.fused_ne)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (coreIntersection z a.g) (fusionCore z) hn
  rw [a.intersection_card, d.card,
    Selected.intersection_fusion_card h d a.g a.fused_mem a.fused_ne a.intersection_ne_fusion] at hc
  omega

/-- An involution centralizing t exists in Q outside EF. First find an
outside element by comparing two subgroups of order sixteen. Multiplying
by a suitable element of E cancels its square in the extraspecial center. -/
public theorem exists_reflection (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    ∃ r : G, r ∈ coreInG z ∧ r ∈ Centralizer t ∧ orderOf r = 2 ∧
      r ∉ coreIntersection z a.g ⊔ fusionCore z := by
  let Q := coreInG z
  let E := coreIntersection z a.g
  let D := Q ⊓ Centralizer t
  let W := E ⊔ fusionCore z
  let : IsExtraspecial 2 Q := h.coreInG_extraspecial
  let : IsElementaryAbelian 2 E := a.intersection_elementary
  have htF : t ∉ fusionCore z := by
    intro hm
    exact hnt (d.fusion t hm (by intro he; simp [he] at ht))
  have hD : 16 ≤ Nat.card D := by
    change 16 ≤ Nat.card (Q ⊓ Centralizer t : Subgroup G)
    rw [← map_subtype_centralizer_singleton Q (⟨t, htE.1⟩ : Q),
      card_map_of_injective Q.subtype_injective]
    exact IsExtraspecial.centralizer_card_ge_sixteen_of_card_thirty_two h.coreInG_card _
  have hW : Nat.card W = 16 := eight_fusion_sup_card h d a
  have hnot : ¬ D ≤ W := by
    intro hle
    have heq : D = W := eq_of_le_of_card_ge hle (by omega)
    apply htF
    rw [← d.centralizer_eq]
    intro f hf
    exact mem_centralizer_singleton_iff.mp
      ((heq.symm ▸ (show f ∈ W from mem_sup_right hf) : f ∈ D).2)
  obtain ⟨x, hxD, hxW⟩ := SetLike.not_le_iff_exists.mp hnot
  have hxE : x ∉ E := fun hx => hxW (mem_sup_left hx)
  have hinv {r : G} (hrW : r ∉ W) (hr2 : r ^ 2 = 1) : orderOf r = 2 :=
    orderOf_eq_prime hr2 (fun he => hrW (he ▸ W.one_mem))
  rcases NonnormalRecognition.core_square_eq_one_or_involution h hxD.1 with hx2 | hx2
  · exact ⟨x, hxD.1, hxD.2, hinv hxW hx2, hxW⟩
  have hxC : x ∉ centralizer (E : Set G) := by
    change x ∉ centralizer (NonnormalRecognition.coreIntersection z a.g : Set G)
    rw [NonnormalRecognition.coreIntersection_self_centralizing h a.g a.fused_mem a.fused_ne]
    exact hxE
  obtain ⟨e, heE, hen⟩ : ∃ e : G, e ∈ E ∧ e * x ≠ x * e := by
    classical
    simpa only [mem_centralizer_iff, not_forall, exists_prop, SetLike.mem_coe] using hxC
  have heQ : e ∈ Q := heE.1
  have he2 : e ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian e heE
  have hcomm : ⁅x, e⁆ = z := by
    have hc : ⁅Q, Q⁆ ≤ zpowers z := by
      rw [← h.coreInG_center_image, ← map_subtype_commutator,
        IsExtraspecial.commutator_eq_center (p := 2)]
    have hm := hc (commutator_mem_commutator hxD.1 heQ)
    have hne : ⁅x, e⁆ ≠ 1 := fun hh => hen
      (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hm
    obtain ⟨n, hn, hh⟩ := Finset.mem_image.mp hm
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · exact (hne (by simpa using hh.symm)).elim
    · simpa using hh.symm
  have hxe2 : (x * e) ^ 2 = 1 := by
    calc
      (x * e) ^ 2 = ⁅x, e⁆ * (e * x ^ 2 * e) := by
        simp only [commutatorElement_def, pow_two]
        group
      _ = z * (e * z * e) := by rw [hcomm, hx2]
      _ = z ^ 2 * e ^ 2 := by
        rw [mem_centralizer_singleton_iff.mp (coreInG_le z heQ)]
        simp only [pow_two, mul_assoc]
      _ = 1 := by rw [he2, ← h.involution, pow_orderOf_eq_one, mul_one]
  have hxeW : x * e ∉ W := by
    intro hm
    have hm' := W.mul_mem hm (W.inv_mem (mem_sup_left heE))
    exact hxW (by simpa only [mul_inv_cancel_right] using hm')
  exact ⟨x * e, Q.mul_mem hxD.1 heQ,
    (Centralizer t).mul_mem hxD.2 (eight_le_centralizer h a htE heE),
    hinv hxeW hxe2, hxeW⟩

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer.Amalgam
