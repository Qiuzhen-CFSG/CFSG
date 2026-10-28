module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PureSixteenIncidence
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedExtensionTransfer

import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PureSixteenIncidence
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedInnerTransitivity

/-!
# Point-core incidence for a specified pure nonseed extension

The central cyclic four and self-centralization construct the two elementary
extensions of any specified nonseed eight. The inner six-point orbit and
six-by-eight incidence argument therefore apply to the same specified pure
sixteen, preserving any previously constructed plane and radical pair.

The two `import all` edges are an intentional internal proof/API split:
they reuse the already proved general orbit and counting arguments without
changing the frozen source owners or exposing their private implementation
names in this public statement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem extensions_at_nonseed (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hEA : E.val ≤ A) :
    ∃ B : Subgroup G, A ≠ B ∧
      ∀ F : Subgroup G, E.val ≤ F → IsElementaryAbelian 2 F →
        Nat.card F = 16 → F = A ∨ F = B := by
  classical
  obtain ⟨_, hCA, _⟩ := h.nonseed_eight_extension_structure E hEn A hEA inferInstance hA
  obtain ⟨c, hc4, hc2, hcZ, _⟩ := h.exists_point_core_central_four
  have hcnot : c ∉ A := by
    intro hc
    have hh := orderOf_dvd_of_pow_eq_one
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) c hc)
    rw [hc4] at hh
    norm_num at hh
  have hnc : ∃ b ∈ A, ¬ Commute b c := by
    by_contra! hh
    exact hcnot (hCA ▸ (show c ∈ centralizer (A : Set G) from fun b hb => (hh b hb).eq))
  obtain ⟨b, hbA, hbcne⟩ := hnc
  let K := centralizer (E.val : Set G)
  have hAK : A ≤ K := fun a ha e he => setLike_mul_comm (hEA he) ha
  have hcK : c ∈ K := by
    obtain ⟨cQ, hcQ, rfl⟩ := hcZ
    intro e he
    exact congrArg Subtype.val (mem_center_iff.mp hcQ ⟨e, E.property.1 he⟩)
  have hbH : b ∈ involutionCentralizer z :=
    mem_centralizer_singleton_iff.mpr (setLike_mul_comm hbA (hEA E.property.2.1))
  have hbc := h.point_core_central_four_inverted c hc4 hcZ b hbH hbcne
  have hEK : E.val ≤ K := hEA.trans hAK
  let EK := E.val.subgroupOf K
  let : IsElementaryAbelian 2 E.val := E.property.2.2.1
  let : IsElementaryAbelian 2 EK := IsElementaryAbelian.subgroupOf hEK
  have hE8 : Nat.card EK = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv).trans E.property.2.2.2
  have hEZ : EK ≤ center K := by
    intro e he
    exact mem_center_iff.mpr (fun k => Subtype.ext (k.property e he).symm)
  let ck : K := ⟨c, hcK⟩
  let bk : K := ⟨b, hAK hbA⟩
  have hck4 : orderOf ck = 4 := by rw [← orderOf_coe]; exact hc4
  have hckE : ck ^ 2 ∈ EK := by change c ^ 2 ∈ E.val; rw [hc2]; exact E.property.2.1
  have hbk2 : bk ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) b hbA)
  obtain ⟨_, _, _, _, _, _, hne, _, hall⟩ :=
    elementaryEight_centralizer_extensions
      (h.point_core_nonseed_eight_centralizer_card E hEn) EK hE8 hEZ ck bk hck4 hckE hbk2
      (fun hh => hbcne (congrArg Subtype.val hh.eq)) (Subtype.ext hbc)
  let U := EK ⊔ zpowers bk
  let B := (EK ⊔ zpowers (ck * bk)).map K.subtype
  have hEmap : EK.map K.subtype = E.val := map_subgroupOf_eq_of_le hEK
  have hUmap : U.map K.subtype = A := by
    rw [Subgroup.map_sup, hEmap, MonoidHom.map_zpowers]
    apply eq_of_le_of_card_ge (sup_le hEA (zpowers_le.mpr hbA))
    have hbE : b ∉ E.val := by
      intro hb
      exact hbcne (hcK b hb)
    rw [card_sup_zpowers_of_normalizing_involution E.val b
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) b hbA) hbE
      (centralizer_le_normalizer _ (hAK hbA)), E.property.2.2.2, hA]
  refine ⟨B, ?_, ?_⟩
  · intro he
    exact hne (map_injective K.subtype_injective (hUmap.trans he))
  · intro F hEF hFe hF16
    let := hFe
    have hFK : F ≤ K := fun f hf e he => setLike_mul_comm (hEF he) hf
    let FK := F.subgroupOf K
    let : IsElementaryAbelian 2 FK := IsElementaryAbelian.subgroupOf hFK
    have hFc : Nat.card FK = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe hFK).toEquiv).trans hF16
    have hFm : FK.map K.subtype = F := map_subgroupOf_eq_of_le hFK
    rcases (hall FK).mp ⟨fun e he => hEF he, inferInstance, hFc⟩ with hh | hh
    · exact Or.inl (hFm.symm.trans ((congrArg (fun S : Subgroup K => S.map K.subtype) hh).trans hUmap))
    · exact Or.inr (hFm.symm.trans (congrArg (fun S : Subgroup K => S.map K.subtype) hh))

/-- Every point of the same specified pure extension has an eight as its
intersection with its original point core. No new choice of sixteen occurs. -/
theorem TypeAt.pure_nonseed_extension_point_core_eights (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hEA : E.val ≤ A) (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z) :
    ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8 := by
  obtain ⟨hQA, _, hAQ⟩ := h.nonseed_eight_extension_structure E hEn A hEA inferInstance hA
  obtain ⟨B, hne, hall⟩ := extensions_at_nonseed h E hEn A hA hEA
  have hi := inner_transitive h E hEn A B hEA inferInstance hA hne hQA hall
  exact all_point_intersections_eight h h E hEn A hA hEA hAQ hpure hi

end CFSG.Quasithin.HigmanSims
