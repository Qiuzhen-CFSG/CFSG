module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.FittingPreimage
public import Theory.GroupTheory.GeneralizedFitting.MovedComponentOutside
public import Theory.Quasithin.Rank
import Mathlib.Tactic
/-!
# The actual block module in the contained generalized-Fitting branch

Pass to H/O₂(H). The moved binary module centralizes the odd core by A.1.26.
If it survives, generalized-Fitting detection selects a moved ordinary
component outside the local subgroup. This contradicts containment of the
full generalized Fitting preimage. Thus the original module lies in O₂(H).
Characteristicness of the original blockU supplies its local normality.

Source: Aschbacher–Smith C.2.13, p.148, specialized to normalized block input.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (A ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem moved_module_le_core {A : Type*} [Group A] [Finite A]
    (hq : IsStronglyQuasithin A) (M L V : Subgroup A)
    [Group.IsPerfect L] [IsElementaryAbelian 2 V]
    (hVM : V ≤ M) (hMV : M ≤ normalizer (V : Set A))
    (hmoved : V = ⁅V,L⁆)
    (hf : (generalizedFitting (A ⧸ pCore 2 A)).comap
      (QuotientGroup.mk' (pCore 2 A)) ≤ M) : V ≤ pCore 2 A := by
  let q := QuotientGroup.mk' (pCore 2 A)
  let V' := V.map q
  let M' := M.map q
  let L' := L.map q
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.map q
  let : Group.IsPerfect L' := Group.IsPerfect.map q
  have hn : M' ≤ normalizer (V' : Set (A ⧸ pCore 2 A)) :=
    (map_mono hMV).trans (V.le_normalizer_map q)
  have hvcore : V' ≤ M'.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup (p := 2) (G := V')) (map_mono hVM) hn
  have hq' : IsStronglyQuasithin (A ⧸ pCore 2 A) := by
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans (hq p hp ho)
  have hm : V' = ⁅V',L'⁆ := by
    change V.map q = ⁅V.map q,L.map q⁆
    rw [←map_commutator,←hmoved]
  have hodd := ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hq' L' V'
    perfect_twoPerfect hm.symm
  have hGF : generalizedFitting (A ⧸ pCore 2 A) ≤ M' := by
    have hh := map_mono (f := q) hf
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _] at hh
  have hvbot : V' = ⊥ := by
    by_contra hv
    obtain ⟨K,hK,hmove,hout⟩ := exists_component_moved_outside_of_centralizes_oddCore
      V' M' (IsElementaryAbelian.isPGroup (p := 2) (G := V')) hv
      (pCore_quotient_pCore_eq_bot 2) hodd hvcore
    exact hout ((component_le_generalizedFitting _ K hK).trans hGF)
  simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff V).mp hvbot

variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H M L R V : Subgroup G}
/-- The unchanged original block module dies modulo the ambient two-core. -/
theorem block_module_le_ambient_core_of_fitting_contained
    (h : HypothesisC28 κ H M L R V)
    (hnorm : M ≤ normalizer (L : Set G))
    (hU : (blockU L).map L.subtype = V)
    (hf : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H) : V ≤ H.pCoreIn 2 := by
  have hs : conjugateSpanBy L M = L :=
    le_antisymm (conjugateSpanBy_le le_rfl hnorm) (le_conjugateSpanBy _ _)
  have hVL : V ≤ L := by simpa only [hs] using h.module_le
  have hLH : L ≤ H := h.component_le.trans h.local_le
  have hVH := hVL.trans hLH
  have hMV : M ≤ normalizer (V : Set G) := by
    rw [←hU]
    exact hnorm.trans (normalizer_le_normalizer_characteristic_image L (blockU L))
  let A := L.subgroupOf H
  let W := V.subgroupOf H
  let N := M.subgroupOf H
  let : Group.IsPerfect L := hs ▸ h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hLH).symm.surjective
  let := h.module_elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  have hWN : W ≤ N := comap_mono (hVL.trans h.component_le)
  have hNW : N ≤ normalizer (W : Set H) := by
    rw [←subgroupOf_normalizer_eq hVH]
    exact comap_mono hMV
  have hWA : W = ⁅W,A⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le hLH]
    simpa only [hs] using h.module_commutator
  have hc := moved_module_le_core h.sqtk.stronglyQuasithin N A W hWN hNW hWA hf
  intro v hv
  exact ⟨⟨v,hVH hv⟩,hc hv,rfl⟩
end CFSG.Quasithin.ChapterC.HypothesisC28
