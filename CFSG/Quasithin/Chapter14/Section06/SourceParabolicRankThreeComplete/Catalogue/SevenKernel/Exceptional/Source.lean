module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Exceptional.Relative
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Exceptional.Moved
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Preparation

/-!
# Exceptional block selection on the original first-parabolic radical

The full moved star four-space gives an actual normal elementary subgroup
with the unchanged action kernel. The original MS input places O₂(KR) in R.
Relative exceptional selection then constructs the C.1.24 alternative on
Baum(R), without recovering K/O₂(K) in advance.

Source: Aschbacher--Smith C.1.24(a), pp.130--131, C.2.7(3)(d), pp.145--147,
and original 14.6.10(5), p.1029.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Exceptional
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
variable {G : Type*} [Group G] [Finite G]

/-- The relative C.1.24 selection on the literal C.2.7 component-radical
product. The original MS condition discharges the two-core containment. -/
theorem selection_of_original_action {H K R M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hms : ChapterC.MSOddIndexRadical (R.subgroupOf (K ⊔ R)))
    (e : starImage K R K ≃* alternatingGroup (Fin 7))
    (m : AlternatingModels.ActionData (starRepresentation K R) (starImage K R K))
    (hfull : starImage K R K = ⊤)
    (hd : Module.finrank (ZMod 2) m.sectionData.space.toSubmodule = 4) :
    SelectionConclusion K R := by
  let J := K ⊔ R
  let L := K.subgroupOf J
  let R₀ := R.subgroupOf J
  let V := starV K R
  let q := QuotientGroup.mk' (starKernel K R)
  let : L.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  let a : L ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let : IsQuasisimple (L ⧸ pCore 2 L) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm
  let U := (⁅V,L⁆ : Subgroup J)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (commutator_le_left V L)
  have hfL : generalizedFitting L = pCore 2 L := by
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,h.fitting]
  obtain ⟨q',hq',hk',hLq',hd'⟩ := moved_exceptional V L q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    m.sectionData.space m.sectionData.space_eq m.faithful e hfull hd
  have hm : ⁅U,L⁆ ≠ ⊥ := by
    intro hb
    have hle : L ≤ q'.ker := by
      rw [hk']
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb)
    have hz : (⊤ : Subgroup (alternatingGroup (Fin 7))) = ⊥ :=
      hLq'.symm.trans ((map_eq_bot_iff L).mpr hle)
    let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact top_ne_bot hz
  have hR : IsPGroup 2 R₀ := hms.isPGroup
  obtain ⟨P,hRP⟩ := hR.exists_le_sylow
  have hgen : L ⊔ R₀ = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ J from le_sup_left) (show R ≤ J from le_sup_right),
      subgroupOf_self]
  have hprod : ∀ g:J, ∃ l∈L, ∃ t∈(P : Subgroup J), l*t=g := by
    intro g
    obtain ⟨l,hl,t,ht,he⟩ := mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top g)
    exact ⟨l,hl,t,hRP ht,he⟩
  exact relative_selection L U R₀
    (h.component.2.subgroupOf_of_le le_sup_left h.join_le)
    (source_join_fitting h) hfL P hprod q' hq' hk' hLq' hd' hm hms.twoCore_le hRP

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Exceptional relative block selection under all unchanged original
Chapter 14 parameters. No full two-core quotient marking is assumed. -/
theorem exceptionalSelectionInput :
    ExceptionalSelectionInput hG T hempty hM hunique hmany hcard e hab := by
  intro H hH d I hI eC m hm
  exact selection_of_original_action
    (prepared hG T hempty hM hunique hmany hcard e hab H hH d I hI).1
    (generated_join_ms_inputs hG T hempty hM hunique hmany hcard e hab H hH d I hI).1
    eC m hm.1 hm.2
end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Exceptional
