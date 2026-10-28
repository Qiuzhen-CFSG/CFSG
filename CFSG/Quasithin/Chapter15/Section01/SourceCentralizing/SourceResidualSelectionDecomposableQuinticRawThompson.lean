module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawComponent
public import Theory.GroupTheory.SylowNormalizedSupIndex
-- Intentional same-package proof reuse: the private central-seed lemma has
-- only intrinsic group inputs; no CaseIComponentData record is constructed.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.Normalizer

/-!
# Thompson normalization and movement on the literal raw component

The original seed lies in J(S)=J(T). Its normal closure in LS is reduced
and elementary and is moved by L, since L escapes the partner. The
surviving-component theorem gives J(S) ≤ N(L). Restriction to N_S(L)
preserves J(S) and its Sylow role in LN_S(L). The original Thompson
normalizer bound and L's escape from M then force [L,J(S)]=L.

All subgroups remain literal. No generation of M by its marked centralizer
and T, CaseI component record, or classified quotient is assumed.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original raw local-family component is normalized and fully moved
by J(S). Its actual Sylow normalizer retains J(S) and the original seed. -/
theorem PreparedChosenModule.raw_component_thompson
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hfit : generalizedFitting L = pCore 2 L)
    (houtMZ : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬L ≤ M) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (L : Set G)
    elementaryAbelianMaxJ S ≤ normalizer (L : Set G) ∧
      ⁅L,elementaryAbelianMaxJ S⁆ = L ∧
      Chapter1.IsSylowIn 2 R (L ⊔ R) ∧
      elementaryAbelianMaxJ R = elementaryAbelianMaxJ S ∧
      centralInvolutions T ≤ R := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (L : Set G)
  have hJS : elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) :=
    (h.caseI_marked_thompson_control hG T hM hJ hZ).1
  have hZJ : centralInvolutions T ≤ elementaryAbelianMaxJ S := by
    rw [hJS]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp
      (omegaCenter_le_omegaCenter_maxJ (T : Subgroup G) hz)).1
  have hZS : centralInvolutions T ≤ S := hZJ.trans (sSup_le fun _ hA => hA.1)
  have hJN : elementaryAbelianMaxJ S ≤ normalizer (L : Set G) := by
    let A := L ⊔ S
    let K := L.subgroupOf A
    let Z := (centralInvolutions T).subgroupOf A
    let W := normalClosure (Z : Set A)
    let C := centralizer (W : Set A)
    let q := QuotientGroup.mk' C
    obtain ⟨P,hP⟩ := hL.2.2.1
    let e : K ≃* L := subgroupOfEquivOfLe le_sup_left
    let := hq
    let : IsQuasisimple (K ⧸ pCore 2 K) :=
      IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
    have hfK : generalizedFitting K = pCore 2 K := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_generalizedFitting_equiv,pCore_map_iso,hfit]
    have hgen : K ⊔ (P : Subgroup A) = ⊤ := by
      apply map_injective A.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show L ≤ A from le_sup_left),hP,
        ←MonoidHom.range_eq_map,range_subtype]
    have hZP : Z ≤ P := by
      intro z hz
      have hzP : (z : G) ∈ (P : Subgroup A).map A.subtype := by
        rw [hP]
        exact hZS hz
      obtain ⟨x,hx,he⟩ := hzP
      exact A.subtype_injective he ▸ hx
    have hZC : Z ≤ centralizer (P : Set A) := by
      intro z hz x hx
      exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz x
        (show (x : G) ∈ (T : Subgroup G) from
          (hP ▸ mem_map_of_mem A.subtype hx).1))
    have hZQ := CaseIComponentData.central_seed_le_core P K Z hL.2.1 hgen hfK hZP hZC
    have hZcore : Z ≤ centralizer (pCore 2 A : Set A) :=
      hZC.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal P))
    have hWQ : W ≤ pCore 2 A := normalClosure_le_normal hZQ
    have hWC : W ≤ centralizer (pCore 2 A : Set A) := normalClosure_le_normal hZcore
    let : IsMulCommutative W :=
      le_centralizer_iff_isMulCommutative.mp (hWC.trans (centralizer_le hWQ))
    let : IsElementaryAbelian 2 (centralInvolutions T) := by
      change IsElementaryAbelian 2 (omegaCenterIn (T : Subgroup G))
      infer_instance
    let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf
      (hZS.trans (show S ≤ A from le_sup_right))
    let : IsMulCommutative (normalClosure (Z : Set A)) :=
      inferInstanceAs (IsMulCommutative W)
    have hr : IsPReduced 2 W := isPReduced_normalClosure_of_sylow_central P Z hZP hZC
    let := hr.elementary
    have hne : K.map q ≠ ⊥ := by
      intro hb
      have hc : K ≤ C := by
        simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff K).mp hb
      have hMc : Mc ∈ maximalTwoLocalOvergroups
          (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
      apply houtMZ
      refine le_inf hL.1 ?_
      intro l hl
      apply hMc.2
      intro z hz
      exact congrArg Subtype.val
        (hc (show (⟨l,mem_sup_left hl⟩ : A) ∈ K from hl)
          ⟨z,mem_sup_right (hZS hz)⟩ (le_normalClosure hz))
    have hcore : pCore 2 A ≤ q.ker := by
      rw [QuotientGroup.ker_mk']
      exact le_centralizer_iff.mp hr.le_centralizer_pCore
    have hn := ChapterB.thompson_normalizes_surviving_cComponent W (P : Subgroup A) K
      (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P)) hL.2.1 inferInstance
      q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hcore hne
    have hm := (map_mono (f := A.subtype) hn).trans (K.le_normalizer_map A.subtype)
    rw [←elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective,hP,
      map_subgroupOf_eq_of_le (show L ≤ A from le_sup_left)] at hm
    exact hm
  have hJR : elementaryAbelianMaxJ S ≤ R :=
    le_inf (sSup_le fun _ hA => hA.1) hJN
  have hJRS : elementaryAbelianMaxJ R = elementaryAbelianMaxJ S :=
    elementaryAbelianMaxJ_eq_of_intermediate S R hJR inf_le_left
  have hRSyl : Chapter1.IsSylowIn 2 R (L ⊔ R) := by
    obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hL.2
    exact (T.isPGroup'.to_le (inf_le_left.trans (show S ≤ (T : Subgroup G) from inf_le_left))).exists_sylow_sup_of_coprime_index
      L R inf_le_right (P : Subgroup L) P.not_dvd_index (by
        rw [hP]
        exact le_inf inf_le_left (inf_le_right.trans L.le_normalizer))
  refine ⟨hJN,?_,hRSyl,hJRS,hZJ.trans hJR⟩
  let A := L ⊔ R
  let K := L.subgroupOf A
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer inf_le_right)
  have hK : K.IsCComponent := hL.2.1.subgroupOf_of_le le_sup_left
    (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  let e : K ≃* L := subgroupOfEquivOfLe le_sup_left
  let := hq
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  obtain ⟨P,hP⟩ := hRSyl
  have hgen : K ⊔ (P : Subgroup A) = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show L ≤ A from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hnot : ¬K ≤ normalizer (elementaryAbelianMaxJ (P : Subgroup A) : Set A) := by
    intro hn
    have hm := (map_mono (f := A.subtype) hn).trans
      ((elementaryAbelianMaxJ (P : Subgroup A)).le_normalizer_map A.subtype)
    rw [map_subgroupOf_eq_of_le (show L ≤ A from le_sup_left),
      ←elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective,hP,hJRS,hJS] at hm
    exact houtM (hm.trans (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1)
  have he := congrArg (map A.subtype)
    (eq_commutator_maxJ_of_quasisimple_core_of_not_normalizes P K hK hgen hnot)
  rw [map_commutator,map_subgroupOf_eq_of_le (show L ≤ A from le_sup_left),
    ←elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective,hP,hJRS] at he
  exact he.symm

end CFSG.Quasithin.Chapter15.Section01
