module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.Normalizer
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentModels

/-!
# The source FF-module on K N_S(K)

Thompson normalization gives J(N_S(K))=J(S), and the source Sylow
intersection makes N_S(K) Sylow in K N_S(K). Its original central-involution
span is reduced and moved by K. Thompson-normalizer escape proves
K=[K,J(S)], and the literal centralizer quotient has quasisimple generalized
Fitting subgroup equal to the image of K and admits a best offender.

The module, two-core identity, movement and quotient are fixed by these
constructions. No model classification is a field of the action record.
This covers the local parabolic residuals as well as ambient C-components.

Source: Aschbacher--Smith 15.1.20(2), printed p.1094, using B.2.7, B.2.10
and B.2.14, printed pp.76--78.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

@[expose] def normalizerSylow (d : CaseIComponentData T M Mc V) (K : Subgroup G) :
    Subgroup G := d.S ⊓ normalizer (K : Set G)

@[expose] def normalizerModule (d : CaseIComponentData T M Mc V) (K : Subgroup G) :
    Subgroup (K ⊔ d.normalizerSylow K : Subgroup G) :=
  normalClosure ((centralInvolutions T).subgroupOf (K ⊔ d.normalizerSylow K) :
    Set (K ⊔ d.normalizerSylow K : Subgroup G))

instance normalizerModule_normal (d : CaseIComponentData T M Mc V) (K : Subgroup G) :
    (d.normalizerModule K).Normal := by unfold normalizerModule; infer_instance

/-- The source normalizer has the original Thompson subgroup and contains
its original central-involution seed. It is Sylow in K N_S(K). -/
theorem localFamily_normalizer_setup (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    Chapter1.IsSylowIn 2 (d.normalizerSylow K) (K ⊔ d.normalizerSylow K) ∧
      elementaryAbelianMaxJ (d.normalizerSylow K) = elementaryAbelianMaxJ d.S ∧
      centralInvolutions T ≤ d.normalizerSylow K := by
  have hn := d.localFamily_thompson_normalizes h hTM hu hK hq hout hf
  have hJS : elementaryAbelianMaxJ d.S ≤ d.S := sSup_le fun _ hA => hA.1
  have hJR : elementaryAbelianMaxJ d.S ≤ d.normalizerSylow K := le_inf hJS hn
  refine ⟨?_,elementaryAbelianMaxJ_eq_of_intermediate d.S _ hJR inf_le_left,?_⟩
  · obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
    exact (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)).exists_sylow_sup_of_coprime_index
      K (d.normalizerSylow K) inf_le_right (P : Subgroup K) P.not_dvd_index (by
        rw [hP]
        exact le_inf inf_le_left (inf_le_right.trans K.le_normalizer))
  · let : IsElementaryAbelian 2 (centralInvolutions T) := by
      change IsElementaryAbelian 2 (omegaCenterIn (T : Subgroup G))
      infer_instance
    have hZS : centralInvolutions T ≤ d.S := le_inf (centralInvolutions_le_sylow T)
      ((centralInvolutions_le_centralizer_sylow T).trans
        (centralizer_le (d.marked_le_sylow h hTM)))
    have he := elementary_centralizer_maxJ_le_omegaCenter d.S (centralInvolutions T) hZS
      ((centralInvolutions_le_centralizer_sylow T).trans (centralizer_le (hJS.trans d.S_le_T)))
    intro z hz
    exact hJR ((mem_omegaOneCenterAmbient_iff _ _).mp (he hz)).1

/-- The actual normalizer action in source 15.1.20(2). Every field refers
to K N_S(K), retaining J(S) as the moving subgroup. -/
structure NormalizerAction (d : CaseIComponentData T M Mc V) (K : Subgroup G) : Prop where
  reduced : IsPReduced 2 (d.normalizerModule K)
  movement : K = ⁅K,elementaryAbelianMaxJ d.S⁆
  core : pCore 2 (K ⊔ d.normalizerSylow K : Subgroup G) =
    (d.normalizerSylow K).subgroupOf (K ⊔ d.normalizerSylow K) ⊓
      centralizer (d.normalizerModule K : Set (K ⊔ d.normalizerSylow K : Subgroup G))
  fitting :
    let q := QuotientGroup.mk' (centralizer (d.normalizerModule K : Set (K ⊔ d.normalizerSylow K : Subgroup G)))
    (K.subgroupOf (K ⊔ d.normalizerSylow K)).map q = generalizedFitting _
  quasisimple :
    let q := QuotientGroup.mk' (centralizer (d.normalizerModule K : Set (K ⊔ d.normalizerSylow K : Subgroup G)))
    IsQuasisimple ((K.subgroupOf (K ⊔ d.normalizerSylow K)).map q)
  ff :
    letI := reduced.elementary
    let q := QuotientGroup.mk' (centralizer (d.normalizerModule K : Set (K ⊔ d.normalizerSylow K : Subgroup G)))
    IsFFModule (NormalElementaryQuotient.representation (d.normalizerModule K) q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))

/-- The FF-module opening of source 15.1.20(2) for the entire original
local family, without assuming S-normalization or ambient componenthood. -/
theorem localFamily_normalizerAction (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) : d.NormalizerAction K := by
  obtain ⟨hs,hJRS,hZR⟩ := d.localFamily_normalizer_setup h hM.1.2 hu hK hq hout hf
  let R := d.normalizerSylow K
  let H := K ⊔ R
  let K0 := K.subgroupOf H
  let W := d.normalizerModule K
  let Z := (centralInvolutions T).subgroupOf H
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer inf_le_right)
  have hK0 : K0.IsCComponent := hK.2.1.subgroupOf_of_le le_sup_left
    (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let := hq
  let : IsQuasisimple (K0 ⧸ pCore 2 K0) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  obtain ⟨P,hP⟩ := hs
  have hPS : (P : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show R ≤ H from le_sup_right)]
  have hgen : K0 ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hZT : Z ≤ P := by
    rw [hPS]
    exact fun _ hz => hZR hz
  have hcent : Z ≤ centralizer (P : Set H) := by
    intro z hz x hx
    exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz x
      (d.S_le_T (show (x : G) ∈ d.S from (hP ▸ mem_map_of_mem H.subtype hx).1)))
  have hcH : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    centralizer_pCore_sup_le 2 K R (hf ▸ centralizer_generalizedFitting_le K)
      (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)) inf_le_right
  have hZC : Z ≤ centralizer (pCore 2 H : Set H) :=
    hcent.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal P))
  have hWQ : W ≤ pCore 2 H := normalClosure_le_normal (hZC.trans hcH)
  have hWC : W ≤ centralizer (pCore 2 H : Set H) := normalClosure_le_normal hZC
  let : IsMulCommutative W :=
    le_centralizer_iff_isMulCommutative.mp (hWC.trans (centralizer_le hWQ))
  let : IsElementaryAbelian 2 (centralInvolutions T) := by
    change IsElementaryAbelian 2 (omegaCenterIn (T : Subgroup G))
    infer_instance
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf (hZR.trans le_sup_right)
  let : IsMulCommutative (normalClosure (Z : Set H)) := inferInstanceAs (IsMulCommutative W)
  have hr : IsPReduced 2 W := isPReduced_normalClosure_of_sylow_central P Z hZT hcent
  let := hr.elementary
  have hmoved : ⁅W,K0⁆ ≠ ⊥ := by
    intro he
    have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    apply hout
    apply le_inf hK.1
    intro k hk
    apply hMc.2
    intro z hz
    exact congrArg Subtype.val (hc (show (⟨k,mem_sup_left hk⟩ : H) ∈ K0 from hk)
      ⟨z,mem_sup_right (hZR hz)⟩ (le_normalClosure hz))
  have hnot : ¬ K0 ≤ normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) := by
    intro hh
    have hm := (map_mono (f := H.subtype) hh).trans
      ((elementaryAbelianMaxJ (P : Subgroup H)).le_normalizer_map H.subtype)
    rw [map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP,hJRS] at hm
    exact d.localFamily_thompson_escape hG hempty hM hJ hu h hK hout hm
  have hmove : K = ⁅K,elementaryAbelianMaxJ d.S⁆ := by
    have he := congrArg (map H.subtype)
      (eq_commutator_maxJ_of_quasisimple_core_of_not_normalizes P K0 hK0 hgen hnot)
    rwa [map_commutator,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP,hJRS] at he
  have hprod : ∀ x : H, ∃ k ∈ K0, ∃ t ∈ (P : Subgroup H), k*t=x := by
    intro x
    exact mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top x)
  obtain ⟨hcore,_,hfit,hquasi⟩ := internalModule_quasisimple_core_structure
    W q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    hr.quotient_pCore_eq_bot P K0 hK0 inferInstance hmoved hprod
  refine ⟨hr,hmove,hPS ▸ hcore,hfit,hquasi,?_⟩
  have hnotC : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ q.ker := by
    intro hh
    have hJP : elementaryAbelianMaxJ (P : Subgroup H) ≤ P := sSup_le fun _ hA => hA.1
    have hhC : elementaryAbelianMaxJ (P : Subgroup H) ≤ C := by
      simpa only [q,QuotientGroup.ker_mk'] using hh
    have hJQ : elementaryAbelianMaxJ (P : Subgroup H) ≤ pCore 2 H :=
      hcore.symm ▸ le_inf hJP hhC
    have he := elementaryAbelianMaxJ_eq_of_intermediate (P : Subgroup H) (pCore 2 H)
      hJQ (pCore_isPGroup.le_sylow_of_normal P)
    have hn : K0 ≤ normalizer (elementaryAbelianMaxJ (pCore 2 H) : Set H) :=
      le_normalizer_of_normal.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
    exact hnot (he ▸ hn)
  exact (ChapterB.lemma_B_2_7_local W q (QuotientGroup.mk'_surjective C)
    (QuotientGroup.ker_mk' C) P (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P)) hnotC).1


end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
