module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalSeed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.SeedSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.FiveComponent
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleFiveMarker
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource.RankOne
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.ExternalSource

/-!
# Rank-one nonblock placement under original Baumann normalization

The actual B.5.1 normalizer action has quasisimple generalized Fitting
subgroup on its offender subgroup. Minimal parabolicity selects its natural
SL₂ or marked S₅ row. The former supplies the original moved coordinates
and uses Baumann characteristic-normalizer control. In the latter, transport
the pair on the original T to N_S(K); its first center restriction is
nontrivial in the original Z, and its second member is characteristic in
Baum(T). Original centralizer uniqueness and normalizer control eliminate
both escaping alternatives, leaving the actual A₅ block.

This discharges the natural-action premises of LocalSeed, including A₅.
The general theorem still requires C.1.16(3)'s Baumann normalization. Its
S-normalized specialization has no such extra input and applies to the
ordinary parabolic residuals when S fixes their parabolics. Both quotient
forms retain the literal K and its original G₁, S and M_Z. General Baumann
normalization, parabolic construction and catalogue assembly remain with
this owner; these conditional exports do not prove full 15.1.20(2).

Source: Aschbacher--Smith 15.1.20(2--3), pp.1094--1096;
B.5.1, C.1.19, C.1.23 and C.1.26, pp.99--103,127,130,132.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB ChapterC ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterC.RankOne.FiveBlockSource ChapterC.GlaubermanNiles
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

private theorem central_seed_normalizer_le
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (C : Subgroup G) (hne : C ≠ ⊥) (hC : C ≤ centralInvolutions T) :
    normalizer (C : Set G) ≤ Mc := by
  have hp : IsPGroup 2 C := T.isPGroup'.to_le (hC.trans (centralInvolutions_le_sylow T))
  obtain ⟨N,hN,hmax⟩ := Finite.exists_le_maximal
    (show IsTwoLocal (normalizer (C : Set G)) from ⟨C,hne,hp,rfl⟩)
  have hm : N ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    ⟨hmax,((centralizer_le hC).trans (Subgroup.centralizer_le_normalizer _)).trans hN⟩
  have he : N = Mc := Set.mem_singleton_iff.mp (hu ▸ hm)
  exact he ▸ hN

/-- B.5.1 on the same offender subgroup, with its intrinsic Fitting marking. -/
theorem NormalizerAction.fitting_source_classification {d : CaseIComponentData T M Mc V}
    {K : Subgroup G} (a : d.NormalizerAction K) (hsq : IsSQTK KnownSimple.IsKnownSimple K) :
    letI := a.reduced.elementary
    let H := K ⊔ d.normalizerSylow K
    let C := centralizer (d.normalizerModule K : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation (d.normalizerModule K) q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let J := offenderSubgroup ρ
    IsQuasisimple (generalizedFitting J) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp J.subtype)
        (generalizedFitting J)) := by
  let := a.reduced.elementary
  let H := K ⊔ d.normalizerSylow K
  let C := centralizer (d.normalizerModule K : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation (d.normalizerModule K) q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let J := offenderSubgroup ρ
  let L := d.normalizerImage K
  let : J.Normal := offenderSubgroup_normal ρ
  obtain ⟨hLJ,hc⟩ := a.source_classification hsq
  obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp a.ff
  let : IsElementaryAbelian 2 A := hA.1.2
  have hshape : IsQuasisimple (generalizedFitting (H ⧸ C)) := a.fitting ▸ a.quasisimple
  have hf := generalizedFitting_normal_eq_of_quasisimple_or_three a.reduced.quotient_pCore_eq_bot
    (Or.inl hshape) J A (IsElementaryAbelian.isPGroup 2 A) hA.1.1 (hA.le_offenderSubgroup ρ)
  have hfit : generalizedFitting J = L.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le (show L ≤ J from hLJ),hf]
    exact a.fitting.symm
  let := a.quasisimple
  have hqL : IsQuasisimple (L.subgroupOf J) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLJ).symm
  exact ⟨hfit.symm ▸ hqL,hfit.symm ▸ hc⟩

/-- Rank-one nonblock exclusion on the original normalizer action, with
only C.1.16(3)'s Baumann normalization still explicit. Both natural rows
are extracted from B.5.1 and both original characteristic-pair alternatives
are eliminated; no natural-action or pair-compatibility premise remains. -/
private theorem localFamily_chi_of_minimalParabolic_baumann (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (hbaum : baumann d.S ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ d.normalizerSylow K : Subgroup G))
    (hP : (P : Subgroup (K ⊔ d.normalizerSylow K : Subgroup G)).map
      (K ⊔ d.normalizerSylow K).subtype = d.normalizerSylow K)
    (hmin : IsMinimalParabolicOver P ⊤) : IsChiBlock K := by
  let := h.elementary
  let H := K ⊔ d.normalizerSylow K
  let U := d.normalizerModule K
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  let := a.reduced.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let J := offenderSubgroup ρ
  have hsq := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hHG : H ≤ d.G1 := sup_le hK.1 (inf_le_left.trans d.S_le_G1)
  have hsqH := (IsSQTK.equiv (subgroupOfEquivOfLe hHG)).mp (hsq.subgroup (H.subgroupOf d.G1))
  have hsqK := (IsSQTK.equiv (subgroupOfEquivOfLe hK.1)).mp (hsq.subgroup (K.subgroupOf d.G1))
  obtain ⟨P0,hP0,hfitH,hres,hseed,hmove⟩ :=
    d.localFamily_normalizer_seed_setup hG hempty hM hJ hu h hK hq hout hf
  have hPP : P0 = P := by
    apply Sylow.ext
    exact map_injective H.subtype_injective (hP0.trans hP.symm)
  subst P0
  have hcpu := d.localFamily_baumann_control hG hM hJ h hbaum P hP
  have hesc : ¬ pResidual 2 H ≤ M.subgroupOf H := by
    rw [hres]
    intro hh
    apply d.localFamily_not_le_M hG hempty hM hu hK hout
    intro k hk
    exact hh (show (⟨k,mem_sup_left hk⟩ : H) ∈ K.subgroupOf H from hk)
  obtain ⟨hqs,⟨c⟩⟩ := a.fitting_source_classification hsqK
  have hqn : q.ker ≠ ⊤ := by
    rw [QuotientGroup.ker_mk']
    intro hz
    apply hmove
    change elementaryAbelianMaxJ (P : Subgroup H) ≤ C
    rw [hz]
    exact le_top
  have hminq := (minimalParabolic_reduced_image P hmin q
    (QuotientGroup.mk'_surjective C) a.reduced.quotient_pCore_eq_bot hqn).2
  have hchi : IsChiBlockIn (pResidual 2 H) := by
    rcases source_offender_quasisimple_rank_one ρ (P.mapSurjective (QuotientGroup.mk'_surjective C))
      hminq a.ff a.reduced.quotient_pCore_eq_bot hqs c with ⟨F0,hnat⟩ | ⟨efive⟩
    · exact quasisimple_linear_seed_chi_of_baumann_control P hmin U a.reduced hmove
        q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hqs c.sectionData F0 hnat
        hseed hfitH (M.subgroupOf H) hcpu hesc
    · obtain ⟨efive⟩ := efive
      let W := ⁅U,pResidual 2 H⁆
      have hW := a.reduced.moved U
      let := hW.elementary
      have hmoveW : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) := by
        rwa [a.reduced.centralizer_moved_eq U]
      obtain ⟨q5,hq5,hk5,f,hfs,hfe,hfk⟩ := quasisimple_five_source_marker P hmin U
        a.reduced hmove q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
        hqs c.sectionData efive
      obtain ⟨hcomp,⟨eL⟩⟩ := symmetric_five_residual_component
        (ChapterA.SQTKStructure.a36Input_of_theoremsAC
          (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
          (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
        hsqH P hmin W hW hmoveW q5 hq5 hk5
      have him : (pResidual 2 H).map q5 = alternatingGroup (Fin 5) := by
        rw [map_pResidual_of_surjective 2 q5 hq5,Equiv.Perm.twoResidual_eq_alternating]
      have hfix : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
          NormalElementaryQuotient.representation W q5 hq5 hk5 g v = v := by
        intro v hv g hg
        have hv' : v ∈ fixedSpace (NormalElementaryQuotient.representation W q5 hq5 hk5)
            ((pResidual 2 H).map q5) := hfk ▸ hv
        exact hv' ⟨g,him.symm ▸ hg⟩
      have hbT := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).2.1
      have hBR : baumann (T : Subgroup G) ≤ (P : Subgroup H).map H.subtype := by
        rw [hP,←hbT]
        exact le_inf inf_le_left hbaum
      have hRT : (P : Subgroup H).map H.subtype ≤ (T : Subgroup G) := by
        rw [hP]
        exact inf_le_left.trans d.S_le_T
      have hTne : (T : Subgroup G) ≠ ⊥ := by
        intro hz
        have hPzero : (P : Subgroup H) = ⊥ :=
          ((P : Subgroup H).map_eq_bot_iff_of_injective H.subtype_injective).mp
            (bot_unique (hRT.trans hz.le))
        exact hmin.2 (hPzero ▸ le_normalizer_of_normal)
      obtain ⟨D,hD⟩ := exists_baumann_universal_pair (T : Subgroup G) T.isPGroup' hTne
      have hsrc := external_source_conclusion (T : Subgroup G) H P hBR hRT hfitH
        (pResidual 2 H) hcomp (pResidual_sup_sylow_eq_top P) eL W q5 hq5 hk5 him
        f hfs hfe hfix hmoveW D hD
      rcases hsrc with hc | hn | ⟨hb,ha,_,_,_⟩
      · have hN := central_seed_normalizer_le hu (firstAmbient (T : Subgroup G) D)
          (firstAmbient_ne_bot (T : Subgroup G) T.isPGroup' D)
          (firstAmbient_le_omegaCenter (T : Subgroup G) D)
        have hHC : H ≤ centralizer (firstAmbient (T : Subgroup G) D : Set G) := by
          intro x hx z hz
          obtain ⟨w,hw,rfl⟩ := hc hz
          exact (congrArg H.subtype ((mem_center_iff.mp hw) ⟨x,hx⟩)).symm
        exact (hout (le_inf hK.1 (le_sup_left.trans
          (hHC.trans ((Subgroup.centralizer_le_normalizer _).trans hN))))).elim
      · let B := secondAmbient (T : Subgroup G) D
        have hBH : B ≤ H := (map_subtype_le _).trans (hBR.trans (map_subtype_le _))
        let : (B.subgroupOf H).Normal := hn
        have hnH : H ≤ normalizer (B : Set G) := by
          have hh := (B.subgroupOf H).le_normalizer_map H.subtype
          rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
            map_subgroupOf_eq_of_le hBH] at hh
          exact hh
        have hcB : (baumann (T : Subgroup G)).characteristicNormalizerClosure ≤ M := by
          rw [←hbT]
          exact (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).2.2.1
        let := D.second_characteristic
        have hnB := (normalizer_le_characteristicNormalizerClosure
          (baumann (T : Subgroup G)) D.second D.second_ne_bot).trans hcB
        exact (d.localFamily_not_le_M hG hempty hM hu hK hout
          (le_sup_left.trans (hnH.trans hnB))).elim
      · exact ⟨hb,Or.inr ⟨5,by decide,ha⟩⟩
  rw [hres] at hchi
  exact RankOne.ChiProduct.chi_of_equiv (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)) hchi.2

/-- The natural rank-one image reconstructs a chi-block from the actual
source action once Baumann normalization has been supplied. -/
theorem localFamily_rankOne_chi_of_baumann_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (hbaum : baumann d.S ≤ normalizer (K : Set G))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage K ≃* Matrix.SpecialLinearGroup (Fin 2) F) : IsChiBlock K := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  obtain ⟨⟨P,hP⟩,_,_⟩ := d.localFamily_normalizer_setup h hM.1.2 hu hK hq hout hf
  exact d.localFamily_chi_of_minimalParabolic_baumann hG hempty hM hJ hu h hK hq hout hf
    hbaum P hP (a.minimalParabolic_of_rankOne hq F e P hP)

/-- The rank-one hypothesis may be stated on the literal K/O₂(K).
This is the form needed for actual higher-field parabolic residuals. -/
theorem localFamily_core_rankOne_chi_of_baumann_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (hbaum : baumann d.S ≤ normalizer (K : Set G))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) : IsChiBlock K := by
  obtain ⟨⟨P,hP⟩,_,_⟩ := d.localFamily_normalizer_setup h hM.1.2 hu hK hq hout hf
  let H := K ⊔ d.normalizerSylow K
  let K0 := K.subgroupOf H
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer inf_le_right)
  let i : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let e0 := (QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).trans e
  let f := e0.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K0))
  have hfs : Function.Surjective f := e0.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfk : f.ker ≤ (frattini (K0 ⧸ pCore 2 K0)).comap (QuotientGroup.mk' (pCore 2 K0)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e0.injective,QuotientGroup.ker_mk']
    intro x hx
    change QuotientGroup.mk' (pCore 2 K0) x ∈ frattini (K0 ⧸ pCore 2 K0)
    have hxq : QuotientGroup.mk' (pCore 2 K0) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [hxq]
    exact one_mem _
  have hgen : K0 ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hmin := minimal_over_normal_rankOne_frattini F K0 P hgen f hfs hfk
  exact d.localFamily_chi_of_minimalParabolic_baumann hG hempty hM hJ hu h hK hq hout hf
    hbaum P hP hmin

/-- The literal local-family restriction consumed by parabolic residuals,
conditional only on the remaining Baumann-normalization source step. -/
theorem localFamily_nonblock_le_MZ_of_baumann_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : generalizedFitting K = pCore 2 K)
    (hbaum : baumann d.S ≤ normalizer (K : Set G)) (hnot : ¬ IsChiBlock K)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) : K ≤ d.MZ := by
  by_contra hout
  exact hnot (d.localFamily_core_rankOne_chi_of_baumann_normalizes
    hG hempty hM hJ hu h hK hq hout hf hbaum F e)

/-- For a member normalized by the original S, the nonblock placement has
no Baumann or action premise. This includes the parabolic residuals in
15.1.20(3) when S fixes their actual parabolics. -/
theorem localFamily_nonblock_le_MZ_of_sylow_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : generalizedFitting K = pCore 2 K)
    (hn : d.S ≤ normalizer (K : Set G)) (hnot : ¬ IsChiBlock K)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) : K ≤ d.MZ :=
  d.localFamily_nonblock_le_MZ_of_baumann_normalizes hG hempty hM hJ hu h hK hq hf
    (inf_le_left.trans hn) hnot F e

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
