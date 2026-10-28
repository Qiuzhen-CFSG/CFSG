module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponentsSetup
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowReduction
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowResiduals

/-!
# LocalAnalysisSylowResidualsComponentsSetup at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowResidualsComponentsSetup`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode ChapterA.Section04

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

private theorem perfect_twoPerfect_at {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (A ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

include S in

lemma coset_core_characteristic_control_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).characteristicNormalizerClosure ≤
      normalizer (L : Set G) := by
  apply characteristicNormalizerClosure_le_of_unique_twoLocal (isPGroup_pCoreIn 2 _)
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact (S.hypothesis.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2

lemma coset_characteristic_control_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {c : G} (hc : c ∈ P.fixed) :
    (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
      (centralizer ({c * (P.six : G)} : Set G))).characteristicNormalizerClosure ≤
        (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)).subgroupOf
          (centralizer ({c * (P.six : G)} : Set G)) := by
  have h := characteristicNormalizerClosure_subgroupOf_le (P.coset_core_le hc)
    (coset_core_characteristic_control_at (S := S) structural)
  intro x hx
  exact ⟨x.property, h hx⟩

include S in

lemma coset_core_normalizer_le_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ normalizer (L : Set G) :=
  (normalizer_le_characteristicNormalizerClosure_self _ (coset_core_ne_bot (S := S))).trans
    (coset_core_characteristic_control_at (S := S) structural)

lemma coset_sylow_normalizes_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (T : Subgroup G) ≤ normalizer (P.sixGroup : Set G) := by
  apply le_trans (le_inf (P.coset_sylow_le (P.fixed.one_mem))
    (S.hypothesis.source_sylow_normalizes_at structural))
  exact P.coset_local_normalizes P.fixed.one_mem

lemma coset_pushingUp_setup_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    {c : G} (hc : c ∈ P.fixed) :
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
      (centralizer ({c * (P.six : G)} : Set G))
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) := by
  let H := centralizer ({c * (P.six : G)} : Set G)
  let N := H ⊓ normalizer (L : Set G)
  have hTN : (T : Subgroup G) ≤ N := le_inf (P.coset_sylow_le hc)
    (S.hypothesis.source_sylow_normalizes_at structural)
  have hKN : P.sixGroup ≤ N := le_inf (P.sixGroup_le_coset_centralizer hc)
    ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer))
  have hTmap : ((T.subtype (P.coset_sylow_le hc) : Sylow 2 H) : Subgroup H).map
      H.subtype = (T : Subgroup G) := by
    exact map_subgroupOf_eq_of_le (P.coset_sylow_le hc)
  apply ChapterC.pushingUpSetup_of_normal_core (T.subtype (P.coset_sylow_le hc))
    (S.hypothesis.simpleQTKE.twoLocal_sqtk (P.coset_isTwoLocal hc)) hKN inf_le_left
    (P.coset_local_normalizes hc) perfect_twoPerfect_at
  · rwa [hTmap]
  · rw [hTmap]
    exact M.core_eq.symm
  · exact coset_core_ne_bot (S := S)
  · exact P.coset_characteristic_control_at structural hc

lemma six_local_family_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    P.sixGroup ∈ Chapter1.L G (T : Subgroup G) := by
  have hc := P.fixed.one_mem
  have hJ : P.sixGroup ⊔ (T : Subgroup G) ≤
      centralizer ({(1 : G) * (P.six : G)} : Set G) ⊓ normalizer (L : Set G) :=
    sup_le (le_inf (P.sixGroup_le_coset_centralizer hc)
      ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer)))
      (le_inf (P.coset_sylow_le hc) (S.hypothesis.source_sylow_normalizes_at structural))
  refine ⟨(P.coset_local_component e6 hc).subgroupOf_of_le le_sup_left hJ, ?_, ?_⟩
  · exact ⟨T.subtype le_sup_right, by
      simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]⟩
  · rw [M.core_eq]
    exact coset_core_ne_bot (S := S)

lemma coset_containing_component_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) :
    ∃ K : Subgroup (centralizer ({c * (P.six : G)} : Set G)),
      K.IsCComponent ∧ K.Normal ∧
      P.sixGroup.subgroupOf (centralizer ({c * (P.six : G)} : Set G)) ≤ K ∧
      generalizedFitting K = pCore 2 K := by
  let H := centralizer ({c * (P.six : G)} : Set G)
  let TH : Sylow 2 H := T.subtype (P.coset_sylow_le hc)
  let B := P.sixGroup.subgroupOf H
  have hB : B ∈ Chapter1.L H (TH : Subgroup H) :=
    (Chapter1.mem_LIn_iff_subgroupOf (P.coset_sylow_le hc)
      (P.sixGroup_le_coset_centralizer hc)).mp
      ⟨P.sixGroup_le_coset_centralizer hc, P.six_local_family_at structural M e6⟩
  have hTB : (TH : Subgroup H) ≤ normalizer (B : Set H) := by
    rw [← subgroupOf_normalizer_eq (P.sixGroup_le_coset_centralizer hc)]
    exact comap_mono (P.coset_sylow_normalizes_at structural)
  have hH := S.hypothesis.simpleQTKE.twoLocal_sqtk (P.coset_isTwoLocal hc)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_, hH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  obtain ⟨K,⟨hK,hBK,hKN⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ TH hB hTB
  refine ⟨K,hK,hKN,hBK,?_⟩
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply subnormal_core_selfCentralizing ?_ K hK.subnormal
  rw [← P.coset_fitting hc]
  exact centralizer_generalizedFitting_le H

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

