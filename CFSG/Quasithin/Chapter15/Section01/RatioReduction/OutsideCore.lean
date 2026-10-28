module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.NormalSource
public import CFSG.Quasithin.Chapter15.Section01.MinimalParabolicSource
public import CFSG.Quasithin.Chapter15.Section01.NormalizerSource
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd

/-!
# The original outside-core branch of the Section 15.1 cubic bound

For the selected minimal overgroup H outside M, the centralizing Thompson
hypothesis supplies a genuine minimal parabolic with marked maximal subgroup
H ∩ M. The original V(M) is elementary and normal in M, hence is normal in
that marked subgroup and contained in its two-core. Its failure to lie in
O₂(H) is exactly its failure to lie in the maximal core, since the latter
intersects the original Sylow subgroup in O₂(H).

The normal-module E.2 theorem then gives a strict cubic bound on the literal
restricted Sylow action. This removes the outside-core branch in source
3.1.6(2), used by 15.1.1(2); transfer to the original normalizer's faithful
action image is left to that consumer. All local and model premises of the
E.2 application are discharged here.

Source: Aschbacher--Smith, printed pp.573--574 and pp.1083--1084.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual outside-core source has cubic ratio strictly below two on its Sylow action. -/
theorem source_outsideCore_sylow_cubicRatio
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hout : ¬localModule T M ≤ H.pCoreIn 2) :
    ∃ hE : IsElementaryAbelian 2 ((localModule T M).subgroupOf H),
      letI := hE
      ∃ hTV : (T.subtype hH.1.1.2 : Subgroup H) ≤
          normalizer ((localModule T M).subgroupOf H : Set H),
        cubicRatio (ChapterE.DihedralCubic.canonicalAction (T.subtype hH.1.1.2)
          ((localModule T M).subgroupOf H) hTV) < 2 := by
  let V := localModule T M
  let S := T.subtype hH.1.1.2
  let W := V.subgroupOf H
  have hMH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let := localModule_elementary_from_source hG T hMH
  have hVM : V ≤ M := localModule_le T hM.1.2
  have hVT : V ≤ (T : Subgroup G) := by
    have hred := localModule_reduced_from_source hG T hMH
    have h := (map_mono hred.le_pCore).trans (pCoreIn_le_sylow M (T.subtype hM.1.2))
    change (V.subgroupOf M).map M.subtype ≤ _ at h
    simpa only [map_subgroupOf_eq_of_le hVM,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using h
  have hVH : V ≤ H := hVT.trans hH.1.1.2
  let hE : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  let := hE
  obtain ⟨_,hP,hmax,hSQ,hfit⟩ := source_centralizing_minimalParabolic hG T hM hJ H hH
  have hB : ChapterB.minimalParabolicMax S hP = (H ⊓ M).subgroupOf H :=
    (ChapterB.minimalParabolicMax_unique S hP hmax (fun x hx => ⟨x.property,hM.1.2 hx⟩)).symm
  have hWS : W ≤ (S : Subgroup H) := fun _ hx => hVT hx
  have hMV : M ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  have hBN : ChapterB.minimalParabolicMax S hP ≤ normalizer (W : Set H) := by
    rw [hB,←subgroupOf_normalizer_eq hVH]
    exact fun _ hx => hMV hx.2
  have hTV : (S : Subgroup H) ≤ normalizer (W : Set H) :=
    (ChapterB.minimalParabolicMax_spec S hP).2.trans hBN
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hP).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W)
      (hWS.trans (ChapterB.minimalParabolicMax_spec S hP).2) hBN
  have hWout : ¬W ≤ ChapterB.minimalParabolicCore S hP := by
    intro he
    have hc : W ≤ pCore 2 H := by
      rw [←ChapterB.minimalParabolic_sylow_inf_core S hP]
      exact le_inf hWS he
    apply hout
    have hm := map_mono (f := H.subtype) hc
    change (V.subgroupOf H).map H.subtype ≤ H.pCoreIn 2 at hm
    simpa only [map_subgroupOf_eq_of_le hVH] using hm
  exact ⟨hE,hTV,ChapterE.Witnesses.source_normal_cubicRatio_lt_two hSQ S hP
    W S hWS hWcore hWout hBN hfit le_rfl hTV⟩

end CFSG.Quasithin.Chapter15.Section01
