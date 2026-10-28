module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt.Faithful
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality

/-!
# Actual full-point components are maximal in the local family

An overcomponent contained in the point stabilizer lies in an actual
C-component there by 1.2.4, hence equals the original component. An escaping
overcomponent is faithful and the earlier small-model classification gives
the same equality. Applying 1.2.4 again therefore makes a Sylow-normalized
full-point component normal in every containing two-local overgroup.
Source: Aschbacher–Smith 14.7.46, printed p.1063.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A genuine component of the full point stabilizer is maximal among the
original local components. Its quotient model is not an extra hypothesis. -/
theorem full_point_component_maximal_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (C : Subgroup F.H) (hC : C.IsCComponent) :
    C.map F.H.subtype ∈ Chapter1.LStar G (T : Subgroup G) := by
  let K := C.map F.H.subtype
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  have hKH : K ≤ F.H := map_subtype_le _
  have hc : (K.subgroupOf F.H).IsCComponent := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective] using hC
  have hK : K ∈ Chapter1.L G (T : Subgroup G) := Chapter1.mem_L_of_cComponent hH.1.1
    ⟨T.subtype hTH,by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
    hKH hc
  refine ⟨hK,?_⟩
  intro D hD hKD
  by_cases hDH : D ≤ F.H
  · have hl : D.subgroupOf F.H ∈ Chapter1.L F.H ((T : Subgroup G).subgroupOf F.H) :=
      (Chapter1.mem_LIn_iff_subgroupOf hTH hDH).mp ⟨hDH,hD⟩
    obtain ⟨E,⟨hE,hDE⟩,_⟩ :=
      Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
        (Chapter1.Section02.containment_of_theoremsAC
          (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
          (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)))
        (local_star_sqtk h F.H hH) (T.subtype hTH) hl
    have hCE : K.subgroupOf F.H ≤ E := (subgroupOf_mono F.H hKD).trans hDE
    have he := hc.eq_of_le hE hCE
    have hDK : D ≤ K := by
      have hm := map_mono (f := F.H.subtype) (hDE.trans he.ge)
      simpa only [map_subgroupOf_eq_of_le hDH,map_subgroupOf_eq_of_le hKH] using hm
    exact le_antisymm hDK hKD
  · exact (local_overcomponent_eq_of_outside_point_at d h faithful hD hK hKD hDH).symm

/-- The same original component is normal in every containing group with
nonzero two-core. Source 1.2.4 constructs the overcomponent internally. -/
theorem full_point_component_normal_in_overgroup_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (C : Subgroup F.H) (hC : C.IsCComponent) [C.Normal]
    {J : Subgroup G} (hKJ : C.map F.H.subtype ≤ J) (hTJ : (T : Subgroup G) ≤ J)
    (hcore : J.pCoreIn 2 ≠ ⊥) : ((C.map F.H.subtype).subgroupOf J).Normal := by
  let K := C.map F.H.subtype
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hmax := full_point_component_maximal_at d h previous faithful C hC
  have hlocal : K.subgroupOf J ∈ Chapter1.L J ((T : Subgroup G).subgroupOf J) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTJ hKJ).mp ⟨hKJ,hmax.1⟩
  have hnC : (K.subgroupOf F.H).Normal := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective] using
      (inferInstance : C.Normal)
  have hHK : F.H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp hnC
  have hn : (T.subtype hTJ : Subgroup J) ≤ normalizer (K.subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq hKJ]
    exact subgroupOf_mono J (hTH.trans hHK)
  obtain ⟨D,⟨hD,hKD,hnD⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk d.qtke hcore)
      (T.subtype hTJ) hlocal hn
  let K₀ := D.map J.subtype
  have hK₀J : K₀ ≤ J := map_subtype_le _
  have he : K₀.subgroupOf J = D := comap_map_eq_self_of_injective J.subtype_injective D
  have hc : (K₀.subgroupOf J).IsCComponent := he.symm ▸ hD
  have hKK₀ : K ≤ K₀ := by
    simpa only [map_subgroupOf_eq_of_le (show K ≤ J from hKJ)] using
      map_mono (f := J.subtype) hKD
  have hK₀ : K₀ = K := hmax.2 K₀
    (Chapter1.mem_L_of_cComponent hcore
      ⟨T.subtype hTJ,by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ]⟩ hK₀J hc) hKK₀
  have hh : (K₀.subgroupOf J).Normal := he.symm ▸ hnD
  simpa only [hK₀] using hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
