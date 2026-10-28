module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Membership
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original

/-!
# Normal containing components for the exterior local residuals

The literal Lᵢ belong to the local family and are normalized by the original
Sylow T. Since Gᵢ is two-local, QTKE supplies its SQTK hypothesis. Applying
source 1.2.4 inside Gᵢ gives the unique normal containing C-component, then
subtype transport returns it to the original ambient group.

This proves the existence and relative normality assertion of 12.5.3.
Its refined alternatives, including the Ξ₇ case, remain to be established.
Source: Aschbacher--Smith, opening of 12.5.3, printed p.817.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The existence and relative normality assertion at the start of 12.5.3.
The refined alternatives require the subsequent source exclusions. -/
theorem exists_unique_normal_local_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (i : ℕ) (hi : LocalIndex i) :
    ∃! K : Subgroup G, K ∈ Chapter1.cComponentsIn (s.marking.Gi i) ∧
      s.marking.Li i ≤ K ∧ (K.subgroupOf (s.marking.Gi i)).Normal := by
  let H := s.marking.Gi i
  have hT : (T : Subgroup G) ≤ H := s.sylow_le_Gi i hi
  have hL : s.marking.Li i ≤ H := s.marking.Li_le_Gi i
  have hlocal : (s.marking.Li i).subgroupOf H ∈ Chapter1.L H (T.subtype hT) := by
    simpa only [Sylow.coe_subtype] using
      (Chapter1.mem_LIn_iff_subgroupOf hT hL).mp ⟨hL, s.Li_mem_local i hi⟩
  have hnorm : (T.subtype hT : Subgroup H) ≤
      normalizer ((s.marking.Li i).subgroupOf H : Set H) := by
    intro t ht b
    exact s.sylow_normalizes_Li i hi ht (b : G)
  have hQ := ChapterE.Structure.sqtk_two_quotient
    (h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal i hi)) (pCore 2 H) pCore_isPGroup
  obtain ⟨K, ⟨hK, hLK, hn⟩, hu⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ (T.subtype hT) hlocal hnorm
  have he : (K.map H.subtype).subgroupOf H = K :=
    comap_map_eq_self_of_injective H.subtype_injective _
  refine ⟨K.map H.subtype, ⟨⟨map_subtype_le _, he.symm ▸ hK⟩, ?_, he.symm ▸ hn⟩, ?_⟩
  · simpa only [map_subgroupOf_eq_of_le hL] using map_mono (f := H.subtype) hLK
  · intro J hJ
    have hj := hu (J.subgroupOf H) ⟨hJ.1.2, comap_mono hJ.2.1, hJ.2.2⟩
    exact (map_subgroupOf_eq_of_le (show J ≤ H from hJ.1.1)).symm.trans
      (congrArg (map H.subtype) hj)
end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
