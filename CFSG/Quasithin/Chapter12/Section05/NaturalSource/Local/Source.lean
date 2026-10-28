module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoSource
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.JankoEscape

/-!
# The complete local source chain under the native Janko cover

All normalizer branches are now proved from the named four-local cover.
Apply them to the existing source point-core, point-control, weak-closure,
generation-one and strict-enlargement theorems. In particular the original
point residual is its normal containing C-component, with relative normality
inside G1. The terminal implication keeps the original configuration.

The only added native premise is MaximalTwoLocalCover, whose producer is
qt-model-j4-elementary-normalizer-cover. Its discharge remains with
qt-d-1251-local. Structural1222At retains qt-d-1222-source, the terminal
configuration retains its existing source producer, and qt-d-1251-source
owns final exterior assembly. These conditional applications do not assert
the unfinished cover or the unconditional exterior exclusion.
Source: Aschbacher--Smith 12.5.3--4, 12.5.8(1), 12.5.11(2), pp.818--822.
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
variable (cover : Janko4.LocalStructure.LargeCenterRadicals.MaximalTwoLocalCover)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)

include cover h structural

theorem point_core_and_elementary_span_from_native_cover :
    V ≤ (s.marking.Gi 1).pCoreIn 2 ∧ IsElementaryAbelian 2 s.marking.U :=
  s.point_core_and_elementary_span_from_source h structural
    (s.local_normalizer_le_M_from_native_cover cover h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_native_cover cover h 6 (.inr rfl))

theorem pointControl_from_native_cover : PointControl s.marking :=
  s.pointControl_from_local_source h structural
    (s.local_normalizer_le_M_from_native_cover cover h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_native_cover cover h 6 (.inr rfl))

theorem first_centralizes_V₆_from_native_cover :
    ChapterE.indexedWeakClosure V (T : Subgroup G) 1 ≤
      centralizer (s.marking.Vi 6 : Set G) :=
  s.first_centralizes_V₆_from_local_source h structural
    (s.local_normalizer_le_M_from_native_cover cover h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_native_cover cover h 6 (.inr rfl))

theorem generation_ne_one_from_native_cover
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ChapterE.generationParameter H ≠ 1 :=
  s.generation_ne_one_from_local_source h structural
    (s.local_normalizer_le_M_from_native_cover cover h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_native_cover cover h 6 (.inr rfl)) hH

theorem point_component_eq_from_native_cover
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    s.marking.Li 1 = K :=
  s.point_component_eq_of_source_parameters h structural
    (s.local_normalizer_le_M_from_native_cover cover h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_native_cover cover h 6 (.inr rfl)) hK hLK hN

theorem point_component_normal_from_native_cover :
    s.marking.Li 1 ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧
      ((s.marking.Li 1).subgroupOf (s.marking.Gi 1)).Normal :=
  s.point_component_normal_of_source_parameters h structural
    (s.local_normalizer_le_M_from_native_cover cover h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_native_cover cover h 6 (.inr rfl))

theorem exterior_contradiction_from_native_cover_and_terminal
    (d : TerminalConfiguration s.marking) : False :=
  s.exterior_contradiction_from_local_source_and_terminal h structural
    (s.local_normalizer_le_M_from_native_cover cover h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_native_cover cover h 6 (.inr rfl)) d

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
