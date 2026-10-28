module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Source
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Source
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.CompleteCover

/-!
# The completed exterior local source theorems

The proved native Janko four-local cover discharges the last input to the
marked normalizer argument. Thus G₃ and G₆ normalize the original L. Together
with the source component and point-core theorems, these containments supply
the local inputs to point fusion, weak closure and generation exclusion.
The strict-enlargement escape then gives K₁ = L₁ with normality inside G₁.

The final construction aligns the original exterior marking with T and
returns its actual local components and fusion conclusions on the same V.
Only the earlier Structural1222At input remains, with qt-d-1222-source;
qt-d-1251-source retains its discharge and construction of the terminal
configuration for the full exterior exclusion. No native-cover, component,
point-core or normalizer premise remains in these source applications.

Source: Aschbacher--Smith, 12.5.3--4, 12.5.8 and 12.5.11, pp.817--821;
Kleidman--Wilson (1988), Section 2, pp.488--493, for the native Janko cover.
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
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)

include h

/-- Source 12.5.4, with every native placement premise discharged for the
same original projected actor and component marking. -/
theorem local_normalizer_le_M_from_source
    (i : ℕ) (hi : i = 3 ∨ i = 6) : s.marking.Gi i ≤ s.marking.M :=
  s.local_normalizer_le_M_from_native_cover
    Janko4.LocalStructure.PureFirstNormalizers.CompleteCover.maximalTwoLocalCover h i hi

variable (structural : Structural1222At KnownSimple.IsKnownSimple T)

include h structural

/-- Both clauses of 12.5.8 with the original local containments proved. -/
theorem point_core_and_elementary_span_from_local_theorems :
    V ≤ (s.marking.Gi 1).pCoreIn 2 ∧ IsElementaryAbelian 2 s.marking.U :=
  s.point_core_and_elementary_span_from_source h structural
    (s.local_normalizer_le_M_from_source h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_source h 6 (.inr rfl))

/-- Point geometry and fusion on the original module, for the terminal consumer. -/
theorem pointControl_from_source : PointControl s.marking :=
  s.pointControl_from_local_source h structural
    (s.local_normalizer_le_M_from_source h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_source h 6 (.inr rfl))

/-- The first weak closure centralizes the original six-space. -/
theorem first_centralizes_V₆_from_source :
    ChapterE.indexedWeakClosure V (T : Subgroup G) 1 ≤
      centralizer (s.marking.Vi 6 : Set G) :=
  s.first_centralizes_V₆_from_local_source h structural
    (s.local_normalizer_le_M_from_source h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_source h 6 (.inr rfl))

/-- The genuine source generation-one exclusion, without local premises. -/
theorem generation_ne_one_from_source
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ChapterE.generationParameter H ≠ 1 :=
  s.generation_ne_one_from_local_source h structural
    (s.local_normalizer_le_M_from_source h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_source h 6 (.inr rfl)) hH

/-- Source 12.5.11(2) for any original normal containing point component. -/
theorem point_component_eq_from_source
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    s.marking.Li 1 = K :=
  s.point_component_eq_of_source_parameters h structural
    (s.local_normalizer_le_M_from_source h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_source h 6 (.inr rfl)) hK hLK hN

/-- The point residual itself is a C-component, normal relative to G₁. -/
theorem point_component_normal_from_source :
    s.marking.Li 1 ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧
      ((s.marking.Li 1).subgroupOf (s.marking.Gi 1)).Normal :=
  s.point_component_normal_of_source_parameters h structural
    (s.local_normalizer_le_M_from_source h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_source h 6 (.inr rfl))

/-- Discharge all three local inputs to the complete fusion/weak-closure
consumer, including n(H) > 1 and the generation-two Hall-three conclusion. -/
theorem exteriorFusion_from_source : ExteriorFusion s :=
  exteriorFusion_of_local s h structural
    (s.local_normalizer_le_M_from_source h 3 (.inl rfl))
    (s.local_normalizer_le_M_from_source h 6 (.inr rfl))
    (s.seed_le_point_core_from_source h)

/-- Apply the completed local chain to the literal terminal configuration.
Its construction remains with the final exterior source owner. -/
theorem exterior_contradiction_from_source_and_terminal
    (d : TerminalConfiguration s.marking) : False :=
  (s.exteriorFusion_from_source h structural).exterior_contradiction d

end SylowExteriorMarking

/-- Construct the Sylow coordinates on the original V and supply the full
local family and its fusion consumer. The structural input is needed only
at the original G,T; no local conclusion is included among the premises. -/
theorem exists_sylow_marking_with_local_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (a : ExteriorMarking D) :
    ∃ s : SylowExteriorMarking D,
      Nonempty (LocalComponents s) ∧
      (∀ i, i = 3 ∨ i = 6 → s.marking.Gi i ≤ s.marking.M) ∧
      V ≤ (s.marking.Gi 1).pCoreIn 2 ∧ ExteriorFusion s := by
  obtain ⟨s⟩ := a.exists_sylowExteriorMarking ((structural L h).2.2 V D).1
  exact ⟨s, s.local_components_from_source h, s.local_normalizer_le_M_from_source h,
    s.seed_le_point_core_from_source h, s.exteriorFusion_from_source h structural⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
