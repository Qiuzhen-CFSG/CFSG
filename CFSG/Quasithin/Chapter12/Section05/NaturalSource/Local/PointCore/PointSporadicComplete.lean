module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointSporadicComplete
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointAlternative

/-!
# Local conclusions for the complete sporadic point-model family

The native M22, M23, Held and J1 exclusions finish the sporadic point sieve.
Only M24 and J4 remain, and their already proved residual containment supplies
Y ≤ K₁. The three-space exclusion constructs all original LocalComponents,
and the actual point-core, point-control and generation-one consumers use
those constructed components and the unchanged quotient maps.

The normalizer containments and Structural1222At remain explicit in the
last two consumers: qt-d-1251-local owns the former and the remaining
classical point rows and quasisimple escape; qt-d-1222-source owns the latter.
Final exterior assembly and discharge of earlier inputs is qt-d-1251-source.
Source: Aschbacher--Smith 12.5.3--4, 12.5.8(1), 12.5.11, pp.817--821.
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
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : (∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier)) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model))

include h hK hLK hN hm

/-- The complete sporadic point family construct all original local components. -/
@[expose] def localComponentsOfSporadicPointModel : LocalComponents s :=
  s.localComponentsOfPointAlternative h K hK hLK hN
    (s.local_point_component_alternative_of_sporadic_or_jankoOne h hK hLK hN hm)

/-- Point-core containment, with the actual component refinement constructed. -/
theorem seed_le_point_core_of_sporadic_point_model : V ≤ (s.marking.Gi 1).pCoreIn 2 :=
  s.seed_le_point_core_of_point_alternative h hK hLK hN
    (s.local_point_component_alternative_of_sporadic_or_jankoOne h hK hLK hN hm)

/-- The point-control consumer retains only the earlier structural input and
both pending ambient normalizer containments. -/
theorem pointControl_of_sporadic_point_model
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M) :
    PointControl s.marking :=
  s.pointControl_of_point_alternative h structural hK hLK hN
    (s.local_point_component_alternative_of_sporadic_or_jankoOne h hK hLK hN hm)
    hG₃ hG₆

/-- The generation-one consumer uses the same original component and quotient maps. -/
theorem generation_ne_one_of_sporadic_point_model
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ChapterE.generationParameter H ≠ 1 :=
  s.generation_ne_one_of_point_alternative h structural hK hLK hN
    (s.local_point_component_alternative_of_sporadic_or_jankoOne h hK hLK hN hm)
    hG₃ hG₆ hH

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
