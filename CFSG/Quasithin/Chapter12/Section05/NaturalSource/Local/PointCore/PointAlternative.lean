module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.ThreeExclusion
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.PointControl
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Consumers

/-!
# Point-component refinement supplies the original point-core consumers

The three-space radical is excluded by seven-rank, so a refined point
component constructs all four local components. Apply the original
point-core, point-control and generation-one theorems to that construction.
The equal-point branch also gives both ambient normalizer containments.

The point-component refinement, other branches of the normalizer
containments and quasisimple strict-enlargement escape remain obligations
of qt-d-1251-local. The final exterior assembly is qt-d-1251-source.
Source: Aschbacher--Smith, 12.5.3--4, 12.5.8 and 12.5.11, pp.817--821.
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

/-- The full original point-core result requires only the refined point
component; no component or normality premise at index three remains. -/
theorem seed_le_point_core_of_point_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {C : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLC : s.marking.Li 1 ≤ C) (hNC : (C.subgroupOf (s.marking.Gi 1)).Normal)
    (ha : LocalComponentAlternative s 1 C) : V ≤ (s.marking.Gi 1).pCoreIn 2 :=
  s.seed_le_point_core h (s.localComponentsOfPointAlternative h C hC hLC hNC ha)

/-- The equal-point branch supplies both normalizer containments and the
point core, with the entire LocalComponents input constructed. -/
theorem local_containments_of_point_residual_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hC : s.marking.Li 1 ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hN : ((s.marking.Li 1).subgroupOf (s.marking.Gi 1)).Normal) :
    s.marking.Gi 3 ≤ s.marking.M ∧ s.marking.Gi 6 ≤ s.marking.M ∧
      V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  let c := s.localComponentsOfPointAlternative h (s.marking.Li 1) hC le_rfl hN (.equal rfl)
  exact s.local_containments_of_point_component_eq h c (by
    dsimp [c,localComponentsOfPointAlternative])

/-- Feed the literal point-fusion consumer with the newly constructed components. -/
theorem pointControl_of_point_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) {C : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLC : s.marking.Li 1 ≤ C) (hNC : (C.subgroupOf (s.marking.Gi 1)).Normal)
    (ha : LocalComponentAlternative s 1 C)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M) :
    PointControl s.marking :=
  s.pointControl_of_local_components h structural
    (s.localComponentsOfPointAlternative h C hC hLC hNC ha) hG₃ hG₆

/-- The actual generation-one exclusion now has no separate three-space premise. -/
theorem generation_ne_one_of_point_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) {C : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLC : s.marking.Li 1 ≤ C) (hNC : (C.subgroupOf (s.marking.Gi 1)).Normal)
    (ha : LocalComponentAlternative s 1 C)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ChapterE.generationParameter H ≠ 1 :=
  s.generation_ne_one_of_local_components h structural
    (s.localComponentsOfPointAlternative h C hC hLC hNC ha) hG₃ hG₆ hH

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
