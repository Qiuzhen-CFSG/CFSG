module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.JankoComponent
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Consumers

/-!
# Point-core containment in the original exterior consumers

All point-core model rows are now discharged. Applying this to the existing
source weak-closure results proves both clauses of 12.5.8, constructs the
literal PointControl, and supplies the point-core input to the original
H-star generation-one exclusion and the terminal contradiction.

The remaining component alternatives and G₃,G₆ normalizer containments
belong to qt-d-1251-local. Structural1222At is the earlier source input
from qt-d-1222-source. The independent weak-closure and terminal work is
owned by qt-d-1251-fusion; qt-d-1251-source discharges the remaining inputs
in the final exterior assembly. No terminal configuration is asserted here.

Source: Aschbacher--Smith, 12.5.8--11 and the proof of 12.5.1,
printed pp.820--822.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- Both clauses of 12.5.8 from the earlier component and normalizer results.
The original U is the G₁-normal closure of the unchanged chosen module. -/
theorem point_core_and_elementary_span
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (c : LocalComponents s)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 ∧ IsElementaryAbelian 2 s.marking.U :=
  ⟨s.seed_le_point_core h c,
    elementary_point_span_of_source_parameters s h structural hG₃ hG₆
      (s.seed_le_point_core h c)⟩

/-- The original point-fusion consumer, with point-core containment discharged. -/
theorem pointControl_of_local_components
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (c : LocalComponents s)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M) : PointControl s.marking :=
  pointControl_of_source_parameters s h structural hG₃ hG₆ (s.seed_le_point_core h c)

/-- Apply the original H-star generation-one exclusion with its point-core
premise proved by the component analysis. -/
theorem generation_ne_one_of_local_components
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (c : LocalComponents s)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ChapterE.generationParameter H ≠ 1 :=
  generation_ne_one_of_source_parameters s h structural hG₃ hG₆
    (s.seed_le_point_core h c) hH

/-- Apply the terminal exterior contradiction after discharging point-core
containment. The final owner still constructs the terminal configuration. -/
theorem exterior_contradiction_of_local_components_and_terminal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (c : LocalComponents s)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (d : TerminalConfiguration s.marking) : False :=
  exterior_contradiction_of_source_parameters_and_terminal s h structural hG₃ hG₆
    (s.seed_le_point_core h c) d

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
