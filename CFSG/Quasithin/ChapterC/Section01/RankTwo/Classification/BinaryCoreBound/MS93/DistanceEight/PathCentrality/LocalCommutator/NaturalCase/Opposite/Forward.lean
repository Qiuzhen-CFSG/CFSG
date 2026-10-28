module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Index
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Moving

/-!
# Forward continuations in the opposite natural case

The complete avoiding ordered-pair orbit, its criticality, the pointwise
edge/kernel identities, and the generated endpoint plane are proved in the
imports. The full local orbit span has the source radius commutator bound
and order-four natural displacement. Its elementary marked image has order four;
duality on the opposite quotient then forces radius saturation and the
moving-layer containment. `forwardFacts` assembles all eight conclusions for
the supplied selected path, discharging the index premise of the moving-layer
calculation with the actual continuation span.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}

/-- Assemble the continuation calculations with explicit index and moving-layer
inputs. `forwardFacts` below supplies both from the source hypotheses. -/
theorem forwardFacts_of_index_and_moving (s : SelectedPath R geometry a c)
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hindex : ∀ w : s.Continuation, (Q R s.center).relIndex (s.continuationSpan w) = 4)
    (hmoving : Vcirc R s.center ≤ localZSpan R s.start s.center) : s.ForwardFacts where
  continuation_exists := s.continuation_exists common (by omega)
  critical w := ⟨s.center_color (by omega), w.critical common hb⟩
  commutator_eq w := w.commutator_eq common hb
  generated_eq := s.generated_eq common hb
  generated_card := s.generated_card common hb
  span_index := hindex
  radius_commutator w := w.radius_commutator common hb
  moving_le_span := hmoving

/-- The forward calculation of MS93 (4.4.1)(1), for every selected path and
every avoiding ordered-pair continuation, with no additional source premise. -/
theorem forwardFacts (s : SelectedPath R geometry a c)
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R) :
    s.ForwardFacts := by
  obtain ⟨w⟩ := s.continuation_exists common (by omega)
  exact s.forwardFacts_of_index_and_moving common hb
    (fun w => w.span_index common hb)
    (w.moving_le_span_of_span_index common hb (w.span_index common hb))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath
