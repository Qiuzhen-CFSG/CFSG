module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Moving.Endpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Moving.Fixed

/-!
# Opposite quotient saturation and the moving layer

The same marked natural action and its opposite quotient give the lower index
four for W = localZSpan(start,center). The elementary endpoint image bounds the
index of V_c intersect Q_b in V_c by four, forcing V_c = (V_c intersect Q_b) W.
The radius commutator bound then extends to V_c, and normal generation inside
the finite center stabilizer gives the literal containment Vcirc_c <= W.

Only the image-index hypothesis remains explicit. Its producer and the
unconditional ForwardFacts assembly belong to the parent task. No favorable
orientation, trapped-radius counterexample or LocalControlAt is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath.Continuation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}
variable {s : SelectedPath R geometry a c} (w : s.Continuation)

/-- The moving-layer containment from the sole additional image-index premise. -/
theorem moving_le_span_of_span_index (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (hindex : (Q R s.center).relIndex (s.continuationSpan w) = 4) :
    Vcirc R s.center ≤ localZSpan R s.start s.center :=
  w.moving_le_span_of_radius_commutator source hb hindex
    (w.radius_commutator_le_span_of_saturation common hb
      (s.radius_eq_kernel_sup_span_of_index common hb (w.span_endpoint_index_ge_four common hb)))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath.Continuation
