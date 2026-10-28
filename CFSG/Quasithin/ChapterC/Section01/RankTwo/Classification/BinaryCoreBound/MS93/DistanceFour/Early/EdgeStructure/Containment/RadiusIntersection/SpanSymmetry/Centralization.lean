module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIntersection.SpanSymmetry.Centralization.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIntersection.SpanSymmetry.Centralization.LineExclusion

/-!
# The paired B-intersection and the radius

The actual natural radius displacement [U_e,V_a] has order two or four.
The midpoint-span argument excludes order two, so the order-four reduction
proves that Z_e intersect B_a centralizes the entire radius V_a. This
discharges the displacement-cardinality premise from the early source
hypotheses and the actual paired spans.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.4), printed p.902.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The paired midpoint's quotient-fixed B-intersection centralizes the actual radius,
as asserted in the second paragraph of MS93 (4.6.4). -/
theorem paired_fixed_centralizes_radius
    (common : CommonFacts R source geometry) (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (p : SpanOffender.PairedSpans geometry a b d ha) :
    Z R p.e ⊓ B R a (geometry.Z_normal a) ≤
      centralizer (V R a : Set (FreeAmalgam R)) := by
  have hcard := (paired_radius_displacement_structure common initial a b d ha p).1
  have hfour := hcard.resolve_left
    (paired_radius_displacement_ne_two common initial hb a b d ha hab hdb hbad p)
  exact paired_fixed_centralizes_radius_of_displacement_card common initial hb a b d ha p hfour

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry
