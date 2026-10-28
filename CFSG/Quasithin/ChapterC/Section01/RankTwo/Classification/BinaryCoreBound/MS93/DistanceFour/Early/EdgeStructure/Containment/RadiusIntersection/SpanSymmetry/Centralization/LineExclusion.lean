module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIntersection.SpanSymmetry.Centralization.LineExclusion.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIntersection.SpanSymmetry.Centralization.LineExclusion.Action

/-!
# Excluding the paired radius displacement line

For the actual paired midpoint e, the span W = ⟨Z_e^{G_a}⟩ is nonabelian.
Its seed's B-intersection centralizes W and has index at most two. If
[U_e,V_a] had order two, evaluation on U_e would bound the image of W
in G_e/Q_e by two, while conjugate generation would identify W' with
the original central line [Z_d,Q_a]. The faithful self-dual action on
W/Z(W) then has a critical-endpoint offender, a contradiction.

This discharges the remaining line case with the actual natural subgroup,
radius, quotient-fixed B, and paired conjugations. The unconditional
centralization assembly remains in the parent Centralization module.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.4), second paragraph, printed p.902.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The actual paired radius displacement cannot be a line. All span and
module premises are discharged from the stated early source hypotheses. -/
theorem paired_radius_displacement_ne_two
    (common : CommonFacts R source geometry) (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (p : SpanOffender.PairedSpans geometry a b d ha) :
    Nat.card (⁅U R p.e,V R a⁆ : Subgroup (FreeAmalgam R)) ≠ 2 := by
  intro hcard
  have hderived := paired_radius_line_span_derived common hb a b d ha hab p hcard
  exact LineExclusion.midpoint_span_not_small_of_derived_line common initial a b d ha hab p
    (by rw [hderived]; exact p.card_left)
    (by rw [hderived]; exact p.central_left)
    (paired_radius_line_span_image_le_two common initial hb a b d ha hab hdb hbad p hcard)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry
