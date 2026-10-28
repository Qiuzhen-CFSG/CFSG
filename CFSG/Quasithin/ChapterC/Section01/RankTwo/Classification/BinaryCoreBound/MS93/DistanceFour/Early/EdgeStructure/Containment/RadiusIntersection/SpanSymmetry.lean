module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIntersection.SpanSymmetry.Index
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIntersection.SpanSymmetry.Centralization

/-!
# Paired conjugate-span symmetry

The escaping neighbor constructs two actual transported spans. The symmetry
argument bounds the literal index [Z_e : Z_e intersect B_a] by two, and the
radius displacement argument proves that this intersection centralizes V_a.
Both conclusions hold for the same constructed pair, with B_a retaining its
quotient-fixed definition and V_a the actual radius group.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.4), second paragraph, printed p.902. The subsequent Z-intersection
index calculation is the responsibility of the RadiusIntersection consumer.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The paired spans from the escaping neighbor satisfy both source bounds:
the midpoint's B-intersection has index at most two and centralizes the radius. -/
theorem paired_span_bounds
    (common : CommonFacts R source geometry) (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ∃ p : SpanOffender.PairedSpans geometry a b d ha,
      (B R a (geometry.Z_normal a)).relIndex (Z R p.e) ≤ 2 ∧
      Z R p.e ⊓ B R a (geometry.Z_normal a) ≤
        centralizer (V R a : Set (FreeAmalgam R)) := by
  obtain ⟨p⟩ := SpanOffender.pairedSpans_nonempty common initial hb a b d ha hab hdb hbad
  exact ⟨p, paired_span_index_le_two common initial hb a b d ha hab hdb hbad p,
    paired_fixed_centralizes_radius common initial hb a b d ha hab hdb hbad p⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry
