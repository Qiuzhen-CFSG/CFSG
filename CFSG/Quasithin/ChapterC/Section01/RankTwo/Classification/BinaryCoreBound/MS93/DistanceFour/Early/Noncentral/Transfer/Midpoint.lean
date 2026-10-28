module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer.Midpoint.Contracts
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer.Midpoint.Source.Assembly

/-!
# Midpoint edge-plane centrality

A central-product witness supplies an actual midpoint-edge conjugating
element. The marked edge layer has index four over its local fixed part,
whereas that element moves at most one binary dimension. The conjugated
center fixed-point inclusion from Basic makes these bounds incompatible.

The imported source assembly proves the full midpoint implication from the
common, initial and edge facts. It uses the genuine relative normalizer,
retained-line comparison, orbit generation and reversed-pair center span.
The older conditional theorem below preserves the edge-stabilizer interface;
the source proof constructs its actors through the corrected normalizer route.

Source: Meierfrankenfeld--Stellmacher (1993), the second (4.6.6), pp.903--904.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Discharge the midpoint comparison from its genuine central-product
witness. Constructing that witness remains an explicit source obligation. -/
theorem critical_edge_plane_central_of_center_span
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (span : Midpoint.CenterSpan geometry)
    (d e c b : Vertex R) (hd : color R d = false)
    (hcrit : CriticalPair R d e (geometry.exists_critical d hd))
    (hdc : (cosetGraph R).dist d c = 2) (hce : (cosetGraph R).dist c e = 2)
    (hdb : Adjacent R d b) (hcb : Adjacent R c b)
    (hcentral : ⁅V R d, V R d⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype) :
    ⁅Z R d, Q R b⁆ ≤ (center (stabilizer R c)).map (stabilizer R c).subtype := by
  by_contra hnot
  obtain ⟨h, _, _, hspan, hsmall⟩ := span d e c b hd hcrit hdc hce hdb hcb hcentral hnot
  exact Midpoint.not_edge_center_span_of_small_fixed_index common edge d b hd hdb h hsmall hspan

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
