module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Sharpening.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Sharpening.OrderFour

/-!
# The edge-action sharpening in MS93 (4.2)(i)

For critical distance four, the initial facts give the source order-four edge
displacement independently of universal edge containment. Its action sharpens
the supplied natural-layer containment to the edge-displacement layer modulo
the actual D_alpha. The neighboring B_alpha hypothesis is retained in the
assembly interface; once the natural-layer bound is supplied, the sharpening
uses no additional information from it.

The nonsplit-extension step producing the natural-layer bound and the final
characteristic-centralizer transfer belong to the parent span-bound proof.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.2)(i), printed p.882.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer.SpanBound
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common in
/-- The unequal-kernel sharpening required by `edgeSpan_le_of_neighbor_steps`.
The order-four equality is proved from the permitted initial distance-four
facts, and the natural-layer containment is the explicit extension input. -/
theorem neighbor_displacement_le_edge_sup_fixedCore
    (hb : geometry.b R = 4) (initial : InitialFacts R geometry)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) (hne : Q R a ≠ Q R d)
    (_hB : ∀ e, Adjacent R e b → ⁅Z R e, Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (hnatural : ⁅Z R d, Q R b⁆ ≤ U R a ⊔ fixedCore R a) :
    ⁅Z R d, Q R b⁆ ≤ ⁅Z R a, Q R b⁆ ⊔ fixedCore R a :=
  Sharpening.neighbor_sharpening_of_card_four common a b d ha hab hdb hne
    (Sharpening.edge_displacement_card_four common hb initial a b ha hab) hnatural

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer.SpanBound
