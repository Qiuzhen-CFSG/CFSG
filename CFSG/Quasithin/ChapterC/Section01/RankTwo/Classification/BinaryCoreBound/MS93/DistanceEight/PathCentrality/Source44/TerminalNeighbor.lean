module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Selection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.EscapeSelection.ImageBounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.EscapeSelection.ImageBounds.SpanRecognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.EscapeSelection.Capture
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.EscapeSelection.Selection

/-!
# The escaping terminal neighbor from the original source

If every radius-two displacement lay in B, the full-radius involution
obstruction and the proved inside-B selector give both source image bounds.
The resulting commutator capture contradicts the backward witness's
nontrivial endpoint triple commutator. Thus an actual displacement escapes B;
relative normal generation selects the required terminal neighbor.

The final theorem constructs both the backward witness and its terminal
neighbor from the original nonnatural case. The later two normalizer
selections on the fixed natural lines remain separate source work.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.4.1), printed p.892, the paragraph following claim (3).
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
open EscapeSelection EscapeSelection.ImageBounds
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

 theorem escaping_neighbor
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a=false) (hc : color R c=false)
    (hd : (cosetGraph R).dist a c=2)
    (hn : ¬⁅Z R a,Q R c⁆≤fixedCore R c)
    (hnone : ¬HasNaturalSection R a c) (w : BackwardWitness R geometry a c) :
    ∃rho, (cosetGraph R).dist c rho=2 ∧
      ¬⁅Z R rho,Q R c⁆≤B R c (geometry.Z_normal c) := by
  by_contra! hall
  have hnat := no_small_radius_involution common hb ha hc hd hn hnone w hall
  have himage := image_bounds_of_involution_obstruction_and_selection
    common hb ha hc hd hn hnone w hall hnat
    (fun _ _ _ hr hx hd hB hn he ht p => inside_conjugate common hb hr hx hd hB hn he ht p)
  obtain ⟨hcap,hcentral⟩ := commutator_capture_and_endpoint_centrality
    common hb ha hd w hall himage.2
  apply w.triple_ne
  exact le_antisymm ((commutator_mono hcap le_rfl).trans hcentral.le) bot_le

 theorem terminal_neighbor
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a=false) (hc : color R c=false)
    (hd : (cosetGraph R).dist a c=2)
    (hn : ¬⁅Z R a,Q R c⁆≤fixedCore R c)
    (hnone : ¬HasNaturalSection R a c) (w : BackwardWitness R geometry a c) :
    Nonempty (TerminalNeighbor w) :=
  terminalNeighbor_of_escape common hb ha w (escaping_neighbor common hb ha hc hd hn hnone w)

/-- Literal consumer: both source choices are constructed on the original pair. -/
theorem exists_terminal_configuration
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a=false) (hc : color R c=false)
    (hd : (cosetGraph R).dist a c=2)
    (hn : ¬⁅Z R a,Q R c⁆≤fixedCore R c)
    (hnone : ¬HasNaturalSection R a c) :
    ∃w : BackwardWitness R geometry a c, Nonempty (TerminalNeighbor w) := by
  obtain ⟨w⟩ := backward_witness common hb ha hc hd hn hnone
  exact ⟨w,terminal_neighbor common hb ha hc hd hn hnone w⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
