module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.MarkedPairing.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.MarkedPairing.IndexTwo

/-!
# Applying the marked fixed-line calculation to the terminal selection

For the supplied TerminalNeighbor, the actual critical pair and its original
first edge are proved in Geometry. The intersection bound, failure of
normalization and triple-commutator obstruction exclude image order two in
IndexTwo. The binary natural-module calculation therefore gives image order
four in both directions. Its fixed-line calculation identifies the selected
commutator with the fixed subgroup of the original first odd-vertex kernel,
and proves that subgroup has order two.

The backward witness and terminal neighbor remain supplied explicitly;
their construction and the ensuing terminal contradiction belong to the
parent argument.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), p.892.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace TerminalNeighbor
variable {a c : Vertex R} {w : BackwardWitness R geometry a c}

/-- Apply the fixed-line calculation to the selected lambda and the original first edge. -/
theorem pairing_of_image_four (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (n : TerminalNeighbor w)
    (hi : (Q R c).relIndex (Z R n.vertex) = 4) :
    (Q R n.vertex).relIndex (Z R c) = 4 ∧
      ⁅Z R n.vertex, Z R c⁆ = edgeFixedNatural c (w.path.walk.getVert 1) ∧
      Nat.card (edgeFixedNatural (R := R) c (w.path.walk.getVert 1)) = 2 := by
  let p := n.criticalPath common hb ha hd
  have hfirst : Adjacent R c (w.path.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    apply w.path.walk.adj_snd
    intro hn
    have hz := hn.length_eq_zero
    have hl := w.path.length_eq_b
    omega
  have hdist := n.first_neighbor_distance common hb ha hd
  refine ⟨(critical_Z_index_reciprocity common p).trans hi, ?_,
    critical_edgeFixedNatural_card common hb p hfirst hdist hi⟩
  rw [commutator_comm]
  exact critical_commutator_eq_edgeFixedNatural common hb p hfirst hdist hi

/-- The selected image has order four: the actual source obstruction excludes order two. -/
theorem image_index_four (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (n : TerminalNeighbor w) :
    (Q R c).relIndex (Z R n.vertex) = 4 :=
  (n.image_indices common hb ha hd).2.resolve_left (n.image_index_ne_two common hb ha hd)

/-- The complete image and fixed-line conclusions for the supplied terminal selection,
with no additional image-order or marked-action premise. -/
theorem pairing (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (n : TerminalNeighbor w) :
    (Q R c).relIndex (Z R n.vertex) = 4 ∧
      CriticalPair R c n.vertex (geometry.exists_critical c w.path.start_color) ∧
      (Q R n.vertex).relIndex (Z R c) = 4 ∧
      ⁅Z R n.vertex, Z R c⁆ = edgeFixedNatural c (w.path.walk.getVert 1) ∧
      Nat.card (edgeFixedNatural (R := R) c (w.path.walk.getVert 1)) = 2 := by
  have hi := n.image_index_four common hb ha hd
  exact ⟨hi, n.critical_from_center common hb ha hd,
    n.pairing_of_image_four common hb ha hd hi⟩

end TerminalNeighbor
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
