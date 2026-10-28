module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inequality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Normalizer

/-!
# The selected neighbor and fixed subgroup in the terminal argument

TerminalNeighbor records the actual lambda selected after the all-rho-in-B
contradiction on p.892, including its failure of normalization. No constructor
from the original hypotheses is claimed here. The two following consequences
apply the already proved claim (3) and source (2.1)(vi) to that same lambda.

The edge-fixed natural subgroup uses Q at the odd vertex, the source T. It
is distinct from the fixed preimage B on V/Z and from the fixed core D.
Its identification with a critical commutator is a further proof obligation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), printed p.892, after claim (3).
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

/-- The fixed subgroup of the actual natural layer under the actual odd-vertex
kernel. Its order and its identification with a commutator require proofs. -/
noncomputable def edgeFixedNatural (a t : Vertex R) : Subgroup (FreeAmalgam R) :=
  U R a ⊓ centralizer (Q R t : Set (FreeAmalgam R))

/-- The selected lambda on p.892. This type retains its exact distance from
alpha'-2 and the source failure of normalization; no existence is asserted. -/
structure TerminalNeighbor {a c : Vertex R} (w : BackwardWitness R geometry a c) where
  vertex : Vertex R
  distance : (cosetGraph R).dist w.predecessor vertex = 2
  not_normalizes : ¬ Z R w.backward ≤ normalizer
    (⁅Z R vertex, Q R w.predecessor⁆ ⊔ Z R w.predecessor : Subgroup (FreeAmalgam R))

namespace TerminalNeighbor
variable {a c : Vertex R} {w : BackwardWitness R geometry a c}

/-- The chosen lambda has M-color. -/
theorem color (n : TerminalNeighbor w) : Stellmacher.PushingUp.AmalgamGraph.color R n.vertex = false :=
  (color_eq_of_dist_even R w.predecessor n.vertex (by rw [n.distance]; decide)).symm.trans
    w.predecessor_color

/-- Apply claim (3) at the actual selected neighboring vertex. -/
theorem intersection_bound [Finite M] (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (n : TerminalNeighbor w) :
    ⁅Z R n.vertex ⊓ Q R c, Z R w.backward⁆ ≤ Z R w.predecessor :=
  neighboring_intersection_commutator_le common hb ha hd w
    (by rw [SimpleGraph.dist_comm, n.distance])

/-- The exact source-ordered obstruction needed for the image-order calculation. -/
theorem triple_noncontainment [Finite M] (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (ha : Stellmacher.PushingUp.AmalgamGraph.color R a = false)
    (n : TerminalNeighbor w) :
    ¬ ⁅Z R n.vertex, Z R w.backward⁆ ≤
      ⁅⁅Z R n.vertex, Q R w.predecessor⁆, Z R w.backward⁆ ⊔ Z R w.predecessor :=
  commutator_not_le_triple_sup common hb ha w n.distance n.not_normalizes

end TerminalNeighbor
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
