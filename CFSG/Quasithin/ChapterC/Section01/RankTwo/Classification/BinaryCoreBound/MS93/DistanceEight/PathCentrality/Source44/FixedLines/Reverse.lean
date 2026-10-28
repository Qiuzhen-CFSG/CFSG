module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.FixedLines.Switching
/-!
# The opposite backward witness and radius intersection

The selected terminal failure of normalization implies the opposite triple
commutator is nonzero. Reverse the original shifted critical path. Its
predecessor is the original center, so it gives a genuine backward witness
with the terminal vertex as backward seed. Claim (3) then controls the
opposite radius intersection, including every seed in the original radius.

The argument retains the original terminal neighbor and uses no extra
normalizer or index premise. Its application to the first selected pair
supplies the opposite intersection estimate needed in the terminal branch.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), printed p.892,
claim (3) and the terminal configuration.
-/
public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
theorem terminal_opposite_triple_ne (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (w : BackwardWitness R geometry a c) (n : TerminalNeighbor w) :
    ⁅⁅Z R n.vertex,Q R w.predecessor⁆,Z R w.backward⁆ ≠ ⊥ := by
  intro hz
  apply n.not_normalizes
  have hE : Z R w.backward ≤ normalizer (⁅Z R n.vertex,Q R w.predecessor⁆ : Subgroup (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr (hz.le.trans bot_le)
  have hZ : Z R w.backward ≤ normalizer (Z R w.predecessor) :=
    (((w.shifted ha (by omega)).reverse common).endpoint_Z_le_start_stabilizer (by omega)).trans
      (Z_normalized R _)
  exact (le_inf hE hZ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem reverse_backward_witness (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) :
    ∃ v : BackwardWitness R geometry n.vertex w.predecessor,
      v.endpoint = w.backward ∧ v.backward = n.vertex ∧ v.conjugator = 1 ∧
      v.predecessor = c := by
  let p := (w.shifted ha (by omega)).reverse common
  have hpred : p.walk.getVert (p.walk.length - 2) = c := by
    change (w.shifted ha (by omega)).walk.reverse.getVert
      ((w.shifted ha (by omega)).walk.reverse.length - 2) = c
    rw [SimpleGraph.Walk.getVert_reverse,SimpleGraph.Walk.length_reverse]
    have hlen := (w.shifted ha (by omega)).length_eq_b
    have hi : (w.shifted ha (by omega)).walk.length -
        ((w.shifted ha (by omega)).walk.length - 2) = 2 := by omega
    rw [hi]
    exact (w.shifted_overlap ha (by omega) (i := 0) (Nat.zero_le _)).trans
      (SimpleGraph.Walk.getVert_zero _)
  obtain ⟨back,hback⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist n.vertex w.predecessor
  have hback2 : back.length = 2 := by rw [hback,SimpleGraph.dist_comm,n.distance]
  let v : BackwardWitness R geometry n.vertex w.predecessor := {
    endpoint := w.backward
    path := p
    backward := n.vertex
    conjugator := 1
    local_conjugator := (stabilizer R w.predecessor).one_mem
    conjugator_image := act_one R _
    backwardWalk := back
    backward_length := hback2
    noncontainment := by rw [hpred]; exact n.not_le_center_kernel common hb ha hd
    triple_ne := terminal_opposite_triple_ne common hb ha w n }
  exact ⟨v,rfl,rfl,rfl,hpred⟩

theorem opposite_radius_intersection (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) :
    ⁅Z R n.vertex,V R c ⊓ Q R w.predecessor⁆ = ⁅Z R n.vertex,Z R c⁆ := by
  obtain ⟨v,hv,hback,hg,hpred⟩ := reverse_backward_witness common hb ha hd w n
  have hdist : (cosetGraph R).dist n.vertex w.predecessor = 2 := by
    rw [SimpleGraph.dist_comm,n.distance]
  have h := source_claim_three common hb n.color hdist v
  simpa only [hback,hpred] using h

theorem opposite_intersection_bound (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {d : Vertex R} (hdc : (cosetGraph R).dist d c ≤ 2) :
    ⁅Z R n.vertex,Z R d ⊓ Q R w.predecessor⁆ ≤ Z R c := by
  apply (commutator_mono le_rfl (inf_le_inf_right _
    (show Z R d ≤ V R c from le_iSup_of_le d (le_iSup_of_le hdc le_rfl)))).trans
  rw [opposite_radius_intersection common hb ha hd w n]
  exact le_normalizer_iff_commutator_le_right.mp
    ((n.criticalPath common hb ha hd).endpoint_Z_le_start_stabilizer (by omega) |>.trans (Z_normalized R c))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
