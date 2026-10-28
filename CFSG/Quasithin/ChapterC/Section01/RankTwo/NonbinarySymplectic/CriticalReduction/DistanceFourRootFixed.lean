module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexIntersectionBound
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexOrbit

/-!
# The critical root commutator is fixed by its first mover

At distance at least four, a reverse critical image smaller than q squared
has both reciprocal images of order q. The full starting seed therefore has
fixed index q under the endpoint seed. The first small-mover join centralizes
its entire displacement, including every central attachment.

This is the first-mover fixedness used in the equal-selector branch of
MS93 (5.12)(1), printed p.925. Neither a strict moving-index bound nor
equality of neighboring movers is needed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The whole critical commutator is fixed by the literal first smaller
mover, already at distance four. -/
theorem Input.replacement_root_critical_commutator_fixed_by_first_mover
    {geometry : Geometry d.radical} {u e : Vertex d.radical}
    (path : CriticalPath d.radical geometry u e) (hb : 4 ≤ geometry.b d.radical)
    (hsmall : (Q d.radical u).relIndex (Z d.radical e) < Nat.card F^2) :
    ⁅Z d.radical u,Z d.radical e⁆ ≤ centralizer
      (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) :
          Set (FreeAmalgam d.radical)) := by
  let t := path.walk.getVert 1
  let rev : CriticalPath d.radical geometry e u :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        u path.start_color (by
          rw [geometry.distance_constant u path.start_color]
          exact lt_of_lt_of_le (by decide : 0 < 4) hb)
        e path.end_color path.critical }
  have hi := (h.replacement_small_critical_indices_eq_field d rev (by omega) hsmall).2
  have hut : Adjacent d.radical u t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have heS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have heT : Z d.radical e ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt _ e (geometry.exists_critical e path.end_color)
    rw [geometry.distance_constant e path.end_color,SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
    change geometry.b d.radical-1 < geometry.b d.radical
    omega
  have huS : Z d.radical u ≤ stabilizer d.radical e :=
    Z_le_stabilizer_of_dist_le u (geometry.exists_critical u path.start_color) path.critical.1.le
  have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) e path.end_color
  have hfixed : Z d.radical u ⊓ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) =
      Z d.radical u ⊓ Q d.radical e := by
    rw [←hC]
    ext x
    exact ⟨fun hx => ⟨hx.1,huS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  let := finite_Z d.radical u
  have hiU : (centralizer (Z d.radical e : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical u) ≤ Nat.card F := by
    apply (relIndex_le_of_le_right (U_le_Z u) index_ne_zero_of_finite).trans
    rw [←inf_relIndex_left,hfixed,inf_relIndex_left,hi]
  rw [h.replacement_Z_commutator_eq_U d geometry hb path.start_color _ heS]
  exact h.replacement_small_mover_join_centralizes_field_displacement d geometry hb
    path.start_color hut _ heT hiU

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
