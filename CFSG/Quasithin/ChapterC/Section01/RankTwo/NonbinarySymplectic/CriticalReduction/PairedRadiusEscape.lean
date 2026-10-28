module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusBudget

/-!
# Full endpoint-kernel escape under the small radius budget

Suppose the literal radius index is at most q squared. If its full endpoint
kernel lay in the penultimate kernel, adjoining the starting seed would
give a subgroup of index at most q inside that kernel. The actual backward
critical seed gives the opposite inequality. Multiplicativity of finite
indices then identifies the entire penultimate radius kernel with that
seed-kernel join. This supplies both premises of the paired image/kernel
obstruction, on its original conjugator, and contradicts that obstruction.

Thus the full endpoint kernel escapes the penultimate kernel. The literal
natural action detects at least q movement there. Reverse the same path
and use its proved mover agreement: the resulting nonzero commutator lies
in the original radius and both terminal Z-layers. Every kernel and central
attachment is retained.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the first contradiction in (5.11), printed p.923. These results
isolate the remaining full-kernel escape case; they do not exclude it or
prove the strict q-squared radius bound. The remaining (5.11)--(5.12)
exclusions and minimum-replacement distance-two witness remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- On the actual paired selection, the small radius budget forces the
full original endpoint kernel to escape the shifted endpoint kernel. -/
theorem Input.replacement_paired_small_radius_kernel_escape
    {geometry : Geometry d.radical} (p p' : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hl : BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F)) p p')
    (hi : (Q d.radical p.last).relIndex (V d.radical p.first) ≤ Nat.card F^2) :
    ¬ V d.radical p.first ⊓ Q d.radical p.last ≤ Q d.radical p'.last := by
  intro hcontain
  let W := V d.radical p.first
  let D := Z d.radical p.first ⊔ (W ⊓ Q d.radical p.last)
  let T := W ⊓ Q d.radical p'.last
  let := finite_stabilizer d.radical p.first
  let : Finite W := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) p.first p.path.start_color).trans
      (fun _ hx => hx.1))) (inclusion_injective _)
  let : Finite T := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hZaE : Z d.radical p.first ≤ Q d.radical p'.last := by
    rw [hl.last_eq]
    apply Z_le_Q_of_dist_lt _ p.first (geometry.exists_critical p.first p.path.start_color)
    rw [geometry.distance_constant p.first p.path.start_color,
      p.path.dist_start (by rw [p.path.length_eq_b]; omega)]
    change geometry.b d.radical-2 < geometry.b d.radical
    omega
  have hDW : D ≤ W := sup_le (Z_le_VBall d.radical p.first 2) inf_le_left
  have hDT : D ≤ T := le_inf hDW (sup_le hZaE hcontain)
  have hsmall : D.relIndex W ≤ Nat.card F :=
    (h.replacement_small_radius_critical_indices d p.path hb hi).2.2.2
  obtain ⟨t,hchoice,hat,hvt,hfirst⟩ := hl.choice
  have hvW : Z d.radical p'.first ≤ W :=
    le_sup_left.trans (neighbor_seed_join_le_radius hat hvt)
  have hlo : Nat.card F ≤ (Q d.radical p'.last).relIndex W :=
    (h.replacement_critical_indices_ge_field d p'.path (by omega)).1.trans
      (relIndex_le_of_le_right hvW index_ne_zero_of_finite)
  have hprod := relIndex_mul_relIndex D T W hDT inf_le_left
  have hTW : T.relIndex W = (Q d.radical p'.last).relIndex W := inf_relIndex_left _ _
  rw [hTW] at hprod
  have hpos : 0 < D.relIndex T := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hq : 0 < Nat.card F := Nat.card_pos
  have hindex : D.relIndex T = 1 := by nlinarith
  have hTD : T ≤ D := relIndex_eq_one.mp hindex
  have himage : (Q d.radical p'.last).relIndex W ≤ Nat.card F := by nlinarith
  obtain ⟨x,hx,hbad⟩ := h.replacement_paired_radius_image_kernel_obstruction d p p' hb hl
  dsimp only at hbad
  have hax : act d.radical x p.first=p.first := Ltilde_le_stabilizer _ hx
  have hatx : Adjacent d.radical p.first (act d.radical x t) := by
    rw [←hax]
    exact (adjacent_act_iff d.radical x p.first t).mpr hat
  have hvtx : Adjacent d.radical (act d.radical x p'.first) (act d.radical x t) :=
    (adjacent_act_iff d.radical x p'.first t).mpr hvt
  have hYW : Z d.radical p'.first ⊔ Z d.radical (act d.radical x p'.first) ≤ W :=
    sup_le hvW (le_sup_left.trans (neighbor_seed_join_le_radius hatx hvtx))
  rcases hbad with hbad | hbad
  · exact hbad.not_ge ((relIndex_le_of_le_right hYW index_ne_zero_of_finite).trans himage)
  · exact hbad ((inf_le_inf_right _ hYW).trans
      (hTD.trans (sup_le_sup_left inf_le_right _)))

/-- Construct the source pair to obtain full-kernel escape on the original
critical path, without an extra choice or image-bound premise. -/
theorem Input.replacement_small_radius_penultimate_kernel_escape
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F^2) :
    ¬ V d.radical a ⊓ Q d.radical z ≤
      Q d.radical (path.walk.getVert (geometry.b d.radical-2)) := by
  let p : CriticalSegment geometry := ⟨a,z,path⟩
  obtain ⟨p',hl⟩ := exists_backward_link (by omega)
    (pairedRadiusChoice geometry (Nat.card F)) p
    (h.replacement_paired_radius_step d p hb)
  have hh := h.replacement_paired_small_radius_kernel_escape d p p' hb hl hi
  rwa [hl.last_eq] at hh

/-- The escaping full kernel moves the whole penultimate natural layer.
Its nonzero displacement lies in the original radius and both terminal
seeds, using the smaller-mover agreement on the reversed literal path. -/
theorem Input.replacement_small_radius_terminal_kernel_movement
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F^2) :
    let e := path.walk.getVert (geometry.b d.radical-2)
    let N := V d.radical a ⊓ Q d.radical z
    Nat.card F ≤ (centralizer (N : Set (FreeAmalgam d.radical))).relIndex (U d.radical e) ∧
      ⁅Z d.radical e,N⁆ ≠ ⊥ ∧
      ⁅Z d.radical e,N⁆ ≤ (V d.radical a ⊓ Z d.radical e) ⊓ Z d.radical z := by
  dsimp only
  let e := path.walk.getVert (geometry.b d.radical-2)
  let N := V d.radical a ⊓ Q d.radical z
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev := (show CriticalSegment geometry from ⟨a,z,path⟩).reverse hedge (by omega)
  have hrevfirst : rev.first=z := rfl
  have heq : rev.path.walk.getVert 2=e := by
    change path.walk.reverse.getVert 2=e
    rw [SimpleGraph.Walk.getVert_reverse,path.length_eq_b]
  have hecol : color d.radical e=false := by
    rw [←heq]
    exact (rev.path.vertex_color (by rw [rev.path.length_eq_b]; omega)).mpr (by decide)
  have hdist : (cosetGraph d.radical).dist a e=geometry.b d.radical-2 :=
    path.dist_start (by rw [path.length_eq_b]; omega)
  have hNS : N ≤ stabilizer d.radical e := inf_le_left.trans
    (CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.radius_le_stabilizer_of_distance
      d.radical geometry path.start_color (by rw [hdist]; omega))
  have hescape := h.replacement_small_radius_penultimate_kernel_escape d path hb hi
  have hmove := h.replacement_natural_fixed_index_lower d geometry hb.le hecol N hNS hescape
  refine ⟨hmove,?_,?_⟩
  · intro hz
    have hfix : U d.radical e ≤ centralizer (N : Set (FreeAmalgam d.radical)) :=
      (U_le_Z e).trans (commutator_eq_bot_iff_le_centralizer.mp hz)
    rw [relIndex_eq_one.mpr hfix] at hmove
    have hq : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hZeQa : Z d.radical e ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt _ e (geometry.exists_critical e hecol)
    rw [geometry.distance_constant e hecol,SimpleGraph.dist_comm,hdist]
    change geometry.b d.radical-2 < geometry.b d.radical
    omega
  have hNV : ⁅Z d.radical e,N⁆ ≤ V d.radical a :=
    (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp
        ((hZeQa.trans (fun _ hx => hx.1)).trans (DistanceEight.V_normalized d.radical a)))
  have hNe : ⁅Z d.radical e,N⁆ ≤ Z d.radical e :=
    le_normalizer_iff_commutator_le_left.mp (hNS.trans (Z_normalized d.radical e))
  refine le_inf (le_inf hNV hNe) ?_
  let t := rev.path.walk.getVert 1
  have hzt : Adjacent d.radical z t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (rev.path.walk.adj_getVert_succ (by rw [rev.path.length_eq_b]; omega : 0 < rev.path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add,hrevfirst] using hh
  have het : Adjacent d.radical e t := by
    rw [←heq]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (rev.path.walk.adj_getVert_succ (by rw [rev.path.length_eq_b]; omega : 1 < rev.path.walk.length)))
  have hequal : Subgroup.SmallMover.join (U d.radical e) (Q d.radical e)
      (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical z) (Q d.radical z)
        (Q d.radical t) (Nat.card F^2) := by
    have hh := h.replacement_mover_agreement_of_four_lt d rev hb
    simpa only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,
      SimpleGraph.Walk.getVert_zero,heq,hrevfirst] using hh
  have hroot : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2 := by
    rw [(h.replacement_small_radius_critical_indices d path hb hi).1]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  obtain ⟨hcenter,hcomm⟩ := h.replacement_equal_root_neighbor_commutator d rev.path hb.le
    hzt het hroot
    (h.replacement_small_mover_index_le_square_of_four_lt d geometry hb path.end_color hzt) hequal
  have hQJ : Q d.radical z ≤ Subgroup.SmallMover.join (U d.radical z) (Q d.radical z)
      (Q d.radical t) (Nat.card F^2) := by
    obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) path.end_color hzt
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  exact (commutator_mono le_rfl (inf_le_right.trans hQJ)).trans (hcomm.trans hcenter)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
