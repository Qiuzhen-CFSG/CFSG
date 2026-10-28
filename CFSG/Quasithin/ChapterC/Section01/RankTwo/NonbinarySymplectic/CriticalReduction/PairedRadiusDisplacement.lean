module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusEscape

/-!
# Noncentral terminal displacement under the small radius budget

The full escaping kernel N = V_a ∩ Q_z moves the penultimate seed Z_e.
The actual neighboring-mover equality puts that same displacement in the
central omega of their common smaller mover. Symplectic duality identifies
its quotient by the complete vertex center with the whole-seed fixed index,
so that quotient has order at least q. The displacement cannot be hidden in
the central attachment.

Source: MS93 (5.11), printed pp.923--924. This retains the original full
kernel N and does not assert the still needed strict radius bound.
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

/-- The same full terminal displacement lies in the central omega of the
literal smaller mover, while its quotient by the full vertex center still
has at least field order. -/
theorem Input.replacement_small_radius_terminal_displacement
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F^2) :
    let e := path.walk.getVert (geometry.b d.radical-2)
    let N := V d.radical a ⊓ Q d.radical z
    let J := Subgroup.SmallMover.join (U d.radical e) (Q d.radical e)
      (Q d.radical (path.walk.getVert (geometry.b d.radical-1))) (Nat.card F^2)
    ⁅Z d.radical e,N⁆ ≤ omegaCenter J ∧
      Nat.card F ≤ (centralizer (stabilizer d.radical e : Set (FreeAmalgam d.radical))).relIndex
        ⁅Z d.radical e,N⁆ := by
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
  obtain ⟨hmove,_,hplace⟩ :=
    h.replacement_small_radius_terminal_kernel_movement d path hb hi
  have hHS : ⁅Z d.radical e,N⁆≤stabilizer d.radical e :=
    hplace.trans (inf_le_left.trans (inf_le_right.trans (Z_le_stabilizer _ _)))
  have hindex : Nat.card F ≤
      (centralizer (stabilizer d.radical e : Set (FreeAmalgam d.radical))).relIndex
        ⁅Z d.radical e,N⁆ := by
    let := finite_Z d.radical e
    have hmoveZ := hmove.trans (relIndex_le_of_le_right (U_le_Z e) index_ne_zero_of_finite)
    have he := h.replacement_displacement_central_index d geometry hb.le hecol N hNS
    rw [commutator_comm N] at he
    have hcent : (stabilizer d.radical e ⊓
        centralizer (stabilizer d.radical e : Set (FreeAmalgam d.radical))).subgroupOf
          ⁅Z d.radical e,N⁆ =
        (centralizer (stabilizer d.radical e : Set (FreeAmalgam d.radical))).subgroupOf
          ⁅Z d.radical e,N⁆ := by
      ext x
      exact ⟨fun hx => hx.2,fun hx => ⟨hHS x.property,hx⟩⟩
    change ((stabilizer d.radical e ⊓ centralizer (stabilizer d.radical e : Set _)).subgroupOf
      ⁅Z d.radical e,N⁆).index=_ at he
    rw [hcent] at he
    exact hmoveZ.trans_eq he.symm
  refine ⟨?_,hindex⟩
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
  obtain ⟨_,hcomm⟩ := h.replacement_equal_root_neighbor_commutator d rev.path hb.le
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
  have hbound : ⁅Z d.radical e,N⁆ ≤ omegaCenter
      (Subgroup.SmallMover.join (U d.radical z) (Q d.radical z)
        (Q d.radical t) (Nat.card F^2)) :=
    (commutator_mono le_rfl (inf_le_right.trans hQJ)).trans hcomm
  rw [←hequal] at hbound
  have ht : t=path.walk.getVert (geometry.b d.radical-1) := by
    change path.walk.reverse.getVert 1=_
    rw [SimpleGraph.Walk.getVert_reverse,path.length_eq_b]
  rwa [ht] at hbound

/-- Full terminal displacement survives modulo the complete vertex center;
in particular it cannot consist only of the central attachment. -/
theorem Input.replacement_small_radius_terminal_displacement_not_central
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F^2) :
    let e := path.walk.getVert (geometry.b d.radical-2)
    ¬ ⁅Z d.radical e,V d.radical a ⊓ Q d.radical z⁆ ≤
      centralizer (stabilizer d.radical e : Set (FreeAmalgam d.radical)) := by
  dsimp only
  intro hc
  have hh := (h.replacement_small_radius_terminal_displacement d path hb hi).2
  rw [relIndex_eq_one.mpr hc] at hh
  have hq : 1 < Nat.card F := Finite.one_lt_card
  omega

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
