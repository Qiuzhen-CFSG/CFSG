module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusPenultimateKernel

/-!
# Strict growth across the two actual endpoint kernels

If the original radius image exceeds q squared, intersecting its kernel
with the penultimate kernel preserves that strict bound. In the other
case, the actual paired backward selection gives more than q images at
the penultimate vertex. The original seed lies in that kernel and has q
images at the original endpoint. Multiplication of the full relative
indices therefore gives more than q squared images modulo their
intersection, with no radius-budget premise remaining.

Reverse the same critical path to obtain the two strict index alternatives
used in the last paragraph of MS93 (5.11), printed p.924. This does not
identify either kernel with their intersection, assert a strict bound for
the original endpoint alone, or supply the remaining commutator premises.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full radius has more than q squared images modulo the intersection
of its actual critical and penultimate endpoint kernels. -/
theorem Input.replacement_two_kernel_radius_index_gt_square
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical) :
    Nat.card F^2 < (Q d.radical z ⊓
      Q d.radical (path.walk.getVert (geometry.b d.radical-2))).relIndex
        (V d.radical a) := by
  let e := path.walk.getVert (geometry.b d.radical-2)
  let := finite_stabilizer d.radical a
  let : Finite (V d.radical a) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) a path.start_color).trans
      (fun _ hx => hx.1))) (inclusion_injective _)
  by_cases hi : (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F^2
  · let p : CriticalSegment geometry := ⟨a,z,path⟩
    obtain ⟨p',hl⟩ := exists_backward_link (by omega)
      (pairedRadiusChoice geometry (Nat.card F)) p
      (h.replacement_paired_radius_step d p hb)
    obtain ⟨x,hx,hatx,hvtx,_,_,_,_,_,_,hlarge⟩ :=
      h.replacement_paired_small_radius_penultimate_kernel_and_image d p p' hb hl hi
    obtain ⟨t,_,hat,hvt,hfirst⟩ := hl.choice
    have hat₀ : Adjacent d.radical a (p'.path.walk.getVert 1) := by rwa [hfirst]
    have hvt₀ : Adjacent d.radical p'.first (p'.path.walk.getVert 1) := by rwa [hfirst]
    have hYV : Z d.radical p'.first ⊔ Z d.radical (act d.radical x p'.first) ≤
        V d.radical a := sup_le
      (le_sup_left.trans (neighbor_seed_join_le_radius hat₀ hvt₀))
      (le_sup_left.trans (neighbor_seed_join_le_radius hatx hvtx))
    have hlast : p'.last=e := by simpa only [p] using hl.last_eq
    have he : Nat.card F < (Q d.radical e).relIndex (V d.radical a) := by
      rw [hlast] at hlarge
      exact hlarge.trans_le (relIndex_le_of_le_right hYV index_ne_zero_of_finite)
    have hZaE : Z d.radical a ≤ Q d.radical e := by
      apply Z_le_Q_of_dist_lt _ a (geometry.exists_critical a path.start_color)
      rw [geometry.distance_constant a path.start_color,
        path.dist_start (by rw [path.length_eq_b]; omega)]
      change geometry.b d.radical-2 < geometry.b d.radical
      omega
    let : Finite (V d.radical a ⊓ Q d.radical e : Subgroup (FreeAmalgam d.radical)) :=
      Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
    have hq : Nat.card F ≤ (Q d.radical z).relIndex (V d.radical a ⊓ Q d.radical e) := by
      rw [←(h.replacement_small_radius_critical_indices d path hb hi).1]
      exact relIndex_le_of_le_right (le_inf (Z_le_VBall d.radical a 2) hZaE)
        index_ne_zero_of_finite
    have hm := relIndex_inf_mul_relIndex (Q d.radical z) (Q d.radical e) (V d.radical a)
    rw [inf_comm (Q d.radical e) (V d.radical a)] at hm
    change Nat.card F^2 < (Q d.radical z ⊓ Q d.radical e).relIndex (V d.radical a)
    rw [←hm]
    have hpos : 0 < Nat.card F := Nat.card_pos
    nlinarith
  · exact (Nat.lt_of_not_ge hi).trans_le
      (relIndex_le_of_le_left (show Q d.radical z ⊓ Q d.radical e ≤ Q d.radical z from
        inf_le_left) index_ne_zero_of_finite)

/-- The reversed literal critical path gives the source numerical
alternative, retaining the entire radius and its full second-vertex kernel. -/
theorem Input.replacement_critical_radius_index_split
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical) :
    Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (V d.radical z) ∨
      Nat.card F < (Q d.radical a).relIndex
        (V d.radical z ⊓ Q d.radical (path.walk.getVert 2)) := by
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        a path.start_color (by
          rw [geometry.distance_constant a path.start_color]
          exact (by omega : 0 < geometry.b d.radical))
        z path.end_color path.critical }
  have hg := h.replacement_two_kernel_radius_index_gt_square d rev hb
  change Nat.card F^2 < (Q d.radical a ⊓
    Q d.radical (path.walk.reverse.getVert (geometry.b d.radical-2))).relIndex
      (V d.radical z) at hg
  rw [SimpleGraph.Walk.getVert_reverse,path.length_eq_b,
    show geometry.b d.radical-(geometry.b d.radical-2)=2 by omega] at hg
  have hm := relIndex_inf_mul_relIndex (Q d.radical a)
    (Q d.radical (path.walk.getVert 2)) (V d.radical z)
  rw [inf_comm (Q d.radical (path.walk.getVert 2)) (V d.radical z)] at hm
  by_contra! hn
  have hu := Nat.mul_le_mul hn.2 hn.1
  rw [hm] at hu
  exact (not_lt_of_ge (by simpa only [pow_two] using hu)) hg

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
