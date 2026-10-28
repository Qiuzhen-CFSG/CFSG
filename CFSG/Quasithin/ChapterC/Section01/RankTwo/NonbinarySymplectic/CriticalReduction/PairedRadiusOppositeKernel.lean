module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusFixedActor

/-!
# The full critical actor lies in the actual selected opposite kernel

The paired small-radius argument fixes X_z intersect Q_a on the whole
selected backward seed Z_v. The literal common edge places Q_a inside
G_v. Thus the exact seed centralizer C_v=Q_v places the whole actor in
Q_v, retaining every central omega attachment.

This is a consequence of the original small radius budget and actual
paired backward selection, without assuming either seed lies in Q_e.
The remaining source (5.11) comparison concerns the action of Z_v at e;
the opposite containment proved here does not identify those kernels.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full X_z intersection, not just its moving quotient, lies in the
kernel at the actual paired backward starting vertex. -/
theorem Input.replacement_paired_small_radius_actor_le_selected_core
    {geometry : Geometry d.radical} (p p' : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hl : BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F)) p p')
    (hi : (Q d.radical p.last).relIndex (V d.radical p.first) ≤ Nat.card F^2) :
    X d.radical p.last ⊓ Q d.radical p.first ≤ Q d.radical p'.first := by
  obtain ⟨x,_,_,_,_,_,_,_,hfixed⟩ :=
    h.replacement_paired_small_radius_fixed_actor d p p' hb hl hi
  obtain ⟨t,_,hat,hvt,_⟩ := hl.choice
  have hAS : X d.radical p.last ⊓ Q d.radical p.first ≤ stabilizer d.radical p'.first :=
    inf_le_right.trans (Q_le_stabilizer_of_dist_le_two p.first p'.first
      p.path.start_color p'.path.start_color
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hat hvt))
  have hcent : X d.radical p.last ⊓ Q d.radical p.first ≤
      centralizer (Z d.radical p'.first : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hfixed)).trans
      (centralizer_le (show Z d.radical p'.first ≤
        Z d.radical p'.first ⊔ Z d.radical (act d.radical x p'.first) from le_sup_left))
  have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
    p'.first p'.path.start_color
  rw [←hC]
  exact le_inf hAS hcent

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
