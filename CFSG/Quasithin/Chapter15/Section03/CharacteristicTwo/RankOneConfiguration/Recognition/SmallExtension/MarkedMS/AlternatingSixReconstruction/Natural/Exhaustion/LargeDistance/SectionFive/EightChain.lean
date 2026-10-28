module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightGenerating
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalPath
/-!
# Generating terminal paths in the image-eight branch

Iterate the proved backward selection to construct every required two-step
orbit relation on one critical path. Three further generating shifts give the
literal R4 and R6 commutator lines: both have order two, are moved by their
respective first-edge kernels, and are centralized by the same endpoint radius.
These calculations preserve all shared walk vertices on the natural graph.

The orbit-complete consumer also identifies the normalizer of the whole
critical kernel inside its actual edge core with the edge mover. Its shifted
forward slice is strict. No critical-image, mover-model or path-selection
premise is supplied by the caller. Both covers and all central attachments
remain; the terminal mover comparison and large-distance contradiction remain
separate mathematical obligations.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.10)(i)--(iii), printed pp.922--923, and the terminal path in (5.11),
pp.923--924. The orbit and graph definitions are the existing natural
replacement definitions, without an identification with the exceptional graph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

namespace EightChain
open SylowTerminalPath
include e hz hn in
/-- An arbitrary finite number of generating shifts constructs the source
orbit relations. The original path may have no initial orbit relations. -/
theorem exists_orbitPrefix_chain_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') (n : ℕ) :
    ∃ c c', ∃ v : CriticalPath d.radical (replacementGeometry h d) c c',
      ShiftChain (h := h) p v n ∧ OrbitPrefix (h := h) v n := by
  induction n with
  | zero => exact ⟨a,a',p,ShiftChain.nil,by intro i hi; omega⟩
  | succ n ih =>
    obtain ⟨c,c',v,hv,ho⟩ := ih
    obtain ⟨q,_⟩ := EightGenerating.backwardShift_with_edge_knownSimple
      (e := e) (hz := hz) (hn := hn) hb v
    exact ⟨_,_,q.path,ShiftChain.step hv q,orbitPrefix_backwardShift hb v q ho⟩

include e hz hn in
/-- Three successive generating shifts realize the source R4/R6 configuration.
Both critical images are two, both lines are moved by their first edge kernels,
and the same endpoint radius centralizes both lines. -/
theorem three_backward_shifts_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
      (t : BackwardShift (h := h) r.path),
      act d.radical q.transporter (p.walk.getVert 1) = q.edge ∧
      act d.radical r.transporter (q.path.walk.getVert 1) = r.edge ∧
      act d.radical t.transporter (r.path.walk.getVert 1) = t.edge ∧
      q.path.walk.getVert (q.path.walk.length-2) = p.walk.getVert (p.walk.length-4) ∧
      r.path.walk.getVert (r.path.walk.length-2) = p.walk.getVert (p.walk.length-6) ∧
      let z₄ := p.walk.getVert (p.walk.length-4)
      let z₆ := p.walk.getVert (p.walk.length-6)
      let H₄ := ⁅Z d.radical r.start,Z d.radical z₄⁆
      let H₆ := ⁅Z d.radical t.start,Z d.radical z₆⁆
      (Q d.radical z₄).relIndex (Z d.radical r.start) = 2 ∧
      (Q d.radical z₆).relIndex (Z d.radical t.start) = 2 ∧
      Nat.card H₄ = 2 ∧ Nat.card H₆ = 2 ∧
      (¬ H₄ ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) ∧
      (¬ H₆ ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical))) ∧
      (¬ Q d.radical r.edge ≤ centralizer (H₄ : Set (FreeAmalgam d.radical))) ∧
      (¬ Q d.radical t.edge ≤ centralizer (H₆ : Set (FreeAmalgam d.radical))) ∧
      H₄ ⊔ H₆ ≤ centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical)) := by
  obtain ⟨q,hqe⟩ := EightGenerating.backwardShift_with_edge_knownSimple (e := e) (hz := hz) (hn := hn) hb p
  obtain ⟨r,hre⟩ := EightGenerating.backwardShift_with_edge_knownSimple (e := e) (hz := hz) (hn := hn) hb q.path
  obtain ⟨t,hte⟩ := EightGenerating.backwardShift_with_edge_knownSimple (e := e) (hz := hz) (hn := hn) hb r.path
  have hfour := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have hsix := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path r t
  have hp : p.walk.length = replacementDistance h d := p.length_eq_b
  have hq : q.path.walk.length = replacementDistance h d := q.path.length_eq_b
  have hr : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
  have h6 : 6 ≤ replacementDistance h d := by
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he
    omega
  have he4 : q.path.walk.getVert (q.path.walk.length-2) = p.walk.getVert (p.walk.length-4) := by
    rw [show q.path.walk.length-2 = (p.walk.length-4)+2 by omega]
    exact q.overlap _ (by omega)
  have he6 : r.path.walk.getVert (r.path.walk.length-2) = p.walk.getVert (p.walk.length-6) := by
    rw [show r.path.walk.length-2 = (q.path.walk.length-4)+2 by omega,r.overlap _ (by omega)]
    rw [show q.path.walk.length-4 = (p.walk.length-6)+2 by omega]
    exact q.overlap _ (by omega)
  have hVQ : V d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤
      Q d.radical (q.path.walk.getVert (q.path.walk.length-2)) :=
    V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color (by change 2 < replacementDistance h d; omega)
  have hVQ₆ : V d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤
      Q d.radical (r.path.walk.getVert (r.path.walk.length-2)) := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) r.path.end_color
    rw [SimpleGraph.dist_comm,r.path.dist_end]
    change r.path.walk.length-(r.path.walk.length-2)+2 < replacementDistance h d
    omega
  have hcentral : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ⊔
      ⁅Z d.radical t.start,Z d.radical (r.path.walk.getVert (r.path.walk.length-2))⁆ ≤
      centralizer (V d.radical (q.path.walk.getVert (q.path.walk.length-2)) : Set (FreeAmalgam d.radical)) := by
    apply sup_le
    · exact (((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
        (DistanceEight.U_le_Z d.radical _)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical _ r.path.end_color)).trans (centralizer_le hVQ))
    · exact (((critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_right).trans
        (DistanceEight.U_le_Z d.radical _)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical _ t.path.end_color)).trans (centralizer_le hVQ₆))
  dsimp only at hfour hsix ⊢
  rw [r.first,he4] at hfour
  rw [t.first,he6] at hsix
  simp only [he4,he6] at hcentral
  exact ⟨q,r,t,hqe,hre,hte,he4,he6,hfour.2.1,hsix.2.1,
    hfour.2.2.2.1,hsix.2.2.2.1,hfour.1,hsix.1,hfour.2.2.2.2,hsix.2.2.2.2,hcentral⟩

include e hz hn in
/-- A source orbit-complete path with its actual generating backward shift.
The full critical kernel's normalizer inside the edge core is precisely the
edge mover, and the second shifted forward slice is strict. -/
theorem orbit_complete_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ c c', ∃ v : CriticalPath d.radical (replacementGeometry h d) c c',
      ShiftChain (h := h) p v (replacementDistance h d) ∧
      OrbitPrefix (h := h) v (replacementDistance h d) ∧
      ∃ q : BackwardShift (h := h) v, ∃ r : BackwardShift (h := h) q.path,
        act d.radical q.transporter (v.walk.getVert 1) = q.edge ∧
        act d.radical r.transporter (q.path.walk.getVert 1) = r.edge ∧
        let z := q.path.walk.getVert (q.path.walk.length-2)
        let T := Q d.radical (r.path.walk.getVert 1)
        let K := Z d.radical r.start ⊓ Q d.radical z
        let J := SmallMover.join (U d.radical r.start) (Q d.radical r.start) T 4
        (Q d.radical z).relIndex (Z d.radical r.start) = 2 ∧
        Nat.card (⁅Z d.radical r.start,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
        T ⊓ normalizer (K : Set (FreeAmalgam d.radical)) = J ∧
        2 < (B d.radical r.start ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical q.start) := by
  obtain ⟨c,c',v,hv,ho⟩ := exists_orbitPrefix_chain_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p (replacementDistance h d)
  obtain ⟨q,hq⟩ := EightGenerating.backwardShift_with_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hb v
  obtain ⟨r,hr⟩ := EightGenerating.backwardShift_with_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path
  have hh := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb v q r
  have hs : (Q d.radical (q.path.walk.getVert (q.path.walk.length-2))).relIndex
      (Z d.radical r.start) < 4 := by rw [hh.2.1]; decide
  have hker := EightSmallMovers.critical_kernel_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r.path hs
  have hstrict := EightBaumann.small_forward_slice_strict_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r.path hs
  have hr2 : r.path.walk.getVert 2 = q.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
  rw [hr2] at hstrict
  exact ⟨c,c',v,hv,ho,q,r,hq,hr,hh.2.1,hh.2.2.2.1,hker.2.2 hh.2.2.2.2,hstrict⟩

end EightChain
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
