module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.Paths

/-!
# The original (5.7)/(5.9) consumer for repeated selected critical paths

The strict inequality in (5.9) is applied at the literal vertex two steps
along each current critical path. The (5.7) selection uses that same index,
that same path, and the original endpoint truncated by two edges. The output
retains every source choice and gives the exact fourth-shift centralization
used in the opening of (5.10). Both earlier source statements remain explicit
with their independent producers; no conclusion of (5.10) or (5.11) is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), pp.919--924.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

/-- The literal moving index in source (5.9). -/
def nextMovingIndex (p : CriticalSegment geometry) : ℕ :=
  (B R p.first (geometry.Z_normal p.first)).relIndex
    (U R (p.path.walk.getVert 2))

/-- Source (5.7), fed its actual (5.9) strict index, supplies all the chosen
critical paths and the fourth-shift commutation on page922. -/
theorem source57_source59_chosen_paths
    (hb : 4 < geometry.b R)
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (source57 : ∀ p : CriticalSegment geometry, 4 < nextMovingIndex p →
      ∃ d t, Chosen p d t ∧ Adjacent R p.first t ∧ Adjacent R d t ∧
        ¬Z R d ≤ Q R (p.path.walk.getVert (geometry.b R - 2)))
    (source59 : ∀ p : CriticalSegment geometry, 4 < nextMovingIndex p)
    (p : CriticalSegment geometry) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ n, BackwardLink geometry Chosen (s n) (s (n+1))) ∧
      (∀ n k i, i + 2*k ≤ geometry.b R →
        (s (n+k)).path.walk.getVert (i+2*k) = (s n).path.walk.getVert i) ∧
      ⁅Z R (s 2).first,Z R (s 2).last⁆ ≤
        centralizer ((Z R (s 0).last ⊔ Z R (s 1).last :
          Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  obtain ⟨s,hs0,hs,hover⟩ := exists_chosen_sequence (by omega) Chosen
    (fun q => source57 q (source59 q)) p
  refine ⟨s,hs0,hs,hover,?_⟩
  apply le_centralizer_iff.mp
  apply sup_le
  · exact le_centralizer_iff.mp
      (shifted_commutator_centralizes_endpoint Chosen s hs 0 2 (by omega))
  · exact le_centralizer_iff.mp
      (shifted_commutator_centralizes_endpoint Chosen s hs 1 1 (by omega))

variable [Finite M]

/-- Reverse the actual critical path using only the source edge-centralizer
hypothesis, without importing the binary natural-module recognition record. -/
def CriticalSegment.reverse (p : CriticalSegment geometry)
    (hC : EdgeCentralizerCondition R) (hb : 0 < geometry.b R) :
    CriticalSegment geometry where
  first := p.last
  last := p.first
  path := {
    start_color := p.path.end_color
    walk := p.path.walk.reverse
    shortest := by
      rw [SimpleGraph.Walk.length_reverse, p.path.shortest, SimpleGraph.dist_comm]
    critical := critical_reverse R geometry hC p.first p.path.start_color
      (by rw [geometry.distance_constant _ p.path.start_color]; exact hb) p.last p.path.end_color p.path.critical }

/-- A source-selected backward step at the reversed pair gives the required
forward endpoint, retaining the same selected seed and every overlap vertex. -/
theorem source57_source59_forward_path
    (hb : 4 < geometry.b R) (hC : EdgeCentralizerCondition R)
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (source57 : ∀ p : CriticalSegment geometry, 4 < nextMovingIndex p →
      ∃ d t, Chosen p d t ∧ Adjacent R p.first t ∧ Adjacent R d t ∧
        ¬Z R d ≤ Q R (p.path.walk.getVert (geometry.b R - 2)))
    (source59 : ∀ p : CriticalSegment geometry, 4 < nextMovingIndex p)
    (p : CriticalSegment geometry) :
    ∃ q : CriticalSegment geometry,
      q.first = p.path.walk.getVert 2 ∧
      (∃ t, Chosen (p.reverse hC (by omega)) q.last t ∧
        Adjacent R p.last t ∧ Adjacent R q.last t) ∧
      ∀ i, i + 2 ≤ geometry.b R →
        q.path.walk.getVert i = p.path.walk.getVert (i+2) := by
  let pr := p.reverse hC (show 0 < geometry.b R by omega)
  obtain ⟨q,hq⟩ := exists_backward_link (by omega) Chosen pr (source57 pr (source59 pr))
  refine ⟨q.reverse hC (by omega), ?_, ?_, ?_⟩
  · change q.last = p.path.walk.getVert 2
    rw [hq.last_eq]
    change p.path.walk.reverse.getVert (geometry.b R - 2) = _
    rw [SimpleGraph.Walk.getVert_reverse, p.path.length_eq_b]
    congr 1
    omega
  · obtain ⟨t,hchosen,hadj,hqadj,_⟩ := hq.choice
    exact ⟨t,hchosen,hadj,hqadj⟩
  · intro i hi
    change q.path.walk.reverse.getVert i = p.path.walk.getVert (i+2)
    rw [SimpleGraph.Walk.getVert_reverse, q.path.length_eq_b]
    have ho := hq.overlap (geometry.b R-i-2) (by omega)
    have hidx : geometry.b R-i-2+2 = geometry.b R-i := by omega
    rw [hidx] at ho
    rw [ho]
    change p.path.walk.reverse.getVert (geometry.b R-i-2) = _
    rw [SimpleGraph.Walk.getVert_reverse, p.path.length_eq_b]
    congr 1
    omega

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
