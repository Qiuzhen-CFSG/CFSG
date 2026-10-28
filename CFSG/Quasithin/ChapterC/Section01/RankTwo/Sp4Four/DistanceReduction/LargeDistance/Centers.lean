module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.Paths

/-!
# Full vertex centers in the large-distance propagation

The propagated subgroup centralizes three stabilizers. Its containment in
those stabilizers also follows from the actual critical commutator and the
exact distances on the chosen paths. Thus the source intersection lies in
the full ambient images of all three vertex centers, not merely in their
centralizers. No central attachment is discarded.

Source: MS93 (5.10), printed p.922, first displayed central-intersection chain.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

/-- The paired critical commutator also lies in its starting seed. -/
theorem critical_commutator_le_start (p : CriticalSegment geometry)
    (hb : 0 < geometry.b R) :
    ⁅Z R p.first,Z R p.last⁆ ≤ Z R p.first := by
  rw [commutator_comm]
  exact le_normalizer_iff_commutator_le_right.mp
    ((p.path.endpoint_Z_le_start_stabilizer hb).trans (Z_normalized R p.first))

/-- The same critical commutator belongs to every nearby earlier vertex
stabilizer along the chosen path sequence. -/
theorem shifted_commutator_le_stabilizer
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ n, BackwardLink geometry Chosen (s n) (s (n+1)))
    (n k : ℕ) (hk : 2*k < geometry.b R) :
    ⁅Z R (s (n+k)).first,Z R (s (n+k)).last⁆ ≤ stabilizer R (s n).first := by
  have hdist := shifted_start_distance Chosen s hs n k (Nat.le_of_lt hk)
  have hQ : Z R (s (n+k)).first ≤ Q R (s n).first := by
    apply Z_le_Q_of_dist_lt R _
      (geometry.exists_critical _ (s (n+k)).path.start_color)
    rw [geometry.distance_constant _ (s (n+k)).path.start_color, hdist]
    exact hk
  exact (critical_commutator_le_start (s (n+k)) (by omega)).trans
    (hQ.trans (fun _ hx => hx.1))

variable [Finite M]

/-- The complete source inclusion of R₄'s edge intersection in the three
literal full vertex centers follows from the marked source generations. -/
theorem fourth_shift_intersection_le_full_centers
    (hb : 4 < geometry.b R)
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ n, BackwardLink geometry Chosen (s n) (s (n+1)))
    {t v : Vertex R}
    (hct : Adjacent R (s 1).first t) (hcv : Adjacent R (s 1).first v)
    (ht : color R t = true)
    (hgenC : stabilizer R (s 1).first ≤ Q R t ⊔ Z R (s 1).last)
    (hgenD : stabilizer R (s 0).first ≤ Q R v ⊔ Z R (s 0).last)
    (x : FreeAmalgam R) (hx : x ∈ stabilizer R (s 1).first)
    (hxa : act R x (s 0).first = (s 2).first) :
    ⁅Z R (s 2).first,Z R (s 2).last⁆ ⊓ Z R t ≤
      (stabilizer R (s 1).first ⊓
        centralizer (stabilizer R (s 1).first : Set (FreeAmalgam R))) ⊓
      (stabilizer R (s 0).first ⊓
        centralizer (stabilizer R (s 0).first : Set (FreeAmalgam R))) ⊓
      (stabilizer R (s 2).first ⊓
        centralizer (stabilizer R (s 2).first : Set (FreeAmalgam R))) := by
  have hc := fourth_shift_intersection_le_centers hb Chosen s hs
    hct hcv ht hgenC hgenD x hx hxa
  have hg1 := shifted_commutator_le_stabilizer Chosen s hs 1 1 (by omega)
  have hg0 := shifted_commutator_le_stabilizer Chosen s hs 0 2 (by omega)
  have hg2 := shifted_commutator_le_stabilizer Chosen s hs 2 0 (by omega)
  exact le_inf (le_inf
    (le_inf (inf_le_left.trans hg1) (hc.trans (inf_le_left.trans inf_le_left)))
    (le_inf (inf_le_left.trans hg0) (hc.trans (inf_le_left.trans inf_le_right))))
    (le_inf (inf_le_left.trans hg2) (hc.trans inf_le_right))

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
