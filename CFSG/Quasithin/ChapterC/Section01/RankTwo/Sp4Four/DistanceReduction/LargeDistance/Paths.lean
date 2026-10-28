module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.CentralPropagation

/-!
# Repeated selected critical paths for the nonbinary symplectic argument

A backward step retains its source-selected seed and common edge, the actual
truncated endpoint, and every vertex of the overlapping geodesics. Iterating
these steps gives exact vertex and distance formulas, so the nearby endpoint
commutations and the page-922 central-intersection propagation follow on the
same paths. Every full central attachment is retained.

The selected-seed noncontainment is the earlier output of MS93 (5.7), whose
strict moving-index premise comes from (5.9). This file proves the iteration
and its geometric consumers; it does not assert either earlier source result,
the J-equality (5.10), or the critical-distance conclusion (5.11).

Source: Meierfrankenfeld--Stellmacher (1993), pp.922--924.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
variable {M : Type*} [Group M] {R : Subgroup M} (geometry : Geometry R)

/-- A genuine critical path with its endpoints retained as data. -/
structure CriticalSegment where
  first : Vertex R
  last : Vertex R
  path : CriticalPath R geometry first last

/-- A chosen backward shift retains the source selection, its common edge,
and all vertices of the overlapping geodesics. -/
structure BackwardLink (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (p q : CriticalSegment geometry) : Prop where
  choice : ∃ t, Chosen p q.first t ∧ Adjacent R p.first t ∧
    Adjacent R q.first t ∧ q.path.walk.getVert 1 = t
  last_eq : q.last = p.path.walk.getVert (geometry.b R - 2)
  overlap : ∀ i, i + 2 ≤ geometry.b R →
    q.path.walk.getVert (i + 2) = p.path.walk.getVert i

variable {geometry}

/-- The exact noncontainment supplied by source (5.7), with its (5.9)
strict-index antecedent discharged, constructs one chosen backward link. -/
theorem exists_backward_link (hb : 2 ≤ geometry.b R)
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (p : CriticalSegment geometry)
    (h : ∃ d t, Chosen p d t ∧ Adjacent R p.first t ∧ Adjacent R d t ∧
      ¬Z R d ≤ Q R (p.path.walk.getVert (geometry.b R - 2))) :
    ∃ q, BackwardLink geometry Chosen p q := by
  obtain ⟨d,t,hchosen,hat,hdt,hn⟩ := h
  have hn' : ¬Z R d ≤ Q R (p.path.walk.getVert (p.path.walk.length - 2)) := by
    simpa only [p.path.length_eq_b] using hn
  obtain ⟨q,hqt,hover⟩ := exists_backward_path_of_not_le geometry hb p.path hat hdt hn'
  refine ⟨⟨d,_,q⟩,⟨⟨t,hchosen,hat,hdt,hqt⟩,?_,?_⟩⟩
  · simp only [p.path.length_eq_b]
  · intro i hi
    exact hover i (by rw [p.path.length_eq_b]; omega)

/-- Iterating a source choice never changes any common path vertex. -/
theorem iterated_overlap
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ n, BackwardLink geometry Chosen (s n) (s (n+1)))
    (n k i : ℕ) (hi : i + 2*k ≤ geometry.b R) :
    (s (n+k)).path.walk.getVert (i + 2*k) = (s n).path.walk.getVert i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hi' : i + 2*k ≤ geometry.b R := by omega
    have hstep := (hs (n+k)).overlap (i+2*k) (by omega)
    have heq : n + (k+1) = n+k+1 := by omega
    have heq' : i + 2*(k+1) = (i+2*k)+2 := by omega
    rw [heq, heq', hstep]
    exact ih hi'

/-- The starts of successive chosen critical paths occur at their exact
positions on the later path. -/
theorem shifted_start_vertex
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ n, BackwardLink geometry Chosen (s n) (s (n+1)))
    (n k : ℕ) (hk : 2*k ≤ geometry.b R) :
    (s (n+k)).path.walk.getVert (2*k) = (s n).first := by
  simpa using iterated_overlap Chosen s hs n k 0 (by omega)

/-- The shifted endpoint is the literal truncated endpoint on the old path. -/
theorem shifted_last_vertex
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ n, BackwardLink geometry Chosen (s n) (s (n+1)))
    (n k : ℕ) (hk : 2*k ≤ geometry.b R) :
    (s (n+k)).last = (s n).path.walk.getVert (geometry.b R - 2*k) := by
  have h := iterated_overlap Chosen s hs n k (geometry.b R - 2*k) (by omega)
  have heq : geometry.b R - 2*k + 2*k = geometry.b R := by omega
  rw [heq, ←(s (n+k)).path.length_eq_b, SimpleGraph.Walk.getVert_length] at h
  simpa only [(s (n+k)).path.length_eq_b] using h

/-- All start-to-start distances of the overlapping critical paths are exact. -/
theorem shifted_start_distance
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ n, BackwardLink geometry Chosen (s n) (s (n+1)))
    (n k : ℕ) (hk : 2*k ≤ geometry.b R) :
    (cosetGraph R).dist (s (n+k)).first (s n).first = 2*k := by
  rw [←shifted_start_vertex Chosen s hs n k hk]
  exact (s (n+k)).path.dist_start (by rw [(s (n+k)).path.length_eq_b]; exact hk)

/-- All endpoint distances use the same original geodesic, not renamed paths. -/
theorem shifted_last_distance
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ n, BackwardLink geometry Chosen (s n) (s (n+1)))
    (n k : ℕ) (hk : 2*k ≤ geometry.b R) :
    (cosetGraph R).dist (s (n+k)).last (s n).last = 2*k := by
  rw [shifted_last_vertex Chosen s hs n k hk, (s n).path.dist_end,
    (s n).path.length_eq_b]
  omega

/-- The critical commutator belongs to the actual endpoint seed. -/
theorem critical_commutator_le_endpoint (p : CriticalSegment geometry) :
    ⁅Z R p.first,Z R p.last⁆ ≤ Z R p.last := by
  have hfirst : Z R p.first ≤ stabilizer R p.last :=
    Z_le_stabilizer_of_dist_le p.first
      (geometry.exists_critical p.first p.path.start_color)
      (by rw [p.path.critical.1])
  exact le_normalizer_iff_commutator_le_right.mp (hfirst.trans (Z_normalized R p.last))

/-- Source (5.10)'s shifted commutator centralizes the nearby original
endpoint seeds, retaining every central attachment. -/
theorem shifted_commutator_centralizes_endpoint
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ n, BackwardLink geometry Chosen (s n) (s (n+1)))
    (n k : ℕ) (hk : 2*k < geometry.b R) :
    ⁅Z R (s (n+k)).first,Z R (s (n+k)).last⁆ ≤
      centralizer (Z R (s n).last : Set (FreeAmalgam R)) := by
  have hdist := shifted_last_distance Chosen s hs n k (Nat.le_of_lt hk)
  have hQ : Z R (s (n+k)).last ≤ Q R (s n).last := by
    apply Z_le_Q_of_dist_lt R _
      (geometry.exists_critical _ (s (n+k)).path.end_color)
    rw [geometry.distance_constant _ (s (n+k)).path.end_color, hdist]
    exact hk
  exact (critical_commutator_le_endpoint (s (n+k))).trans
    (hQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes _ (s n).path.end_color))))

variable [Finite M]

/-- The actual page-922 central propagation for R₄ uses the overlapping
critical paths at shifts zero, two and four. All three full centers survive. -/
theorem fourth_shift_intersection_le_centers
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
      centralizer (stabilizer R (s 1).first : Set (FreeAmalgam R)) ⊓
      centralizer (stabilizer R (s 0).first : Set (FreeAmalgam R)) ⊓
      centralizer (stabilizer R (s 2).first : Set (FreeAmalgam R)) := by
  have h21 : (cosetGraph R).dist (s 2).last (s 1).last = 2 :=
    shifted_last_distance Chosen s hs 1 1 (by omega)
  have h20 : (cosetGraph R).dist (s 2).last (s 0).last = 4 :=
    shifted_last_distance Chosen s hs 0 2 (by omega)
  exact critical_intersection_le_three_centers geometry hb (s 2).path hct hcv ht
    (s 1).path.end_color (s 0).path.end_color (by omega) (by omega)
    hgenC hgenD x hx hxa

omit [Finite M] in
/-- A selected path has arbitrarily many compatible backward critical shifts.
The input is exactly the selected-seed noncontainment, not a distance bound. -/
theorem exists_chosen_sequence (hb : 2 ≤ geometry.b R)
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (hstep : ∀ p, ∃ d t, Chosen p d t ∧ Adjacent R p.first t ∧ Adjacent R d t ∧
      ¬Z R d ≤ Q R (p.path.walk.getVert (geometry.b R - 2)))
    (p : CriticalSegment geometry) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ n, BackwardLink geometry Chosen (s n) (s (n+1))) ∧
      ∀ n k i, i + 2*k ≤ geometry.b R →
        (s (n+k)).path.walk.getVert (i+2*k) = (s n).path.walk.getVert i := by
  let next (p : CriticalSegment geometry) :=
    Classical.choose (exists_backward_link hb Chosen p (hstep p))
  have hn (p : CriticalSegment geometry) : BackwardLink geometry Chosen p (next p) :=
    Classical.choose_spec (exists_backward_link hb Chosen p (hstep p))
  let s : ℕ → CriticalSegment geometry := Nat.rec p (fun _ q => next q)
  have hs (n : ℕ) : BackwardLink geometry Chosen (s n) (s (n+1)) := hn (s n)
  exact ⟨s,rfl,hs,fun n k i hi => iterated_overlap Chosen s hs n k i hi⟩

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
