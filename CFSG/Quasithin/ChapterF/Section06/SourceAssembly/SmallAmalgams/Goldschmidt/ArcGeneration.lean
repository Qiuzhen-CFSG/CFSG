module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcIndices
public import Theory.GroupAction.CubicTree.ArcGeneration
public import Theory.GroupAction.CubicTree.ArcIntervals
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth

/-!
# Goldschmidt's generation by overlapping arc stabilizers

Every interval subgroup is the literal pointwise fixer of a subarc in the
original coset tree. Short-arc regularity supplies the actual prime extension
indices. The backwards subgroup induction then identifies the join of prefix
and suffix stabilizers with the stabilizer of their overlap.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.13), p.384.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The fixer of the vertices at positions `j` through `i` of the actual walk. -/
abbrev arcIntervalStabilizer {x y : RankTwo.Vertex F}
    (p : (RankTwo.graph F).Walk x y) (j i : ℕ) : Subgroup G :=
  intervalFixer (fun k => RankTwo.stabilizer F (p.getVert k)) j i

theorem pathStabilizer_segment {x y : RankTwo.Vertex F}
    (p : (RankTwo.graph F).Walk x y) (j i : ℕ) (hji : j ≤ i) (hi : i ≤ p.length) :
    RankTwo.pathStabilizer F (segment p j i hji hi) = arcIntervalStabilizer p j i := by
  ext a
  change (∀ z ∈ (segment p j i hji hi).vertices, a • z = z) ↔
    ∀ k, j ≤ k → k ≤ i → a • p.getVert k = p.getVert k
  constructor
  · intro ha k hjk hki
    exact ha _ ((mem_vertices_segment p j i hji hi).2 ⟨k, hjk, hki, rfl⟩)
  · intro ha z hz
    obtain ⟨k, hjk, hki, rfl⟩ := (mem_vertices_segment p j i hji hi).1 hz
    exact ha k hjk hki

theorem pathStabilizer_segment_snoc {x y : RankTwo.Vertex F}
    (p : (RankTwo.graph F).Walk x y) (hp : p.IsPath)
    (j i : ℕ) (hji : j ≤ i) (hi : i < p.length) :
    RankTwo.pathStabilizer F ((segment p j i hji hi.le).snoc
      (forward_adj _ (segment_next_forward p hp j i hji hi))) =
        arcIntervalStabilizer p j (i + 1) := by
  rw [pathStabilizer_snoc, pathStabilizer_segment]
  ext a
  change ((∀ k, j ≤ k → k ≤ i → a • p.getVert k = p.getVert k) ∧
    a • p.getVert (i + 1) = p.getVert (i + 1)) ↔
    ∀ k, j ≤ k → k ≤ i + 1 → a • p.getVert k = p.getVert k
  constructor
  · rintro ⟨ha, hb⟩ k hjk hki
    by_cases hk : k = i + 1
    · simpa only [hk] using hb
    · exact ha k hjk (by omega)
  · intro ha
    exact ⟨fun k hjk hki => ha k hjk (by omega), ha (i + 1) (by omega) le_rfl⟩

private theorem CubicTreeAction.extension_relIndex_prime (h : CubicTreeAction F)
    {n : ℕ} {v z : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) n v)
    (hp : RightRegular (A := G) p) (hz : Theory.GroupAction.CubicTree.Forward p z) :
    ((RankTwo.pathStabilizer F (p.snoc (forward_adj p hz))).relIndex
      (RankTwo.pathStabilizer F p)).Prime := by
  rw [pathStabilizer_snoc_relIndex p hp hz]
  cases n with
  | zero =>
    change (Nat.card ((RankTwo.graph F).neighborSet v)).Prime
    rw [h.card_neighbor]
    decide
  | succ n =>
    change (Nat.card {z : RankTwo.Vertex F // Theory.GroupAction.CubicTree.Forward p z}).Prime
    rw [card_forward_of_cubic p (h.card_neighbor p.endpoint)]
    decide

/-- Every one-step subarc inclusion is maximal for a short source arc. -/
theorem CubicTreeAction.arcInterval_relIndex_prime (h : CubicTreeAction F) {s n : ℕ}
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hn : n ≤ s) {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) n v)
    (hp : p.Nonbacktracking) (j i : ℕ) (hji : j ≤ i) (hi : i < n) :
    ((arcIntervalStabilizer p.toWalk j (i + 1)).relIndex
      (arcIntervalStabilizer p.toWalk j i)).Prime := by
  have hpath : p.toWalk.IsPath := isPath_of_nonbacktracking_of_cycle_bound
    (N := n) (fun _ c hc => (h.tree.isAcyclic c hc).elim) p hp le_rfl
  have hi' : i < p.toWalk.length := by simpa only [BasedWalk.length_toWalk] using hi
  let q := segment p.toWalk j i hji hi'.le
  have hq : q.Nonbacktracking := segment_nonbacktracking p.toWalk hpath j i hji hi'.le
  have hreg : RightRegular (A := G) q := hshort (i - j) _ q (by omega) hq
  have hforward := segment_next_forward p.toWalk hpath j i hji hi'
  have hindex := h.extension_relIndex_prime q hreg hforward
  dsimp only [q] at hindex
  rw [pathStabilizer_segment_snoc p.toWalk hpath j i hji hi',
    pathStabilizer_segment] at hindex
  exact hindex

/-- The first conclusion of (2.13), for the actual pointwise interval fixers. -/
theorem CubicTreeAction.arc_stabilizers_generate_overlap (h : CubicTreeAction F)
    {s n : ℕ}
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hn : n ≤ s) {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) n v)
    (hp : p.Nonbacktracking) {i j : ℕ} (hji : j ≤ i) (hi : i ≤ n) :
    arcIntervalStabilizer p.toWalk 0 i ⊔ arcIntervalStabilizer p.toWalk j n =
      arcIntervalStabilizer p.toWalk j i :=
  prefix_sup_suffix_eq_interval _ n
    (fun j i hji hi => h.arcInterval_relIndex_prime hshort hn p hp j i hji hi) hji hi

theorem CubicTreeAction.adjacent_stabilizers_generate (h : CubicTreeAction F)
    {v w : RankTwo.Vertex F} (hvw : (RankTwo.graph F).Adj v w) :
    RankTwo.stabilizer F v ⊔ RankTwo.stabilizer F w = ⊤ := by
  obtain ⟨g, hv, hw⟩ := RankTwo.incident_common_translate F hvw.2
  have hbase (i : Bool) : RankTwo.stabilizer F (RankTwo.base F i) = F i :=
    stabilizer_base F i
  rw [← hv, ← hw, RankTwo.stabilizer_translate, RankTwo.stabilizer_translate,
    hbase, hbase, ← Subgroup.map_sup]
  have he : F v.type ⊔ F w.type = ⊤ := by
    have ht := hvw.1
    cases hi : v.type <;> cases hj : w.type
    · exact (ht (hi.trans hj.symm)).elim
    · exact h.generated
    · exact sup_comm (F true) (F false) |>.trans h.generated
    · exact (ht (hi.trans hj.symm)).elim
  rw [he]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

/-- Separated prefix and suffix fixers generate the whole original acting
group. Type preservation removes the possible edge inversion in source (2.13). -/
theorem CubicTreeAction.arc_stabilizers_generate_separated (h : CubicTreeAction F)
    {s n : ℕ}
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hn : n ≤ s) {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) n v)
    (hp : p.Nonbacktracking) {i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    arcIntervalStabilizer p.toWalk 0 i ⊔ arcIntervalStabilizer p.toWalk j n = ⊤ := by
  apply prefix_sup_suffix_eq_top _ n
    (fun j i hji hi => h.arcInterval_relIndex_prime hshort hn p hp j i hji hi)
    ?_ hij hj
  intro k hk
  exact h.adjacent_stabilizers_generate
    (p.toWalk.adj_getVert_succ (by simpa only [BasedWalk.length_toWalk] using hk))

/-- The literal second conclusion of (2.13) follows from the stronger generated
subgroup equality available for the two-orbit source action. -/
theorem CubicTreeAction.arc_stabilizers_index_le_two (h : CubicTreeAction F)
    {s n : ℕ}
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hn : n ≤ s) {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) n v)
    (hp : p.Nonbacktracking) {i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    (arcIntervalStabilizer p.toWalk 0 i ⊔ arcIntervalStabilizer p.toWalk j n).index ≤ 2 := by
  rw [h.arc_stabilizers_generate_separated hshort hn p hp hij hj, Subgroup.index_top]
  decide

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
