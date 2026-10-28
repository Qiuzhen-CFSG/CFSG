module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralBalance
public import Theory.GroupAction.CubicTree.TrackArcs

/-!
# Central vertex stabilizers and symmetric fixed intervals

The two adjacent edge stabilizers generate their common vertex stabilizer.
Thus an involution central in both edges is central at the vertex. Short-arc
transitivity then equates fixation at opposite points of equal distance.
A fixed interval shorter than the singularity length is consequently symmetric
about any such central vertex it contains.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.5), p.397.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.centralizes_vertex_of_two_centralEdges (h : CubicTreeAction F)
    {s : ℕ} (hs : 2 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) (c : ℤ) {z : G}
    (hl : t.CentralEdge z (c - 1)) (hr : t.CentralEdge z c) :
    ∀ g ∈ RankTwo.stabilizer F (t.vertex c), Commute z g := by
  have h01 : (RankTwo.graph F).Adj (t.vertex (c-1)) (t.vertex c) := by
    simpa only [sub_add_cancel] using t.adjacent (c-1)
  let p : BasedWalk (RankTwo.graph F) 2 (t.vertex (c-1)) :=
    ⟨⟨t.vertex c, h01⟩, ⟨⟨t.vertex (c+1), t.adjacent c⟩, PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := by
    refine ⟨?_, trivial⟩
    intro he
    have hi := t.injective he
    omega
  have hgen := h.arc_stabilizers_generate_overlap hshort hs p hp
    (i := 1) (j := 1) le_rfl (by decide)
  let C := centralizer ({z} : Set G)
  have hleft : arcIntervalStabilizer p.toWalk 0 1 ≤ C := by
    intro a ha w hw
    obtain rfl := Set.mem_singleton_iff.mp hw
    apply hl.2 a
    refine ⟨ha 0 (by decide) (by decide), ?_⟩
    change a • t.vertex (c-1+1) = t.vertex (c-1+1)
    simpa only [sub_add_cancel] using
      (show a • t.vertex c = t.vertex c from ha 1 (by decide) (by decide))
  have hright : arcIntervalStabilizer p.toWalk 1 2 ≤ C := by
    intro a ha w hw
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact hr.2 a ⟨ha 1 (by decide) (by decide), ha 2 (by decide) (by decide)⟩
  intro g hg
  have hgin : g ∈ arcIntervalStabilizer p.toWalk 1 1 := by
    intro k hk hk'
    have he : k = 1 := by omega
    subst k
    exact hg
  rw [← hgen] at hgin
  exact (sup_le hleft hright hgin) z (Set.mem_singleton z)

theorem CubicTreeAction.central_vertex_fixes_opposite (h : CubicTreeAction F)
    {s : ℕ}
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) (c : ℤ) {z : G}
    (hc : ∀ g ∈ RankTwo.stabilizer F (t.vertex c), Commute z g)
    (n : ℕ) (hn : n ≤ s) :
    z • t.vertex (c + n) = t.vertex (c + n) ↔
      z • t.vertex (c - n) = t.vertex (c - n) := by
  let p := t.arc c n
  let q := t.reverse.arc (-c) n
  obtain ⟨g, hg⟩ := h.congruent_arcs s hshort hn p q
    (t.arc_nonbacktracking _ _) (t.reverse.arc_nonbacktracking _ _)
    (by simp only [Track.reverse, neg_neg])
  have hgfix : g • t.vertex c = t.vertex c := Option.some.inj (by
    have hh := congrArg List.head? hg
    simpa only [p, q, List.head?_map, BasedWalk.head_vertices, Option.map_some,
      Track.reverse, neg_neg] using hh)
  have hgend : g • t.vertex (c+n) = t.vertex (c-n) := by
    have hh := endpoint_smul_of_vertices trackGraphAction g p q hg
    simpa only [p, q, Track.arc_endpoint, Track.reverse, neg_add_rev, neg_neg,
      sub_eq_add_neg, add_comm] using hh
  have hcomm := hc g hgfix
  constructor
  · intro hz
    rw [← hgend, ← mul_smul, hcomm.eq, mul_smul, hz]
  · intro hz
    apply (MulAction.toPerm g).injective
    change g • (z • t.vertex (c+n)) = g • t.vertex (c+n)
    rw [← mul_smul, hcomm.symm.eq, mul_smul, hgend, hz]

theorem CubicTreeAction.centralInterval_symmetric_of_centralVertex (h : CubicTreeAction F)
    {s : ℕ}
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z : G} (d : t.CentralInterval z) (c : ℤ)
    (hlen : (d.fixedRight - d.fixedLeft).toNat < s)
    (hc : d.fixedLeft ≤ c ∧ c ≤ d.fixedRight)
    (hcentral : ∀ g ∈ RankTwo.stabilizer F (t.vertex c), Commute z g) :
    d.fixedLeft + d.fixedRight = 2*c := by
  by_contra hne
  have hnonneg : 0 ≤ d.fixedRight-d.fixedLeft := by omega
  rcases lt_or_gt_of_ne hne with hh | hh
  · let n := (d.fixedRight-c+1).toNat
    have hncast : (n : ℤ) = d.fixedRight-c+1 := by dsimp [n]; omega
    have hn : n ≤ s := by omega
    have hf := (h.central_vertex_fixes_opposite hshort t c hcentral n hn).2
      ((d.fixed_iff _).2 ⟨by omega, by omega⟩)
    have hi := (d.fixed_iff _).1 hf
    omega
  · let n := (c-d.fixedLeft+1).toNat
    have hncast : (n : ℤ) = c-d.fixedLeft+1 := by dsimp [n]; omega
    have hn : n ≤ s := by omega
    have hf := (h.central_vertex_fixes_opposite hshort t c hcentral n hn).1
      ((d.fixed_iff _).2 ⟨by omega, by omega⟩)
    have hi := (d.fixed_iff _).1 hf
    omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
