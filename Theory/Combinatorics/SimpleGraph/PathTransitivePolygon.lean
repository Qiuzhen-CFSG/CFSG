module

public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.Walks
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Rooted path transitivity

Transitivity of a vertex stabilizer on nonbacktracking walks descends to shorter
lengths whenever every vertex has at least two neighbors. It also induces
transitivity on the corresponding metric sphere. These are the first reductions
in Aschbacher–Smith, Lemma F.3.5, printed pp. 270–272.

All actions here preserve the actual graph adjacency relation. Their metric
invariance is proved, and the path action is the vertex-by-vertex action on the
`BasedWalk` list. No uniqueness or geodesicity assertion is built into the
transitivity hypothesis.

The graph-wide polygon alternative needs particular care: a transitivity
hypothesis at a single vertex, even with type preservation and edge transitivity,
is insufficient for the claimed diameter. For example the affine-plane incidence
graph AG(2,3) is edge transitive and is transitive on nonbacktracking four-walks
from a point, but has diameter four, not three. This module therefore supplies
only the proved rooted reductions; it does not assert the full recognition result.
-/

@[expose] public section

namespace SimpleGraph.PathTransitivePolygon

universe u v
variable {V : Type u} {A : Type v} {G : SimpleGraph V}
variable [Group A] [MulAction A V]

/-- An action on vertices that preserves adjacency. Inverses give reflection. -/
structure GraphAction (G : SimpleGraph V) (A : Type v) [Group A] [MulAction A V] : Prop where
  map_adj : ∀ (a : A) {x y : V}, G.Adj x y → G.Adj (a • x) (a • y)

namespace GraphAction

/-- The graph homomorphism induced by an acting element. -/
def hom (h : GraphAction G A) (a : A) : G →g G where
  toFun := (a • ·)
  map_rel' := h.map_adj a

theorem adj_iff (h : GraphAction G A) (a : A) {x y : V} :
    G.Adj (a • x) (a • y) ↔ G.Adj x y := by
  refine ⟨fun hp => ?_, h.map_adj a⟩
  simpa only [inv_smul_smul] using h.map_adj a⁻¹ hp

private theorem edist_le (h : GraphAction G A) (a : A) (x y : V) :
    G.edist (a • x) (a • y) ≤ G.edist x y := by
  change G.edist (a • x) (a • y) ≤ ⨅ p : G.Walk x y, (p.length : ℕ∞)
  refine le_iInf fun p => ?_
  have hp : G.edist (a • x) (a • y) ≤ (p.map (h.hom a)).length :=
    (p.map (h.hom a)).edist_le
  simpa only [Walk.length_map] using hp

theorem edist_smul (h : GraphAction G A) (a : A) (x y : V) :
    G.edist (a • x) (a • y) = G.edist x y := by
  refine le_antisymm (h.edist_le a x y) ?_
  simpa only [inv_smul_smul] using h.edist_le a⁻¹ (a • x) (a • y)

theorem dist_smul (h : GraphAction G A) (a : A) (x y : V) :
    G.dist (a • x) (a • y) = G.dist x y := by
  simp only [SimpleGraph.dist, h.edist_smul]

theorem nonbacktracking_map_iff (h : GraphAction G A) (a : A)
    {n : ℕ} {x : V} (p : BasedWalk G n x) :
    (p.map (h.hom a)).Nonbacktracking ↔ p.Nonbacktracking := by
  apply BasedWalk.nonbacktracking_map_iff
  intro x b c heq
  apply Subtype.ext
  exact (MulAction.toPerm a).injective (congrArg Subtype.val heq)

end GraphAction

/-- The stabilizer of `u` is transitive on all nonbacktracking `n`-walks from `u`.
The list equation is the literal action on every vertex of the walk. -/
def RootPathTransitive (G : SimpleGraph V) (A : Type v) [Group A] [MulAction A V]
    (u : V) (n : ℕ) : Prop :=
  ∀ (p q : BasedWalk G n u), p.Nonbacktracking → q.Nonbacktracking →
    ∃ a : A, a • u = u ∧ p.vertices.map (a • ·) = q.vertices

/-- A vertex stabilizer is transitive on a sphere for the Mathlib graph distance. -/
def SphereTransitive (G : SimpleGraph V) (A : Type v) [Group A] [MulAction A V]
    (u : V) (n : ℕ) : Prop :=
  ∀ x y, G.dist u x = n → G.dist u y = n →
    ∃ a : A, a • u = u ∧ a • x = y

/-- An equality between the acted-on vertex lists also identifies the endpoints. -/
theorem endpoint_smul_of_vertices (h : GraphAction G A) {n k : ℕ} {x y : V}
    (a : A) (p : BasedWalk G n x) (q : BasedWalk G k y)
    (heq : p.vertices.map (a • ·) = q.vertices) : a • p.endpoint = q.endpoint := by
  have heq' : (p.map (h.hom a)).vertices = q.vertices := by
    rw [BasedWalk.vertices_map]
    exact heq
  have hend := BasedWalk.endpoint_eq_of_vertices_eq _ _ heq'
  rw [BasedWalk.endpoint_map] at hend
  exact hend

namespace RootPathTransitive

/-- Surjectivity of truncation descends stabilizer transitivity to every shorter
length. This is the first paragraph of the proof of F.3.5. -/
theorem mono {u : V} {n N : ℕ} (ht : RootPathTransitive G A u N)
    (hdeg : BasedWalk.HasTwoNeighbors G) (hn : n ≤ N) :
    RootPathTransitive G A u n := by
  intro p q hp hq
  obtain ⟨p', hp', heqp⟩ := BasedWalk.exists_extension hdeg hn p hp
  obtain ⟨q', hq', heqq⟩ := BasedWalk.exists_extension hdeg hn q hq
  obtain ⟨a, hau, ha⟩ := ht p' q' hp' hq'
  refine ⟨a, hau, ?_⟩
  have htake := congrArg (List.take (n + 1)) ha
  rw [← List.map_take, ← BasedWalk.vertices_take n hn p',
    ← BasedWalk.vertices_take n hn q', heqp, heqq] at htake
  exact htake

/-- Shortest walks give sphere transitivity without any assumption that all
nonbacktracking walks of this length are geodesic. -/
theorem sphereTransitive {u : V} {n : ℕ} (ht : RootPathTransitive G A u n)
    (h : GraphAction G A) (hconn : G.Connected) : SphereTransitive G A u n := by
  intro x y hx hy
  obtain ⟨p, hp, hpx⟩ := BasedWalk.exists_geodesic (hconn u x)
  obtain ⟨q, hq, hqy⟩ := BasedWalk.exists_geodesic (hconn u y)
  let p' : BasedWalk G n u := hx ▸ p
  let q' : BasedWalk G n u := hy ▸ q
  have hp' : p'.Nonbacktracking := by simpa only [p', BasedWalk.nonbacktracking_cast] using hp
  have hq' : q'.Nonbacktracking := by simpa only [q', BasedWalk.nonbacktracking_cast] using hq
  obtain ⟨a, hau, ha⟩ := ht p' q' hp' hq'
  refine ⟨a, hau, ?_⟩
  have hend := endpoint_smul_of_vertices h a p' q' ha
  simpa only [p', q', BasedWalk.endpoint_cast, hpx, hqy] using hend

/-- All nonbacktracking walks in one transitive rooted orbit have the same
endpoint distance. This is the metric comparison used in the rigidity proof. -/
theorem distance_eq {u : V} {n : ℕ} (ht : RootPathTransitive G A u n)
    (h : GraphAction G A) (p q : BasedWalk G n u)
    (hp : p.Nonbacktracking) (hq : q.Nonbacktracking) :
    G.dist u p.endpoint = G.dist u q.endpoint := by
  obtain ⟨a, hau, ha⟩ := ht p q hp hq
  have hend := endpoint_smul_of_vertices h a p q ha
  have hdist := h.dist_smul a u p.endpoint
  rw [hau, hend] at hdist
  exact hdist.symm

/-- One geodesic in a transitive rooted orbit forces every walk in that orbit
to be geodesic. -/
theorem geodesic_of_exists {u : V} {n : ℕ} (ht : RootPathTransitive G A u n)
    (h : GraphAction G A)
    (hex : ∃ p : BasedWalk G n u, p.Nonbacktracking ∧ G.dist u p.endpoint = n) :
    ∀ q : BasedWalk G n u, q.Nonbacktracking → G.dist u q.endpoint = n := by
  obtain ⟨p, hp, hdist⟩ := hex
  intro q hq
  exact (ht.distance_eq h q p hq hp).trans hdist

end RootPathTransitive
end SimpleGraph.PathTransitivePolygon
