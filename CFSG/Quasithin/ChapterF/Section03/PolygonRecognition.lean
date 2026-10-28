module

public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon

/-!
# Initial reductions for F.3.5

The proof of Aschbacher–Smith, Lemma F.3.5 (printed pp. 271–272), begins by
extending nonbacktracking paths and descending the root-stabilizer transitivity
hypothesis to shorter lengths. The theorem below implements that reduction and
the resulting sphere transitivity in the literal graph and vertex action.
The coset-geometry instantiation belongs to the Section F.3 assembly.

This module does not yet assert all of F.3.5. In particular, deriving the global
diameter from transitivity at only one root is invalid without another global
hypothesis: AG(2,3) with its affine group is a thick edge-transitive bipartite
counterexample at m = 3. Its point stabilizer is transitive on four-edge
nonbacktracking paths, its point eccentricity is three, and its graph diameter
is four because distinct parallel lines have distance four. The full source
assembly must resolve the quantification over the two types before using a
polygon-recognition conclusion.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.PolygonRecognition

open SimpleGraph SimpleGraph.PathTransitivePolygon

universe u v
variable {V : Type u} {A : Type v} [Group A] [MulAction A V]
variable {G : SimpleGraph V}

/-- The short-path and sphere-transitivity assertions used at the start of
F.3.5. The degree condition states that every vertex has at least three neighbors,
without requiring finite neighbor sets. -/
theorem shorter_paths_and_spheres
    (hact : GraphAction G A) (hconn : G.Connected)
    (hthick : ∀ x a b : V, ∃ z, G.Adj x z ∧ z ≠ a ∧ z ≠ b)
    {u : V} {m : ℕ} (htrans : RootPathTransitive G A u (m + 1)) :
    ∀ i ≤ m + 1, RootPathTransitive G A u i ∧ SphereTransitive G A u i := by
  have hdeg : BasedWalk.HasTwoNeighbors G := by
    intro x y
    obtain ⟨z, hz, hzy, _⟩ := hthick x y y
    exact ⟨z, hz, hzy⟩
  intro i hi
  have ht := htrans.mono hdeg hi
  exact ⟨ht, ht.sphereTransitive hact hconn⟩

/-- Distance comparison for any two shorter nonbacktracking paths. This is the
contradiction principle used in the following rigidity paragraphs of F.3.5. -/
theorem shorter_path_distances_eq
    (hact : GraphAction G A)
    (hdeg : BasedWalk.HasTwoNeighbors G)
    {u : V} {m i : ℕ} (htrans : RootPathTransitive G A u (m + 1))
    (hi : i ≤ m + 1) (p q : BasedWalk G i u)
    (hp : p.Nonbacktracking) (hq : q.Nonbacktracking) :
    G.dist u p.endpoint = G.dist u q.endpoint :=
  (htrans.mono hdeg hi).distance_eq hact p q hp hq

end CFSG.Quasithin.ChapterF.PolygonRecognition
