/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Graphs/TransitiveStronglyRegular.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Theory.AtlasPort.OtherSporadic.Graphs.CommonNeighborsEquiv

/-!
# TransitiveStronglyRegular

A transitive graph action transports counts at one vertex to every vertex.
Graph automorphisms identify neighbor and common-neighbor sets, so base counts
give strong regularity without any recognition assumption.

Source: Gerald Höhn, ATLAS, `Atlas/Graphs/TransitiveStronglyRegular.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries, rewritten imports,
and an explicit finite-cardinality import. The graph-equivalence helper is
re-exported from `CommonNeighborsEquiv` for use independently of strong regularity.
-/

@[expose] public section

noncomputable section
namespace Atlas.Graphs

/-- For a transitive graph action, neighbor and pair counts at one base vertex
suffice to establish the full strongly regular graph statement. -/
theorem srg_of_transitive_base_counts {G V : Type*} [Group G] [MulAction G V]
    [MulAction.IsPretransitive G V] [Fintype V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (ha : ∀ g : G, ∀ x y : V, A.Adj (g • x) (g • y) ↔ A.Adj x y)
    (v : V) (n k l m : ℕ) (hn : Nat.card V = n)
    (hk : Nat.card (A.neighborSet v) = k)
    (hl : ∀ w, A.Adj v w → Nat.card (A.commonNeighbors v w) = l)
    (hm : ∀ w, v ≠ w → ¬A.Adj v w → Nat.card (A.commonNeighbors v w) = m) :
    A.IsSRGWith n k l m := by
  let e (g : G) : A ≃g A :=
    { toEquiv := MulAction.toPerm g
      map_rel_iff' := ha g _ _ }
  refine ⟨?_,?_,?_,?_⟩
  · exact (Nat.card_eq_fintype_card).symm.trans hn
  · intro x
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G v x
    have he := Nat.card_congr ((e g).mapNeighborSet v)
    change Nat.card (A.neighborSet v) = Nat.card (A.neighborSet (g • v)) at he
    rw [hg,hk] at he
    simpa only [Nat.card_eq_fintype_card,A.card_neighborSet_eq_degree] using he.symm
  · intro x y hxy
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G v x
    have hgv : g • (g⁻¹ • y) = y := smul_inv_smul _ _
    have he := Nat.card_congr (commonNeighborsEquiv (e g) v (g⁻¹ • y))
    change Nat.card (A.commonNeighbors v (g⁻¹ • y)) = Nat.card (A.commonNeighbors (g • v) (g • (g⁻¹ • y))) at he
    rw [hg,hgv] at he
    have hh : A.Adj v (g⁻¹ • y) := (ha g _ _).mp (by rwa [hg,hgv])
    rw [hl _ hh] at he
    simpa only [Nat.card_eq_fintype_card] using he.symm
  · intro x y hne hxy
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G v x
    have hgv : g • (g⁻¹ • y) = y := smul_inv_smul _ _
    have he := Nat.card_congr (commonNeighborsEquiv (e g) v (g⁻¹ • y))
    change Nat.card (A.commonNeighbors v (g⁻¹ • y)) = Nat.card (A.commonNeighbors (g • v) (g • (g⁻¹ • y))) at he
    rw [hg,hgv] at he
    have hh : ¬A.Adj v (g⁻¹ • y) := fun h => hxy (by simpa only [hg,hgv] using (ha g _ _).mpr h)
    have hn' : v ≠ g⁻¹ • y := by
      intro h
      exact hne (hg.symm.trans ((congrArg (fun z => g • z) h).trans hgv))
    rw [hm _ hn' hh] at he
    simpa only [Nat.card_eq_fintype_card] using he.symm

end Atlas.Graphs
