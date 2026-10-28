module

public import Theory.Combinatorics.PairGraphTriangleClosure.FourSubsetBase
public import Theory.GroupTheory.GraphUniquenessSystem

/-!
# The four-subset base for a graph uniqueness system

When the ambient graph is the pair graph and the local edge orbit is its
induced graph on four points, four-transitivity implies the actual `IsBase`
condition. The bridge preserves the local edge relation and uses the published
nonabelian closed-walk closure. Its cycle filling and translation inputs are
proved in `FourSubsetBase`.

Source: Aschbacher–Smith, §5.2, proof of Theorem 5.2.10, printed p.658;
Aschbacher, *Sporadic Groups*, §37, p.200.
-/

@[expose] public section

namespace Theory.GroupTheory.GraphUniquenessSystem.System
open Theory.Combinatorics.PairGraph SimpleGraph.WalkClosure
variable {α G : Type*} [DecidableEq α] [Group G] [MulAction G α]
  [Finite α] [MulAction.IsMultiplyPretransitive G α 4]

/-- An induced four-point local orbit is a base for the pair-graph system. -/
theorem isBase_of_pairGraph_fourSubset (U : System G (Vertex α))
    (hgraph : U.graph = Theory.Combinatorics.PairGraph.graph α) (s : Finset α) (hs : s.card = 4)
    (hlocal : ∀ a b, U.localEdge a b ↔
      (Theory.Combinatorics.PairGraph.graph α).Adj a b ∧ a.val ⊆ s ∧ b.val ⊆ s) : U.IsBase := by
  change IsCycleBase (Γ := U.graph)
    (fun _ p => ∃ g : G, Supported (fun a b => U.localEdge (g⁻¹ • a) (g⁻¹ • b)) p)
  rw [hgraph]
  exact fourSubset_edge_isCycleBase s hs U.localEdge
    (fun {a b} hab ha hb => (hlocal a b).mpr ⟨hab, ha, hb⟩)
end Theory.GroupTheory.GraphUniquenessSystem.System
