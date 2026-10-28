module

public import Theory.GroupTheory.GraphUniquenessSystem.Recognition
public import Theory.Combinatorics.PairGraphTriangleClosure.FourSubsetBase.SystemBridge

/-!
# Recognition by a four-transitive pair-graph system

For a simple group acting four-transitively on a finite point set, suppose the
uniqueness system has the pair graph as its ambient graph and the induced graph
on a four-set as its local edge orbit. Its local graph is a base: triangles use
at most four points, four-transitivity moves their supports into the four-set,
and every closed walk is in the nonabelian closure of triangles.

Thus equivalence, or similarity with a rigid edge fixer, gives the unique group
isomorphism extending the two local comparisons. All three generation
conditions are explicit fields of `System`; compatibility on the local
intersections is recorded by `Similarity`. The final rigidity theorem requires
neither a cycle-base premise nor an equivalence premise.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, proof of
Theorem 5.2.10, printed pp.657–658; Aschbacher, *Sporadic Groups*, §§33–37.
-/

@[expose] public section

namespace Theory.GroupTheory.GraphUniquenessSystem.Similarity

open Theory.Combinatorics.PairGraph

universe u v u' w
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable {G' : Type u'} {α : Type w} [Group G'] [MulAction G' α]
variable [DecidableEq α] [Finite α] [MulAction.IsMultiplyPretransitive G' α 4]
variable [IsSimpleGroup G']
variable {U : System G V} {U' : System G' (Vertex α)} (s : Similarity U U')

/-- Equivalence recognizes a simple four-transitive pair-graph target, using
only its induced four-point local graph to establish the cycle base. -/
theorem existsUnique_mulEquiv_of_isEquivalence_of_pairGraph_fourSubset
    (he : s.IsEquivalence) (hgraph : U'.graph = graph α)
    (q : Finset α) (hq : q.card = 4)
    (hlocal : ∀ a b, U'.localEdge a b ↔ (graph α).Adj a b ∧ a.val ⊆ q ∧ b.val ⊆ q) :
    ∃! e : G ≃* G',
      (∀ a : U.vertexGroup, e a = (s.vertexIso a : G')) ∧
      (∀ a : U.H, e a = (s.localIso a : G')) :=
  s.existsUnique_mulEquiv_of_isEquivalence_of_isBase he
    (U'.isBase_of_pairGraph_fourSubset hgraph q hq hlocal)

/-- Pair-graph recognition from compatible local comparisons and the trivial
pointwise automorphism centralizer of the source edge fixer. This is the
specialized 37.9 route for the final step of Aschbacher–Smith 5.2.10. -/
theorem existsUnique_mulEquiv_of_rigid_of_pairGraph_fourSubset
    (hRigid : AutomorphismRigid (U.H.subgroupOf U.edgeGroup))
    (hgraph : U'.graph = graph α) (q : Finset α) (hq : q.card = 4)
    (hlocal : ∀ a b, U'.localEdge a b ↔ (graph α).Adj a b ∧ a.val ⊆ q ∧ b.val ⊆ q) :
    ∃! e : G ≃* G',
      (∀ a : U.vertexGroup, e a = (s.vertexIso a : G')) ∧
      (∀ a : U.H, e a = (s.localIso a : G')) :=
  s.existsUnique_mulEquiv_of_isEquivalence_of_pairGraph_fourSubset
    (s.isEquivalence_of_rigid hRigid) hgraph q hq hlocal

end Theory.GroupTheory.GraphUniquenessSystem.Similarity
