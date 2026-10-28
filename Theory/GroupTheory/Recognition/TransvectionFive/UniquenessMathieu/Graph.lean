module

public import Theory.GroupTheory.GraphUniquenessSystem.Recognition
public import Theory.GroupTheory.GraphUniquenessSystem.PairGraphRecognition
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.Normalizer
public import Theory.Mathieu.M24.Properties.Simplicity
public import Theory.Mathieu.M24.Properties.Transitivity

/-!
# Graph data for the Mathieu uniqueness route

The uniqueness theorem is applied to actual `GraphUniquenessSystem.System`s.
The source system and all local comparisons are therefore explicit data; no
abstract family tag is used in their place.  The target is the pair graph on
24 points.  Four-transitivity proves its cycle-base condition from the local
edge relation, which is the base step in Aschbacher's §41 argument.
-/

@[expose] public section
namespace Theory.GroupTheory.TransvectionFive

open Subgroup
open Theory.GroupTheory.GraphUniquenessSystem
open Theory.Combinatorics.PairGraph

universe u v w

variable {G : Type u} [Group G]
variable {V : Type v} [MulAction G V]
variable {z : G}

/-- A concrete source/model comparison for the M24 uniqueness argument.

`source` is the graph system reconstructed from the original local data.
`model` is the actual pair-graph system on the native degree-24 Mathieu
carrier.  The model's local orbit is required to be the induced graph on a
four-set, exactly the relation needed by the four-subset base theorem. -/
public structure MathieuGraphComparison where
  source : GraphUniquenessSystem.System G V
  model : GraphUniquenessSystem.System Sporadic.Mathieu.M24
    (Vertex (Fin 24))
  similarity : GraphUniquenessSystem.Similarity source model
  model_graph : model.graph = graph (Fin 24)
  four_set : Finset (Fin 24)
  four_set_card : four_set.card = 4
  model_local : ∀ a b,
    model.localEdge a b ↔
      (graph (Fin 24)).Adj a b ∧ a.val ⊆ four_set ∧ b.val ⊆ four_set
  equivalence : similarity.IsEquivalence

/-- The complete source witness consumed by the §41 assembly.  The normalizer
and type record and the graph comparison are separate fields so that neither
one can be replaced by the final group isomorphism. -/
public structure MathieuSourceWitness (F : MarkedCentralizer z) where
  normalizer : NormalizerTypeConsequences F
  W : Type w
  action : MulAction G W
  graphData : @MathieuGraphComparison G _ W action

namespace MathieuGraphComparison

variable (D : MathieuGraphComparison (G := G) (V := V))

/-- The native M24 pair-graph system has the required cycle base. -/
public theorem model_isBase : D.model.IsBase := by
  let : MulAction.IsMultiplyPretransitive Sporadic.Mathieu.M24 (Fin 24) 5 :=
    Sporadic.Mathieu.m24_isFivePretransitive
  let : MulAction.IsMultiplyPretransitive Sporadic.Mathieu.M24 (Fin 24) 4 :=
    MulAction.isMultiplyPretransitive_of_le (G := Sporadic.Mathieu.M24)
      (α := Fin 24) (m := 4) (n := 5) (by decide) (by simp)
  exact D.model.isBase_of_pairGraph_fourSubset D.model_graph D.four_set
    D.four_set_card D.model_local

/-- The source system is recognized from the explicit model comparison. -/
public theorem exists_mulEquiv (D : MathieuGraphComparison (G := G) (V := V)) :
    Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  let : IsSimpleGroup Sporadic.Mathieu.M24 :=
    Sporadic.Mathieu.m24_isSimpleGroup
  obtain ⟨e, _⟩ :=
    GraphUniquenessSystem.Similarity.existsUnique_mulEquiv_of_isEquivalence_of_isBase
      D.similarity D.equivalence D.model_isBase
  exact ⟨e⟩

end MathieuGraphComparison

end Theory.GroupTheory.TransvectionFive
