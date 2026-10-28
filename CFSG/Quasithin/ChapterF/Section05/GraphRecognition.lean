module

public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.SimplyConnected
public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.Action
public import Theory.GroupTheory.Amalgam.UniquenessSystem.Recognition

/-!
# The geometric recognition step in F.5

The concrete ternary graph is simply connected. If the actual orthogonal
group's local triangle is its triangle orbit, that triangle is a cycle base.
An equivalent uniqueness system then identifies the acting groups, extending
both prescribed local maps, provided the orthogonal group is simple.

This discharges the graph-contraction premise of the last paragraph of F.5,
printed pp.303--304. Construction of the two systems, F.5.7 equivalence, the
triangle orbit, and the identification of the concrete orthogonal group with
PSL₄(3) remain explicit obligations; this is not the unconditional F.4.31.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterF.Section05.GraphRecognition

open Theory.GroupTheory.GraphUniquenessSystem
open OmegaSixThree.OrthogonalityGraph

local notation "Model" => OmegaSixThree.omegaPlusSixThree

variable (U : System Model Point) (hgraph : U.graph = graph)
include hgraph

/-- F.5.8(3), conditional only on the actual local triangle and its orbit.
The graph's simple connectivity is proved internally. -/
theorem model_isBase (T : U.LocalTriangle) (ht : T.IsTriangleOrbit) : U.IsBase := by
  apply T.isBase _ ht
  rw [hgraph]
  exact triangleSimplyConnected

variable {G V : Type*} [Group G] [MulAction G V]
variable {U} {W : System G V} [IsSimpleGroup Model]

/-- The final uniqueness-system argument of F.5, with the model-to-source
orientation of the book. Both marked local isomorphisms are preserved. -/
theorem existsUnique_equiv (s : Similarity U W) (hs : s.IsEquivalence)
    (T : U.LocalTriangle) (ht : T.IsTriangleOrbit) :
    ∃! e : Model ≃* G,
      (∀ a : U.vertexGroup, e a = (s.vertexIso a : G)) ∧
      (∀ a : U.H, e a = (s.localIso a : G)) :=
  s.existsUnique_mulEquiv_of_isEquivalence_of_sourceBase hs
    (model_isBase U hgraph T ht)

end CFSG.Quasithin.ChapterF.Section05.GraphRecognition
