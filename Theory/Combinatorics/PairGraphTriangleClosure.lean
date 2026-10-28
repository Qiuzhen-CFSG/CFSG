module

public import Theory.Combinatorics.PairGraphLocalGeometry
public import Theory.Combinatorics.PairGraphTriangleClosure.WalkClosure

/-!
# Cycle bases for pair graphs

This interface connects the pair graph geometry to the nonabelian cycle closure
used by uniqueness systems. The closure and triangulability notions are those of
Aschbacher, *Sporadic Groups*, §§33--34 and §37, p.200; the intended application
is Aschbacher--Smith, §5.2, printed p.658.
-/

@[expose] public section

namespace Theory.Combinatorics.PairGraph

variable {α : Type*} [DecidableEq α]

/-- Cycles lying in the pair graph induced on a specified subset of points. -/
def cyclesOn (s : Finset α) : SimpleGraph.WalkClosure.Cycles (graph α) :=
  fun _ p => ∀ v ∈ p.support, v.val ⊆ s

/-- Enlarging the point set enlarges the family of supported cycles. -/
theorem cyclesOn_mono {s t : Finset α} (hst : s ⊆ t) (x : Vertex α) :
    cyclesOn s x ⊆ cyclesOn t x := by
  intro p hp v hv
  exact (hp v hv).trans hst

end Theory.Combinatorics.PairGraph
