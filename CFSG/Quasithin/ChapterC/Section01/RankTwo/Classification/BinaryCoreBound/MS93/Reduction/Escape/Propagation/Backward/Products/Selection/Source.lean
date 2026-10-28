module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.SelectionGeometry

/-!
# Local comparisons needed for the two edge choices

The first comparison concerns the actual natural eight-group at the start
of a contrary critical pair. Its endpoint-fixed plane is the displacement
at the first path edge. Generating edges cut that plane in lines which,
together with the critical commutator, generate the plane. Two such lines
must actually occur.

The second comparison bounds the predecessor commutator of a backward span
already contained in the kernel four before the endpoint. Neither contract
asserts the existence of an edge with a favorable backward-span bound.
Their producers are required before the conditional selection assembly can
be used as a source theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.7)(i), pp.887--888.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

/-- The intersection line at a chosen incident edge, inside the first
path-edge plane. This uses the actual amalgam subgroups. -/
noncomputable def edgeLine (p : Counterexample geometry) (β t : Vertex R) :
    Subgroup (FreeAmalgam R) := edgeDisplacement p.a t ⊓ Z R β

/-- Local natural-module targets, with no backward-span containment in
any field. In applications β is the first neighbor on the critical path. -/
structure PencilFacts (p : Counterexample geometry) (β : Vertex R) : Prop where
  fixed_plane : U R p.a ⊓ centralizer (Z R p.a' : Set (FreeAmalgam R)) =
    edgeDisplacement p.a β
  line_card : ∀ t, Adjacent R p.a t →
    (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a →
      Nat.card (edgeLine p β t) = 2
  line_join : ∀ t, Adjacent R p.a t →
    (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a →
      edgeLine p β t ⊔ criticalCommutator p.a p.a' = edgeDisplacement p.a β
  two_lines : ∃ t u, Adjacent R p.a t ∧
    (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a ∧
    Adjacent R p.a u ∧
    (stabilizer R p.a ⊓ stabilizer R u) ⊔ Z R p.a' = stabilizer R p.a ∧
    edgeLine p β t ≠ edgeLine p β u

/-- The predecessor commutator comparison on printed p.888. Its antecedent
is the first favorable bound; its conclusion is a containment, not a
selected-edge witness. The source proof must construct this comparison. -/
def PredecessorComparison (geometry : Geometry R) : Prop :=
  ∀ p : Counterexample geometry, ∀ d t,
    Before p.a p.a' d 4 → Adjacent R p.a t →
    (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a →
      backwardSpan geometry p.a t ≤ Q R d →
      ⁅backwardSpan geometry p.a t, Z R p.c⁆ ≤ edgeDisplacement p.a t

/-- The source generating subgroup from MS93 p.881.  It is the relative
normalizer in the local stabilizer, rather than the edge stabilizer. -/
def relativeGenerating (p : Counterexample geometry) (t : Vertex R) : Prop :=
  (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔ Z R p.a' =
    stabilizer R p.a

/-- The corrected reverse-span clause of (4.3.6), with the generating group
from the source definition of G_(a,t).  The legacy `BoundFacts` record is
retained unchanged; this record is the source-facing extension consumed by
the corrected selection assembly. -/
structure RelativeBoundFacts (geometry : Geometry R) : Prop where
  bound : ∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
    ¬ radiusCommutator p.a p.a' ≤ localCenter d →
      d ∈ movingNeighbors geometry p.c ∧
      ∀ t, Adjacent R p.a t → relativeGenerating p t →
        backwardSpan geometry p.a t ≤ Q R d

/-- Pencil identities with the source relative normalizer as generating
premise.  The older `PencilFacts` record above remains the raw edge-stabilizer
interface used by the legacy conditional helpers. -/
structure RelativePencilFacts (p : Counterexample geometry) (β : Vertex R) : Prop where
  fixed_plane : U R p.a ⊓ centralizer (Z R p.a' : Set (FreeAmalgam R)) =
    edgeDisplacement p.a β
  line_card : ∀ t, Adjacent R p.a t → relativeGenerating p t →
    Nat.card (edgeLine p β t) = 2
  line_join : ∀ t, Adjacent R p.a t → relativeGenerating p t →
    edgeLine p β t ⊔ criticalCommutator p.a p.a' = edgeDisplacement p.a β
  two_lines : ∃ t u, Adjacent R p.a t ∧ relativeGenerating p t ∧
    Adjacent R p.a u ∧ relativeGenerating p u ∧
    edgeLine p β t ≠ edgeLine p β u

/-- The predecessor comparison with the corrected source generating premise. -/
def RelativePredecessorComparison (geometry : Geometry R) : Prop :=
  ∀ p : Counterexample geometry, ∀ d t,
    Before p.a p.a' d 4 → Adjacent R p.a t → relativeGenerating p t →
    backwardSpan geometry p.a t ≤ Q R d →
      ⁅backwardSpan geometry p.a t, Z R p.c⁆ ≤ edgeDisplacement p.a t

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
