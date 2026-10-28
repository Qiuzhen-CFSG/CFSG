module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.Reduction
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.Lifts
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedRows

/-!
# Certified literal max2 forest edges

The full actor-matrix evaluations and packed crossing-row certificates prove
all 4725 nonroot conjugation equations in the literal source subgroup. The
assembly uses the certified lifts and actual quotient centralization; together
with the local order bound, equal first rows imply the full group equality.
`edges` discharges both certificate families in `edges_of_certificates`.

Source and ATLAS attribution: `Edges/source/README.md`; the local counting
motivation is refs/quasithin.pdf, printed pp.64--65, A.6.1--4.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest
open Edges KernelRows
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- Assemble literal edges from the two independent certificate families. -/
theorem edges_of_certificates (hH : Nat.card H ≤ 21799895040)
    (ha : ∀ k n, sourceMatrix (actorAt k n) = decodeRows (actorRowsAt k n))
    (he : ∀ (k : Fin 11) (n : Fin (fiberBound k)), n.val ≠ 0 → PackedEdge k n.val)
    (k : Fin 11) (n : Fin (fiberBound k)) (hn : n.val ≠ 0) : Edge k n.val :=
  edge_of_packed hH k n (liftRows_spec (fiberIndex k)) (ha k n.val) (he k n hn)

/-- Every prescribed nonroot edge is a literal source-subgroup conjugation
equality, under only the local order bound. -/
theorem edges (hH : Nat.card H ≤ 21799895040)
    (k : Fin 11) (n : Fin (fiberBound k)) (hn : n.val ≠ 0) : Edge k n.val :=
  edges_of_certificates hH actorRowsAt_spec packed_edges k n hn

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest
