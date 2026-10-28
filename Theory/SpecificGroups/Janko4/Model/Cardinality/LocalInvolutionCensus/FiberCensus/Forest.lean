module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Labels
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.KernelRows
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Assembly
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage

/-!
# The labelled max2 source forest

Every square-one coordinate in the four literal source fibers belongs to a
published mask list and is conjugate, inside the source subgroup, to that
list's representative. Only the local order upper bound is required.

The checked earlier-parent relation propagates conjugacy along the certified
edges. The edge proof establishes quotient equality before using first-row
faithfulness under the order bound. Independent row exclusions place every
square-one coordinate in one of the lists. `source_forest` discharges both
inputs of `source_forest_of_edges_and_coverage` with these certificates.

Source motivation: Aschbacher--Smith, refs/quasithin.pdf, printed pp.64--65,
A.6.1--4. ATLAS witness provenance is in FiberCensus/source/README.md.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- The labelled conjugacy cover of all square-one coordinates, with
conjugacy inside the literal source subgroup. -/
theorem source_forest (hH : Nat.card H ≤ 21799895040)
    (j : Fin 4) (m : Fin 8192) (hs : (sourceElement j m) ^ 2 = 1) :
    ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k ∧
      IsConj (sourceRepresentative k) (sourceElement j m) :=
  source_forest_of_edges_and_coverage (Forest.edges hH) Forest.square_one_covered j m hs

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus
