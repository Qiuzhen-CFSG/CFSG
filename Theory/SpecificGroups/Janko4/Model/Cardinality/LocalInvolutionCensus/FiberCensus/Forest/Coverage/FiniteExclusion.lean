module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Assembly
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Forward0
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Backward0
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Matches0
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Forward1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Backward1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Matches1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Forward2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Backward2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Matches2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Forward3
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Backward3
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Matches3

/-!
# Finite packed-row exclusion for all four max2 fibers

The forward rows and the reverse inverse-word rows are identified with literal
tables by kernel-checked bounded recurrences. Equality of their decoded rows
then gives a checked index into one of the eleven unchanged mask lists.
This finite arithmetic theorem assumes no group, quotient, order, or matrix
evaluation result. Source: the ATLAS J4G1-max2W1 data of R. A. Wilson,
S. J. Nickerson and J. N. Bray; see `Coverage/source/README.md`.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage
open FiniteExclusion

/-- Every decoded packed-row match occurs in a published mask list of its fiber. -/
theorem rowsAgree_covered (j : Fin 4) (m : Fin 8192) (h : RowsAgree j m) :
    ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k := by
  fin_cases j
  · apply covered_of_tables 0 forwardTable0 backwardTable0
      forward_semantics0 backward_zero0 backward_steps0
      (fun a => (bounds0 a).1) (fun a => (bounds0 a).2) ?_ m h
    intro a
    simpa only [Fin.ofNat_val_eq_self] using matches0 a
  · apply covered_of_tables 1 forwardTable1 backwardTable1
      forward_semantics1 backward_zero1 backward_steps1
      (fun a => (bounds1 a).1) (fun a => (bounds1 a).2) ?_ m h
    intro a
    simpa only [Fin.ofNat_val_eq_self] using matches1 a
  · apply covered_of_tables 2 forwardTable2 backwardTable2
      forward_semantics2 backward_zero2 backward_steps2
      (fun a => (bounds2 a).1) (fun a => (bounds2 a).2) ?_ m h
    intro a
    simpa only [Fin.ofNat_val_eq_self] using matches2 a
  · apply covered_of_tables 3 forwardTable3 backwardTable3
      forward_semantics3 backward_zero3 backward_steps3
      (fun a => (bounds3 a).1) (fun a => (bounds3 a).2) ?_ m h
    intro a
    simpa only [Fin.ofNat_val_eq_self] using matches3 a

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage
