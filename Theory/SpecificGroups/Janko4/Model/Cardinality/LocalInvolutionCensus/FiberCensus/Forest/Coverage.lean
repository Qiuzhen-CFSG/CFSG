module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.Transport
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.MatrixEvaluation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Labels

/-!
# Excluding unlisted square-one max2 coordinates

The algebraic reduction compares the first row of each literal source word
with the row of its inverse. A differing row excludes square-one without
an order bound, a quotient assumption, or a faithfulness assertion. The
certified matrix evaluations identify both rows with the packed algorithms;
the checked finite exclusion then places every square-one coordinate in
one of the eleven unchanged mask lists.

Source motivation: Aschbacher--Smith, `refs/quasithin.pdf`, printed
pp.64--65, A.6.1--4. The concrete ATLAS witnesses, attribution, and
certificate contracts are documented in `Coverage/source/README.md`.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest
open Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound
open KernelRows Coverage

/-- The actual source exclusion follows from independently certified matrix
values and packed-row exclusions. All remaining premises are explicit. -/
theorem square_one_covered_of_row_certificates
    (hlift : ∀ j, sourceMatrix (sourceLift j) = decodeRows (liftRows j))
    (hinvlift : ∀ j, sourceMatrix ((sourceLift j)⁻¹) = decodeRows (liftRows j))
    (hfactor : ∀ i,
      sourceMatrix ((kernelFactor i)⁻¹) = decodeRows (inverseFactorRows i))
    (hrows : ∀ (j : Fin 4) (m : Fin 8192), RowsAgree j m →
      ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k)
    (j : Fin 4) (m : Fin 8192) (hsq : (sourceElement j m)^2 = 1) :
    ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k :=
  hrows j m (rowsAgree_of_square_one hlift hinvlift hfactor j m hsq)

/-- Every square-one coordinate in the four literal source fibers occurs in
one of the published mask lists. No order or quotient premise is required. -/
theorem square_one_covered (j : Fin 4) (m : Fin 8192)
    (hsq : (sourceElement j m)^2 = 1) :
    ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k :=
  square_one_covered_of_row_certificates Coverage.eval_lift Coverage.eval_inverse_lift
    Coverage.eval_inverse_factor Coverage.rowsAgree_covered j m hsq

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest
