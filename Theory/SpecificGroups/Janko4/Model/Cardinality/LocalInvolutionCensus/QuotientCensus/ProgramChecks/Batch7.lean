module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramData

/-!
# Quotient multiplication checks, batch 7

These kernel computations certify a bounded part of the fixed multiplication
program. Separating batches limits memory and caches the expensive arithmetic
independently of the membership and counting proofs. See `source/README.md`.
-/

set_option maxRecDepth 100000

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound QuotientOrderCertificate

namespace ProgramChecks

set_option maxHeartbeats 4000000 in
theorem block56 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 56 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block57 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 57 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

end ProgramChecks

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
