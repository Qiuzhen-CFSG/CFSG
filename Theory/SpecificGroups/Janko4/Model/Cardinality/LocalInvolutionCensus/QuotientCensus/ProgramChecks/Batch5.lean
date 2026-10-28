module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramData

/-!
# Quotient multiplication checks, batch 5

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
theorem block40 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 40 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block41 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 41 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block42 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 42 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block43 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 43 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block44 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 44 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block45 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 45 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block46 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 46 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block47 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 47 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

end ProgramChecks

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
