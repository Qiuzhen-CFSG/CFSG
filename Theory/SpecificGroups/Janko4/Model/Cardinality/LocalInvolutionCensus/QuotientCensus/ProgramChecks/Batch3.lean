module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramData

/-!
# Quotient multiplication checks, batch 3

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
theorem block24 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 24 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block25 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 25 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block26 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 26 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block27 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 27 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block28 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 28 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block29 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 29 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block30 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 30 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block31 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 31 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

end ProgramChecks

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
