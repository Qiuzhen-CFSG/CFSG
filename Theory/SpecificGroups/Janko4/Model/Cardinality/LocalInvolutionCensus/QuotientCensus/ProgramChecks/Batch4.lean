module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramData

/-!
# Quotient multiplication checks, batch 4

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
theorem block32 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 32 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block33 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 33 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block34 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 34 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block35 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 35 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block36 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 36 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block37 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 37 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block38 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 38 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block39 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 39 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

end ProgramChecks

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
