module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramData

/-!
# Quotient multiplication checks, batch 6

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
theorem block48 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 48 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block49 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 49 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block50 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 50 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block51 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 51 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block52 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 52 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block53 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 53 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block54 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 54 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block55 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 55 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

end ProgramChecks

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
