module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramData

/-!
# Quotient multiplication checks, batch 0

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
theorem block0 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 0 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block1 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 1 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block2 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 2 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block3 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 3 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block4 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 4 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block5 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 5 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block6 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 6 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block7 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 7 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

end ProgramChecks

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
