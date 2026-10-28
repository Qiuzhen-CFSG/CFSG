module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.ProgramData

/-!
# Quotient multiplication checks, batch 1

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
theorem block8 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 8 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block9 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 9 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block10 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 10 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block11 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 11 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block12 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 12 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block13 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 13 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block14 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 14 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem block15 : ∀ r : Fin 128,
    programCheck (Fin.ofNat 7392 (128 * 15 + r.val)) := by
  apply forall_fin_of_range
  decide +kernel

end ProgramChecks

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
