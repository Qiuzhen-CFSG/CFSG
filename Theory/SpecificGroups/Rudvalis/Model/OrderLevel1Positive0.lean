module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0Prefix
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockA
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockB
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockC
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockD

/-!
# Assembly of the first positive Rudvalis level-1 transition

The initial eighty representatives are certified in `OrderLevel1Positive0Prefix`.
Four independent ranges cover the remaining batches. This module assembles their
transition identities by the division into batches proved in `OrderLevel1Reduction`.
The witnesses are the ATLAS-derived data documented in `OrderLevel1Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0
open Level1Reduction Theory.GroupTheory

/-- Assemble the initial certificate and the four remaining batch ranges. -/
public theorem assemble
    (hA : ∀ b : Fin 84, stepBatch 0 ⟨16 + b.val, by omega⟩)
    (hB : ∀ b : Fin 84, stepBatch 0 ⟨100 + b.val, by omega⟩)
    (hC : ∀ b : Fin 84, stepBatch 0 ⟨184 + b.val, by omega⟩)
    (hD : ∀ b : Fin 83, stepBatch 0 ⟨268 + b.val, by omega⟩)
    (r : Fin 1755) :
    L1Gen 0 * L1Rep r = L1Rep (L1Act 0 r) * evalWord L2Gen (L1Factor 0 r) := by
  apply positiveStep_of_batches 0
  intro b
  by_cases h16 : b.val < 16
  · exact initial ⟨b.val, h16⟩
  by_cases h100 : b.val < 100
  · have he : 16 + (b.val - 16) = b.val := by omega
    simpa only [he] using hA ⟨b.val - 16, by omega⟩
  by_cases h184 : b.val < 184
  · have he : 100 + (b.val - 100) = b.val := by omega
    simpa only [he] using hB ⟨b.val - 100, by omega⟩
  by_cases h268 : b.val < 268
  · have he : 184 + (b.val - 184) = b.val := by omega
    simpa only [he] using hC ⟨b.val - 184, by omega⟩
  · have he : 268 + (b.val - 268) = b.val := by omega
    simpa only [he] using hD ⟨b.val - 268, by omega⟩

end Rudvalis.OrderCertificate.OrderLevel1Positive0

namespace Rudvalis.OrderCertificate

/-- The first positive generator satisfies every level-1 transition identity. -/
public theorem L1PositiveStep0 (r : Fin 1755) :
    L1Gen 0 * L1Rep r = L1Rep (L1Act 0 r) *
      Theory.GroupTheory.evalWord L2Gen (L1Factor 0 r) :=
  OrderLevel1Positive0.assemble OrderLevel1Positive0.blockA
    OrderLevel1Positive0.blockB OrderLevel1Positive0.blockC OrderLevel1Positive0.blockD r

end Rudvalis.OrderCertificate
