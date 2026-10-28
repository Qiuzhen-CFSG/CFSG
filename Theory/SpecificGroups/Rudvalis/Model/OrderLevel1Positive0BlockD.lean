module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockD328To337
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockD338To347
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockD348To350

/-!
# Final block of positive-generator-0 Rudvalis level-1 transitions

Batches 268 through 350 cover representatives 1340 through 1754. The imported
checkpoints certify each transition by free cancellation or kernel computation
at every point of the degree-4060 action. This module assembles those checkpoints.

Source: the ATLAS-derived witnesses documented in `OrderLevel1Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0

/-- The final 415 representatives satisfy the positive-generator-0 transition. -/
public theorem blockD (b : Fin 83) :
    Level1Reduction.stepBatch 0 ⟨268 + b.val, by omega⟩ := by
  by_cases h10 : b.val < 10
  · exact segment268 ⟨b.val, h10⟩
  by_cases h20 : b.val < 20
  · have he : 278 + (b.val - 10) = 268 + b.val := by omega
    simpa only [he] using segment278 ⟨b.val - 10, by omega⟩
  by_cases h30 : b.val < 30
  · have he : 288 + (b.val - 20) = 268 + b.val := by omega
    simpa only [he] using segment288 ⟨b.val - 20, by omega⟩
  by_cases h40 : b.val < 40
  · have he : 298 + (b.val - 30) = 268 + b.val := by omega
    simpa only [he] using segment298 ⟨b.val - 30, by omega⟩
  by_cases h50 : b.val < 50
  · have he : 308 + (b.val - 40) = 268 + b.val := by omega
    simpa only [he] using segment308 ⟨b.val - 40, by omega⟩
  by_cases h60 : b.val < 60
  · have he : 318 + (b.val - 50) = 268 + b.val := by omega
    simpa only [he] using segment318 ⟨b.val - 50, by omega⟩
  by_cases h70 : b.val < 70
  · have he : 328 + (b.val - 60) = 268 + b.val := by omega
    simpa only [he] using segment328 ⟨b.val - 60, by omega⟩
  by_cases h80 : b.val < 80
  · have he : 338 + (b.val - 70) = 268 + b.val := by omega
    simpa only [he] using segment338 ⟨b.val - 70, by omega⟩
  have he : 348 + (b.val - 80) = 268 + b.val := by omega
  simpa only [he] using segment348 ⟨b.val - 80, by omega⟩

end Rudvalis.OrderCertificate.OrderLevel1Positive0
