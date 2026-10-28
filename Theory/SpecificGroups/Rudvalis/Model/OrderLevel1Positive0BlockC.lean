module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockCPart0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockCPart1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockC204To213
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockC214To223
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockC224To233
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockC234To243
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockC244To253
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockC254To263
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockC264To267

/-!
# Positive level-1 Rudvalis transitions: batches 184–267

This module assembles the checkpoint certificates for all positive-generator-0
batches 184 through 267, covering representatives 920 through 1339.

Source: the ATLAS-derived witnesses documented in `OrderLevel1Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0
open Level1Reduction

/-- The positive-generator-0 transitions for batches 184 through 267. -/
public theorem blockC (b : Fin 84) :
    Level1Reduction.stepBatch 0 ⟨184 + b.val, by omega⟩ := by
  by_cases h12 : b.val < 12
  · exact BlockC.part0 ⟨b.val, h12⟩
  by_cases h24 : b.val < 24
  · have he : 196 + (b.val - 12) = 184 + b.val := by omega
    simpa only [he] using BlockC.part1 ⟨b.val - 12, by omega⟩
  by_cases h30 : b.val < 30
  · have he : 204 + (b.val - 20) = 184 + b.val := by omega
    simpa only [he] using segment204 ⟨b.val - 20, by omega⟩
  by_cases h40 : b.val < 40
  · have he : 214 + (b.val - 30) = 184 + b.val := by omega
    simpa only [he] using segment214 ⟨b.val - 30, by omega⟩
  by_cases h50 : b.val < 50
  · have he : 224 + (b.val - 40) = 184 + b.val := by omega
    simpa only [he] using segment224 ⟨b.val - 40, by omega⟩
  by_cases h60 : b.val < 60
  · have he : 234 + (b.val - 50) = 184 + b.val := by omega
    simpa only [he] using segment234 ⟨b.val - 50, by omega⟩
  by_cases h70 : b.val < 70
  · have he : 244 + (b.val - 60) = 184 + b.val := by omega
    simpa only [he] using segment244 ⟨b.val - 60, by omega⟩
  by_cases h80 : b.val < 80
  · have he : 254 + (b.val - 70) = 184 + b.val := by omega
    simpa only [he] using segment254 ⟨b.val - 70, by omega⟩
  have he : 264 + (b.val - 80) = 184 + b.val := by omega
  simpa only [he] using segment264 ⟨b.val - 80, by omega⟩

end Rudvalis.OrderCertificate.OrderLevel1Positive0
