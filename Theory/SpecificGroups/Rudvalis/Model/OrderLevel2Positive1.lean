module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block5
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block6
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block7
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block8
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block9
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block10
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block11
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block12
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block13
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block14
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1Block15

/-!
# Rudvalis level-2 positive generator 1 transitions

The 1024 transitions are certified in 256 batches of four representatives.
The supporting modules check these in sixteen ranges. Each batch uses free
word cancellation where possible and otherwise checks all 4060 permutation
points in Lean's kernel. The batch assembly covers every representative.

Source: the ATLAS degree-4060 witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive1
open Level2Reduction Theory.GroupTheory

private theorem batches (b : Fin 256) : stepBatch 1 b := by
  by_cases h16 : b.val < 16
  · have he : 0 + (b.val - 0) = b.val := by omega
    simpa only [he] using block0 ⟨b.val - 0, by omega⟩
  by_cases h32 : b.val < 32
  · have he : 16 + (b.val - 16) = b.val := by omega
    simpa only [he] using block1 ⟨b.val - 16, by omega⟩
  by_cases h48 : b.val < 48
  · have he : 32 + (b.val - 32) = b.val := by omega
    simpa only [he] using block2 ⟨b.val - 32, by omega⟩
  by_cases h64 : b.val < 64
  · have he : 48 + (b.val - 48) = b.val := by omega
    simpa only [he] using block3 ⟨b.val - 48, by omega⟩
  by_cases h80 : b.val < 80
  · have he : 64 + (b.val - 64) = b.val := by omega
    simpa only [he] using block4 ⟨b.val - 64, by omega⟩
  by_cases h96 : b.val < 96
  · have he : 80 + (b.val - 80) = b.val := by omega
    simpa only [he] using block5 ⟨b.val - 80, by omega⟩
  by_cases h112 : b.val < 112
  · have he : 96 + (b.val - 96) = b.val := by omega
    simpa only [he] using block6 ⟨b.val - 96, by omega⟩
  by_cases h128 : b.val < 128
  · have he : 112 + (b.val - 112) = b.val := by omega
    simpa only [he] using block7 ⟨b.val - 112, by omega⟩
  by_cases h144 : b.val < 144
  · have he : 128 + (b.val - 128) = b.val := by omega
    simpa only [he] using block8 ⟨b.val - 128, by omega⟩
  by_cases h160 : b.val < 160
  · have he : 144 + (b.val - 144) = b.val := by omega
    simpa only [he] using block9 ⟨b.val - 144, by omega⟩
  by_cases h176 : b.val < 176
  · have he : 160 + (b.val - 160) = b.val := by omega
    simpa only [he] using block10 ⟨b.val - 160, by omega⟩
  by_cases h192 : b.val < 192
  · have he : 176 + (b.val - 176) = b.val := by omega
    simpa only [he] using block11 ⟨b.val - 176, by omega⟩
  by_cases h208 : b.val < 208
  · have he : 192 + (b.val - 192) = b.val := by omega
    simpa only [he] using block12 ⟨b.val - 192, by omega⟩
  by_cases h224 : b.val < 224
  · have he : 208 + (b.val - 208) = b.val := by omega
    simpa only [he] using block13 ⟨b.val - 208, by omega⟩
  by_cases h240 : b.val < 240
  · have he : 224 + (b.val - 224) = b.val := by omega
    simpa only [he] using block14 ⟨b.val - 224, by omega⟩
  · have he : 240 + (b.val - 240) = b.val := by omega
    simpa only [he] using block15 ⟨b.val - 240, by omega⟩

/-- The second forward generator satisfies every level-2 transition. -/
public theorem positiveStep (r : Fin 1024) :
    L2Gen 1 * L2Rep r = L2Rep (L2Act 1 r) * evalWord L3Gen (L2Factor 1 r) := by
  exact positiveStep_of_batches 1 batches r

end Rudvalis.OrderCertificate.OrderLevel2Positive1
