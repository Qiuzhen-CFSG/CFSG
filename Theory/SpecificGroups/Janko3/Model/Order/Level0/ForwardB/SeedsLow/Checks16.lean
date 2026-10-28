module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 16.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3390 : L0Gen 1 * L0Rep 3390 =
    L0Rep (L0Act 1 3390) * evalWord L1Gen (L0Factor 1 3390) := by
  apply step_of_packed_check rawBlock_spec 3390 [38, 38, 40, 46, 38, 35] [2, 13, 2, 1, 2, 57, 51, 64, 67] [packed38, packed38, packed40, packed46, packed38, packed35] [packed2, packed13, packed2, packed1, packed2, packed57, packed51, packed64, packed67]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3391 : L0Gen 1 * L0Rep 3391 =
    L0Rep (L0Act 1 3391) * evalWord L1Gen (L0Factor 1 3391) := by
  apply step_of_packed_check rawBlock_spec 3391 [38, 44, 40, 46, 38, 35] [1, 1, 2, 14, 2, 33, 61, 57, 57, 55, 69] [packed38, packed44, packed40, packed46, packed38, packed35] [packed1, packed1, packed2, packed14, packed2, packed33, packed61, packed57, packed57, packed55, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3395 : L0Gen 1 * L0Rep 3395 =
    L0Rep (L0Act 1 3395) * evalWord L1Gen (L0Factor 1 3395) := by
  apply step_of_packed_check rawBlock_spec 3395 [38, 40, 46, 46, 38, 35] [1, 14, 14, 13, 1, 67, 67, 67, 53] [packed38, packed40, packed46, packed46, packed38, packed35] [packed1, packed14, packed14, packed13, packed1, packed67, packed67, packed67, packed53]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3398 : L0Gen 1 * L0Rep 3398 =
    L0Rep (L0Act 1 3398) * evalWord L1Gen (L0Factor 1 3398) := by
  apply step_of_packed_check rawBlock_spec 3398 [40, 44, 38, 38, 44, 35] [1, 14, 14, 13, 1, 27, 64, 64, 63, 52] [packed40, packed44, packed38, packed38, packed44, packed35] [packed1, packed14, packed14, packed13, packed1, packed27, packed64, packed64, packed63, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3399 : L0Gen 1 * L0Rep 3399 =
    L0Rep (L0Act 1 3399) * evalWord L1Gen (L0Factor 1 3399) := by
  apply step_of_packed_check rawBlock_spec 3399 [38, 46, 38, 38, 44, 35] [13, 14, 2, 1, 13, 31, 57, 54, 67, 47] [packed38, packed46, packed38, packed38, packed44, packed35] [packed13, packed14, packed2, packed1, packed13, packed31, packed57, packed54, packed67, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3401 : L0Gen 1 * L0Rep 3401 =
    L0Rep (L0Act 1 3401) * evalWord L1Gen (L0Factor 1 3401) := by
  apply step_of_packed_check rawBlock_spec 3401 [40, 40, 44, 38, 44, 35] [13, 14, 1, 2, 1, 73, 75, 56] [packed40, packed40, packed44, packed38, packed44, packed35] [packed13, packed14, packed1, packed2, packed1, packed73, packed75, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3417 : L0Gen 1 * L0Rep 3417 =
    L0Rep (L0Act 1 3417) * evalWord L1Gen (L0Factor 1 3417) := by
  apply step_of_packed_check rawBlock_spec 3417 [40, 38, 40, 40, 44, 35] [13, 2, 2, 2, 13, 63, 57, 50, 61, 47] [packed40, packed38, packed40, packed40, packed44, packed35] [packed13, packed2, packed2, packed2, packed13, packed63, packed57, packed50, packed61, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3421 : L0Gen 1 * L0Rep 3421 =
    L0Rep (L0Act 1 3421) * evalWord L1Gen (L0Factor 1 3421) := by
  apply step_of_packed_check rawBlock_spec 3421 [38, 38, 38, 46, 44, 35] [14, 2, 13, 14, 2, 72, 67, 61, 54, 60] [packed38, packed38, packed38, packed46, packed44, packed35] [packed14, packed2, packed13, packed14, packed2, packed72, packed67, packed61, packed54, packed60]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
