module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 14.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed2509 : L0Gen 1 * L0Rep 2509 =
    L0Rep (L0Act 1 2509) * evalWord L1Gen (L0Factor 1 2509) := by
  apply step_of_packed_check rawBlock_spec 2509 [38, 40, 40, 38, 40] [1, 14, 13, 13, 19, 51, 64, 67, 52] [packed38, packed40, packed40, packed38, packed40] [packed1, packed14, packed13, packed13, packed19, packed51, packed64, packed67, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2513 : L0Gen 1 * L0Rep 2513 =
    L0Rep (L0Act 1 2513) * evalWord L1Gen (L0Factor 1 2513) := by
  apply step_of_packed_check rawBlock_spec 2513 [40, 40, 46, 38, 40] [2, 1, 2, 1, 5, 67, 64, 67, 67, 55, 48] [packed40, packed40, packed46, packed38, packed40] [packed2, packed1, packed2, packed1, packed5, packed67, packed64, packed67, packed67, packed55, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2515 : L0Gen 1 * L0Rep 2515 =
    L0Rep (L0Act 1 2515) * evalWord L1Gen (L0Factor 1 2515) := by
  apply step_of_packed_check rawBlock_spec 2515 [40, 38, 38, 44, 40] [1, 14, 13, 13, 4, 73, 51, 61, 69] [packed40, packed38, packed38, packed44, packed40] [packed1, packed14, packed13, packed13, packed4, packed73, packed51, packed61, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2518 : L0Gen 1 * L0Rep 2518 =
    L0Rep (L0Act 1 2518) * evalWord L1Gen (L0Factor 1 2518) := by
  apply step_of_packed_check rawBlock_spec 2518 [38, 40, 38, 44, 40] [2, 13, 14, 14, 8, 57, 57, 50, 61, 69] [packed38, packed40, packed38, packed44, packed40] [packed2, packed13, packed14, packed14, packed8, packed57, packed57, packed50, packed61, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2556 : L0Gen 1 * L0Rep 2556 =
    L0Rep (L0Act 1 2556) * evalWord L1Gen (L0Factor 1 2556) := by
  apply step_of_packed_check rawBlock_spec 2556 [38, 38, 38, 38, 46] [1, 1, 1, 2, 15, 67, 61, 54, 64, 63] [packed38, packed38, packed38, packed38, packed46] [packed1, packed1, packed1, packed2, packed15, packed67, packed61, packed54, packed64, packed63]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2564 : L0Gen 1 * L0Rep 2564 =
    L0Rep (L0Act 1 2564) * evalWord L1Gen (L0Factor 1 2564) := by
  apply step_of_packed_check rawBlock_spec 2564 [38, 38, 46, 38, 46] [1, 14, 1, 1, 8, 67, 55, 50, 61] [packed38, packed38, packed46, packed38, packed46] [packed1, packed14, packed1, packed1, packed8, packed67, packed55, packed50, packed61]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2574 : L0Gen 1 * L0Rep 2574 =
    L0Rep (L0Act 1 2574) * evalWord L1Gen (L0Factor 1 2574) := by
  apply step_of_packed_check rawBlock_spec 2574 [40, 40, 44, 44, 46] [13, 13, 13, 1, 19, 72, 63, 57, 69] [packed40, packed40, packed44, packed44, packed46] [packed13, packed13, packed13, packed1, packed19, packed72, packed63, packed57, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2579 : L0Gen 1 * L0Rep 2579 =
    L0Rep (L0Act 1 2579) * evalWord L1Gen (L0Factor 1 2579) := by
  apply step_of_packed_check rawBlock_spec 2579 [40, 38, 46, 44, 46] [14, 13, 14, 14, 15, 64, 67, 67, 55, 49] [packed40, packed38, packed46, packed44, packed46] [packed14, packed13, packed14, packed14, packed15, packed64, packed67, packed67, packed55, packed49]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
