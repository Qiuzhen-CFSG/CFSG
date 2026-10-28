module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 17.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3433 : L0Gen 1 * L0Rep 3433 =
    L0Rep (L0Act 1 3433) * evalWord L1Gen (L0Factor 1 3433) := by
  apply step_of_packed_check rawBlock_spec 3433 [38, 38, 46, 46, 44, 35] [1, 2, 14, 14, 1, 55, 50, 67, 67, 63, 47] [packed38, packed38, packed46, packed46, packed44, packed35] [packed1, packed2, packed14, packed14, packed1, packed55, packed50, packed67, packed67, packed63, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3440 : L0Gen 1 * L0Rep 3440 =
    L0Rep (L0Act 1 3440) * evalWord L1Gen (L0Factor 1 3440) := by
  apply step_of_packed_check rawBlock_spec 3440 [40, 40, 38, 38, 40, 35] [2, 13, 1, 1, 2, 25, 51, 61, 55] [packed40, packed40, packed38, packed38, packed40, packed35] [packed2, packed13, packed1, packed1, packed2, packed25, packed51, packed61, packed55]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3442 : L0Gen 1 * L0Rep 3442 =
    L0Rep (L0Act 1 3442) * evalWord L1Gen (L0Factor 1 3442) := by
  apply step_of_packed_check rawBlock_spec 3442 [40, 38, 40, 38, 40, 35] [2, 2, 14, 2, 2, 57, 57, 55, 75, 57, 56] [packed40, packed38, packed40, packed38, packed40, packed35] [packed2, packed2, packed14, packed2, packed2, packed57, packed57, packed55, packed75, packed57, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3446 : L0Gen 1 * L0Rep 3446 =
    L0Rep (L0Act 1 3446) * evalWord L1Gen (L0Factor 1 3446) := by
  apply step_of_packed_check rawBlock_spec 3446 [40, 38, 46, 38, 40, 35] [1, 13, 14, 2, 1, 29, 67, 64, 65] [packed40, packed38, packed46, packed38, packed40, packed35] [packed1, packed13, packed14, packed2, packed1, packed29, packed67, packed64, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3448 : L0Gen 1 * L0Rep 3448 =
    L0Rep (L0Act 1 3448) * evalWord L1Gen (L0Factor 1 3448) := by
  apply step_of_packed_check rawBlock_spec 3448 [40, 40, 46, 38, 40, 35] [14, 14, 1, 13, 14, 33, 63, 57, 50, 59] [packed40, packed40, packed46, packed38, packed40, packed35] [packed14, packed14, packed1, packed13, packed14, packed33, packed63, packed57, packed50, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3450 : L0Gen 1 * L0Rep 3450 =
    L0Rep (L0Act 1 3450) * evalWord L1Gen (L0Factor 1 3450) := by
  apply step_of_packed_check rawBlock_spec 3450 [38, 38, 44, 40, 40, 35] [2, 1, 14, 13, 13, 50, 67, 61, 47] [packed38, packed38, packed44, packed40, packed40, packed35] [packed2, packed1, packed14, packed13, packed13, packed50, packed67, packed61, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3461 : L0Gen 1 * L0Rep 3461 =
    L0Rep (L0Act 1 3461) * evalWord L1Gen (L0Factor 1 3461) := by
  apply step_of_packed_check rawBlock_spec 3461 [40, 44, 46, 40, 40, 35] [2, 1, 2, 1, 13, 30, 73, 69] [packed40, packed44, packed46, packed40, packed40, packed35] [packed2, packed1, packed2, packed1, packed13, packed30, packed73, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3462 : L0Gen 1 * L0Rep 3462 =
    L0Rep (L0Act 1 3462) * evalWord L1Gen (L0Factor 1 3462) := by
  apply step_of_packed_check rawBlock_spec 3462 [38, 40, 46, 40, 40, 35] [1, 2, 1, 2, 14, 68, 64, 61, 54, 63] [packed38, packed40, packed46, packed40, packed40, packed35] [packed1, packed2, packed1, packed2, packed14, packed68, packed64, packed61, packed54, packed63]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
