module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 21.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3551 : L0Gen 1 * L0Rep 3551 =
    L0Rep (L0Act 1 3551) * evalWord L1Gen (L0Factor 1 3551) := by
  apply step_of_packed_check rawBlock_spec 3551 [40, 40, 46, 40, 44, 41] [14, 1, 14, 13, 14, 50, 67, 55, 51, 64, 59] [packed40, packed40, packed46, packed40, packed44, packed41] [packed14, packed1, packed14, packed13, packed14, packed50, packed67, packed55, packed51, packed64, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3554 : L0Gen 1 * L0Rep 3554 =
    L0Rep (L0Act 1 3554) * evalWord L1Gen (L0Factor 1 3554) := by
  apply step_of_packed_check rawBlock_spec 3554 [40, 46, 38, 46, 44, 41] [1, 1, 1, 14, 13, 30, 57, 57, 55, 75, 48] [packed40, packed46, packed38, packed46, packed44, packed41] [packed1, packed1, packed1, packed14, packed13, packed30, packed57, packed57, packed55, packed75, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3557 : L0Gen 1 * L0Rep 3557 =
    L0Rep (L0Act 1 3557) * evalWord L1Gen (L0Factor 1 3557) := by
  apply step_of_packed_check rawBlock_spec 3557 [40, 38, 46, 46, 44, 41] [14, 1, 2, 13, 1, 33, 64, 67, 67, 55, 52] [packed40, packed38, packed46, packed46, packed44, packed41] [packed14, packed1, packed2, packed13, packed1, packed33, packed64, packed67, packed67, packed55, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3559 : L0Gen 1 * L0Rep 3559 =
    L0Rep (L0Act 1 3559) * evalWord L1Gen (L0Factor 1 3559) := by
  apply step_of_packed_check rawBlock_spec 3559 [40, 44, 46, 46, 44, 41] [2, 13, 14, 1, 2, 54, 63, 55, 73, 69] [packed40, packed44, packed46, packed46, packed44, packed41] [packed2, packed13, packed14, packed1, packed2, packed54, packed63, packed55, packed73, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3563 : L0Gen 1 * L0Rep 3563 =
    L0Rep (L0Act 1 3563) * evalWord L1Gen (L0Factor 1 3563) := by
  apply step_of_packed_check rawBlock_spec 3563 [40, 44, 44, 44, 40, 41] [13, 13, 2, 1, 1, 34, 61, 54, 64] [packed40, packed44, packed44, packed44, packed40, packed41] [packed13, packed13, packed2, packed1, packed1, packed34, packed61, packed54, packed64]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3565 : L0Gen 1 * L0Rep 3565 =
    L0Rep (L0Act 1 3565) * evalWord L1Gen (L0Factor 1 3565) := by
  apply step_of_packed_check rawBlock_spec 3565 [38, 38, 38, 40, 40, 41] [14, 14, 14, 1, 1, 51, 61, 54, 67, 57] [packed38, packed38, packed38, packed40, packed40, packed41] [packed14, packed14, packed14, packed1, packed1, packed51, packed61, packed54, packed67, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3567 : L0Gen 1 * L0Rep 3567 =
    L0Rep (L0Act 1 3567) * evalWord L1Gen (L0Factor 1 3567) := by
  apply step_of_packed_check rawBlock_spec 3567 [40, 40, 38, 40, 40, 41] [14, 1, 2, 13, 13, 31, 57, 51, 63, 55, 47] [packed40, packed40, packed38, packed40, packed40, packed41] [packed14, packed1, packed2, packed13, packed13, packed31, packed57, packed51, packed63, packed55, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3570 : L0Gen 1 * L0Rep 3570 =
    L0Rep (L0Act 1 3570) * evalWord L1Gen (L0Factor 1 3570) := by
  apply step_of_packed_check rawBlock_spec 3570 [38, 38, 40, 40, 40, 41] [2, 2, 2, 1, 14, 67, 57, 57, 50, 61] [packed38, packed38, packed40, packed40, packed40, packed41] [packed2, packed2, packed2, packed1, packed14, packed67, packed57, packed57, packed50, packed61]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
