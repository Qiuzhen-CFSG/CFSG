module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 18.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3463 : L0Gen 1 * L0Rep 3463 =
    L0Rep (L0Act 1 3463) * evalWord L1Gen (L0Factor 1 3463) := by
  apply step_of_packed_check rawBlock_spec 3463 [38, 46, 46, 40, 40, 35] [1, 14, 1, 1, 14, 31, 57, 73, 57, 56] [packed38, packed46, packed46, packed40, packed40, packed35] [packed1, packed14, packed1, packed1, packed14, packed31, packed57, packed73, packed57, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3473 : L0Gen 1 * L0Rep 3473 =
    L0Rep (L0Act 1 3473) * evalWord L1Gen (L0Factor 1 3473) := by
  apply step_of_packed_check rawBlock_spec 3473 [38, 38, 44, 44, 46, 35] [14, 1, 14, 14, 2, 34, 63, 61, 54, 65] [packed38, packed38, packed44, packed44, packed46, packed35] [packed14, packed1, packed14, packed14, packed2, packed34, packed63, packed61, packed54, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3477 : L0Gen 1 * L0Rep 3477 =
    L0Rep (L0Act 1 3477) * evalWord L1Gen (L0Factor 1 3477) := by
  apply step_of_packed_check rawBlock_spec 3477 [38, 40, 38, 40, 46, 35] [14, 13, 1, 2, 13, 33, 67, 67, 57, 56] [packed38, packed40, packed38, packed40, packed46, packed35] [packed14, packed13, packed1, packed2, packed13, packed33, packed67, packed67, packed57, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3479 : L0Gen 1 * L0Rep 3479 =
    L0Rep (L0Act 1 3479) * evalWord L1Gen (L0Factor 1 3479) := by
  apply step_of_packed_check rawBlock_spec 3479 [40, 38, 44, 40, 46, 35] [14, 1, 13, 14, 13, 50, 61, 72, 63, 57, 47] [packed40, packed38, packed44, packed40, packed46, packed35] [packed14, packed1, packed13, packed14, packed13, packed50, packed61, packed72, packed63, packed57, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3480 : L0Gen 1 * L0Rep 3480 =
    L0Rep (L0Act 1 3480) * evalWord L1Gen (L0Factor 1 3480) := by
  apply step_of_packed_check rawBlock_spec 3480 [38, 44, 44, 40, 46, 35] [13, 13, 14, 14, 14, 31, 51, 61, 47] [packed38, packed44, packed44, packed40, packed46, packed35] [packed13, packed13, packed14, packed14, packed14, packed31, packed51, packed61, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3481 : L0Gen 1 * L0Rep 3481 =
    L0Rep (L0Act 1 3481) * evalWord L1Gen (L0Factor 1 3481) := by
  apply step_of_packed_check rawBlock_spec 3481 [38, 40, 44, 40, 46, 35] [1, 14, 1, 14, 13, 57, 72, 64, 63, 65] [packed38, packed40, packed44, packed40, packed46, packed35] [packed1, packed14, packed1, packed14, packed13, packed57, packed72, packed64, packed63, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3485 : L0Gen 1 * L0Rep 3485 =
    L0Rep (L0Act 1 3485) * evalWord L1Gen (L0Factor 1 3485) := by
  apply step_of_packed_check rawBlock_spec 3485 [40, 44, 46, 40, 46, 35] [13, 14, 13, 1, 2, 31, 73, 73, 73, 73, 56] [packed40, packed44, packed46, packed40, packed46, packed35] [packed13, packed14, packed13, packed1, packed2, packed31, packed73, packed73, packed73, packed73, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3487 : L0Gen 1 * L0Rep 3487 =
    L0Rep (L0Act 1 3487) * evalWord L1Gen (L0Factor 1 3487) := by
  apply step_of_packed_check rawBlock_spec 3487 [40, 44, 44, 46, 46, 35] [14, 14, 13, 13, 2, 31, 50, 61, 54, 66] [packed40, packed44, packed44, packed46, packed46, packed35] [packed14, packed14, packed13, packed13, packed2, packed31, packed50, packed61, packed54, packed66]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
