module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 19.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3488 : L0Gen 1 * L0Rep 3488 =
    L0Rep (L0Act 1 3488) * evalWord L1Gen (L0Factor 1 3488) := by
  apply step_of_packed_check rawBlock_spec 3488 [38, 40, 44, 46, 46, 35] [14, 2, 14, 2, 1, 31, 54, 67, 57, 51, 59] [packed38, packed40, packed44, packed46, packed46, packed35] [packed14, packed2, packed14, packed2, packed1, packed31, packed54, packed67, packed57, packed51, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3489 : L0Gen 1 * L0Rep 3489 =
    L0Rep (L0Act 1 3489) * evalWord L1Gen (L0Factor 1 3489) := by
  apply step_of_packed_check rawBlock_spec 3489 [38, 38, 40, 46, 46, 35] [14, 14, 1, 14, 14, 67, 66] [packed38, packed38, packed40, packed46, packed46, packed35] [packed14, packed14, packed1, packed14, packed14, packed67, packed66]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3493 : L0Gen 1 * L0Rep 3493 =
    L0Rep (L0Act 1 3493) * evalWord L1Gen (L0Factor 1 3493) := by
  apply step_of_packed_check rawBlock_spec 3493 [40, 40, 40, 46, 46, 35] [2, 13, 13, 13, 14, 24] [packed40, packed40, packed40, packed46, packed46, packed35] [packed2, packed13, packed13, packed13, packed14, packed24]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3494 : L0Gen 1 * L0Rep 3494 =
    L0Rep (L0Act 1 3494) * evalWord L1Gen (L0Factor 1 3494) := by
  apply step_of_packed_check rawBlock_spec 3494 [38, 46, 40, 46, 46, 35] [1, 1, 14, 14, 14, 50, 67, 55, 50, 65] [packed38, packed46, packed40, packed46, packed46, packed35] [packed1, packed1, packed14, packed14, packed14, packed50, packed67, packed55, packed50, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3498 : L0Gen 1 * L0Rep 3498 =
    L0Rep (L0Act 1 3498) * evalWord L1Gen (L0Factor 1 3498) := by
  apply step_of_packed_check rawBlock_spec 3498 [40, 46, 38, 44, 38, 41] [1, 2, 13, 14, 1, 63, 57, 54, 64, 58] [packed40, packed46, packed38, packed44, packed38, packed41] [packed1, packed2, packed13, packed14, packed1, packed63, packed57, packed54, packed64, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3500 : L0Gen 1 * L0Rep 3500 =
    L0Rep (L0Act 1 3500) * evalWord L1Gen (L0Factor 1 3500) := by
  apply step_of_packed_check rawBlock_spec 3500 [38, 44, 44, 44, 38, 41] [1, 14, 13, 1, 2, 31, 57, 73, 56] [packed38, packed44, packed44, packed44, packed38, packed41] [packed1, packed14, packed13, packed1, packed2, packed31, packed57, packed73, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3502 : L0Gen 1 * L0Rep 3502 =
    L0Rep (L0Act 1 3502) * evalWord L1Gen (L0Factor 1 3502) := by
  apply step_of_packed_check rawBlock_spec 3502 [40, 38, 40, 44, 38, 41] [1, 1, 14, 13, 2, 30, 57, 57, 57, 50, 59] [packed40, packed38, packed40, packed44, packed38, packed41] [packed1, packed1, packed14, packed13, packed2, packed30, packed57, packed57, packed57, packed50, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3510 : L0Gen 1 * L0Rep 3510 =
    L0Rep (L0Act 1 3510) * evalWord L1Gen (L0Factor 1 3510) := by
  apply step_of_packed_check rawBlock_spec 3510 [38, 46, 46, 44, 38, 41] [14, 14, 2, 2, 14, 26, 61, 72, 67, 61, 52] [packed38, packed46, packed46, packed44, packed38, packed41] [packed14, packed14, packed2, packed2, packed14, packed26, packed61, packed72, packed67, packed61, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
