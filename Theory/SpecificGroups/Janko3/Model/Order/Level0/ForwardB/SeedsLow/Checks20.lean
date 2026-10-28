module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 20.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3514 : L0Gen 1 * L0Rep 3514 =
    L0Rep (L0Act 1 3514) * evalWord L1Gen (L0Factor 1 3514) := by
  apply step_of_packed_check rawBlock_spec 3514 [40, 46, 46, 40, 38, 41] [13, 1, 2, 13, 13, 26, 67, 67, 63, 47] [packed40, packed46, packed46, packed40, packed38, packed41] [packed13, packed1, packed2, packed13, packed13, packed26, packed67, packed67, packed63, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3515 : L0Gen 1 * L0Rep 3515 =
    L0Rep (L0Act 1 3515) * evalWord L1Gen (L0Factor 1 3515) := by
  apply step_of_packed_check rawBlock_spec 3515 [38, 40, 38, 38, 44, 41] [14, 13, 1, 14, 2, 75, 57, 57, 52] [packed38, packed40, packed38, packed38, packed44, packed41] [packed14, packed13, packed1, packed14, packed2, packed75, packed57, packed57, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3520 : L0Gen 1 * L0Rep 3520 =
    L0Rep (L0Act 1 3520) * evalWord L1Gen (L0Factor 1 3520) := by
  apply step_of_packed_check rawBlock_spec 3520 [40, 44, 44, 38, 44, 41] [14, 13, 2, 14, 2, 50, 61, 72, 59] [packed40, packed44, packed44, packed38, packed44, packed41] [packed14, packed13, packed2, packed14, packed2, packed50, packed61, packed72, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3527 : L0Gen 1 * L0Rep 3527 =
    L0Rep (L0Act 1 3527) * evalWord L1Gen (L0Factor 1 3527) := by
  apply step_of_packed_check rawBlock_spec 3527 [38, 38, 38, 44, 44, 41] [1, 2, 1, 2, 2, 67, 67, 67, 59] [packed38, packed38, packed38, packed44, packed44, packed41] [packed1, packed2, packed1, packed2, packed2, packed67, packed67, packed67, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3531 : L0Gen 1 * L0Rep 3531 =
    L0Rep (L0Act 1 3531) * evalWord L1Gen (L0Factor 1 3531) := by
  apply step_of_packed_check rawBlock_spec 3531 [38, 46, 38, 44, 44, 41] [13, 14, 1, 1, 14, 30, 51, 63] [packed38, packed46, packed38, packed44, packed44, packed41] [packed13, packed14, packed1, packed1, packed14, packed30, packed51, packed63]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3537 : L0Gen 1 * L0Rep 3537 =
    L0Rep (L0Act 1 3537) * evalWord L1Gen (L0Factor 1 3537) := by
  apply step_of_packed_check rawBlock_spec 3537 [40, 46, 40, 44, 44, 41] [13, 1, 13, 2, 13, 30, 50, 67, 67, 62] [packed40, packed46, packed40, packed44, packed44, packed41] [packed13, packed1, packed13, packed2, packed13, packed30, packed50, packed67, packed67, packed62]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3539 : L0Gen 1 * L0Rep 3539 =
    L0Rep (L0Act 1 3539) * evalWord L1Gen (L0Factor 1 3539) := by
  apply step_of_packed_check rawBlock_spec 3539 [38, 44, 46, 44, 44, 41] [13, 1, 14, 13, 14, 57, 51, 61, 73, 70] [packed38, packed44, packed46, packed44, packed44, packed41] [packed13, packed1, packed14, packed13, packed14, packed57, packed51, packed61, packed73, packed70]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3542 : L0Gen 1 * L0Rep 3542 =
    L0Rep (L0Act 1 3542) * evalWord L1Gen (L0Factor 1 3542) := by
  apply step_of_packed_check rawBlock_spec 3542 [40, 40, 46, 44, 44, 41] [14, 1, 13, 14, 13, 26, 55, 73, 73, 53] [packed40, packed40, packed46, packed44, packed44, packed41] [packed14, packed1, packed13, packed14, packed13, packed26, packed55, packed73, packed73, packed53]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
