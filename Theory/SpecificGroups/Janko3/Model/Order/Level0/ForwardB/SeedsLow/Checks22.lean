module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 22.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3571 : L0Gen 1 * L0Rep 3571 =
    L0Rep (L0Act 1 3571) * evalWord L1Gen (L0Factor 1 3571) := by
  apply step_of_packed_check rawBlock_spec 3571 [38, 44, 40, 40, 40, 41] [2, 2, 2, 1, 1, 67, 67, 67, 57, 50, 47] [packed38, packed44, packed40, packed40, packed40, packed41] [packed2, packed2, packed2, packed1, packed1, packed67, packed67, packed67, packed57, packed50, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3589 : L0Gen 1 * L0Rep 3589 =
    L0Rep (L0Act 1 3589) * evalWord L1Gen (L0Factor 1 3589) := by
  apply step_of_packed_check rawBlock_spec 3589 [40, 40, 40, 44, 46, 41] [14, 2, 2, 14, 1, 61, 72, 67, 57, 49] [packed40, packed40, packed40, packed44, packed46, packed41] [packed14, packed2, packed2, packed14, packed1, packed61, packed72, packed67, packed57, packed49]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3598 : L0Gen 1 * L0Rep 3598 =
    L0Rep (L0Act 1 3598) * evalWord L1Gen (L0Factor 1 3598) := by
  apply step_of_packed_check rawBlock_spec 3598 [40, 38, 44, 40, 46, 41] [13, 1, 13, 13, 13, 31, 73, 72, 64, 63] [packed40, packed38, packed44, packed40, packed46, packed41] [packed13, packed1, packed13, packed13, packed13, packed31, packed73, packed72, packed64, packed63]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3601 : L0Gen 1 * L0Rep 3601 =
    L0Rep (L0Act 1 3601) * evalWord L1Gen (L0Factor 1 3601) := by
  apply step_of_packed_check rawBlock_spec 3601 [38, 46, 44, 40, 46, 41] [2, 13, 14, 14, 13, 51, 64, 64, 67, 62] [packed38, packed46, packed44, packed40, packed46, packed41] [packed2, packed13, packed14, packed14, packed13, packed51, packed64, packed64, packed67, packed62]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3610 : L0Gen 1 * L0Rep 3610 =
    L0Rep (L0Act 1 3610) * evalWord L1Gen (L0Factor 1 3610) := by
  apply step_of_packed_check rawBlock_spec 3610 [38, 44, 40, 46, 46, 41] [2, 14, 14, 2, 2, 30, 51, 61, 73, 73, 48] [packed38, packed44, packed40, packed46, packed46, packed41] [packed2, packed14, packed14, packed2, packed2, packed30, packed51, packed61, packed73, packed73, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3611 : L0Gen 1 * L0Rep 3611 =
    L0Rep (L0Act 1 3611) * evalWord L1Gen (L0Factor 1 3611) := by
  apply step_of_packed_check rawBlock_spec 3611 [40, 44, 40, 46, 46, 41] [1, 13, 14, 1, 14, 33, 61, 73, 50, 60] [packed40, packed44, packed40, packed46, packed46, packed41] [packed1, packed13, packed14, packed1, packed14, packed33, packed61, packed73, packed50, packed60]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3619 : L0Gen 1 * L0Rep 3619 =
    L0Rep (L0Act 1 3619) * evalWord L1Gen (L0Factor 1 3619) := by
  apply step_of_packed_check rawBlock_spec 3619 [40, 40, 46, 46, 46, 41] [14, 1, 2, 14, 1, 67, 57, 50, 61, 52] [packed40, packed40, packed46, packed46, packed46, packed41] [packed14, packed1, packed2, packed14, packed1, packed67, packed57, packed50, packed61, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3629 : L0Gen 1 * L0Rep 3629 =
    L0Rep (L0Act 1 3629) * evalWord L1Gen (L0Factor 1 3629) := by
  apply step_of_packed_check rawBlock_spec 3629 [38, 44, 38, 40, 38, 36] [14, 2, 1, 2, 1, 26, 67, 67, 67, 53] [packed38, packed44, packed38, packed40, packed38, packed36] [packed14, packed2, packed1, packed2, packed1, packed26, packed67, packed67, packed67, packed53]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
