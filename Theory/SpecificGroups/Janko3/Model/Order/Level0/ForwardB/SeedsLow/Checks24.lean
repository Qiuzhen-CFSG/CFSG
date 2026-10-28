module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 24.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3690 : L0Gen 1 * L0Rep 3690 =
    L0Rep (L0Act 1 3690) * evalWord L1Gen (L0Factor 1 3690) := by
  apply step_of_packed_check rawBlock_spec 3690 [40, 38, 44, 38, 40, 36] [1, 2, 13, 14, 14, 64, 61, 73, 51] [packed40, packed38, packed44, packed38, packed40, packed36] [packed1, packed2, packed13, packed14, packed14, packed64, packed61, packed73, packed51]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3693 : L0Gen 1 * L0Rep 3693 =
    L0Rep (L0Act 1 3693) * evalWord L1Gen (L0Factor 1 3693) := by
  apply step_of_packed_check rawBlock_spec 3693 [38, 46, 44, 38, 40, 36] [14, 14, 1, 14, 13, 29, 64, 61, 74] [packed38, packed46, packed44, packed38, packed40, packed36] [packed14, packed14, packed1, packed14, packed13, packed29, packed64, packed61, packed74]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3704 : L0Gen 1 * L0Rep 3704 =
    L0Rep (L0Act 1 3704) * evalWord L1Gen (L0Factor 1 3704) := by
  apply step_of_packed_check rawBlock_spec 3704 [38, 40, 44, 44, 40, 36] [2, 14, 14, 14, 2, 67, 67, 68, 63, 66] [packed38, packed40, packed44, packed44, packed40, packed36] [packed2, packed14, packed14, packed14, packed2, packed67, packed67, packed68, packed63, packed66]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3709 : L0Gen 1 * L0Rep 3709 =
    L0Rep (L0Act 1 3709) * evalWord L1Gen (L0Factor 1 3709) := by
  apply step_of_packed_check rawBlock_spec 3709 [38, 40, 46, 44, 40, 36] [13, 1, 1, 2, 13, 30, 50, 67, 67, 62] [packed38, packed40, packed46, packed44, packed40, packed36] [packed13, packed1, packed1, packed2, packed13, packed30, packed50, packed67, packed67, packed62]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3711 : L0Gen 1 * L0Rep 3711 =
    L0Rep (L0Act 1 3711) * evalWord L1Gen (L0Factor 1 3711) := by
  apply step_of_packed_check rawBlock_spec 3711 [40, 44, 38, 40, 40, 36] [1, 1, 13, 13, 13, 57, 57, 57, 57, 50, 60] [packed40, packed44, packed38, packed40, packed40, packed36] [packed1, packed1, packed13, packed13, packed13, packed57, packed57, packed57, packed57, packed50, packed60]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3712 : L0Gen 1 * L0Rep 3712 =
    L0Rep (L0Act 1 3712) * evalWord L1Gen (L0Factor 1 3712) := by
  apply step_of_packed_check rawBlock_spec 3712 [40, 46, 44, 40, 40, 36] [14, 2, 2, 14, 13, 75, 51, 63, 56] [packed40, packed46, packed44, packed40, packed40, packed36] [packed14, packed2, packed2, packed14, packed13, packed75, packed51, packed63, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3717 : L0Gen 1 * L0Rep 3717 =
    L0Rep (L0Act 1 3717) * evalWord L1Gen (L0Factor 1 3717) := by
  apply step_of_packed_check rawBlock_spec 3717 [40, 46, 40, 40, 40, 36] [2, 14, 1, 2, 2, 34, 64, 63] [packed40, packed46, packed40, packed40, packed40, packed36] [packed2, packed14, packed1, packed2, packed2, packed34, packed64, packed63]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3727 : L0Gen 1 * L0Rep 3727 =
    L0Rep (L0Act 1 3727) * evalWord L1Gen (L0Factor 1 3727) := by
  apply step_of_packed_check rawBlock_spec 3727 [38, 38, 44, 46, 40, 36] [14, 14, 14, 1, 2, 31, 54, 63, 57, 49] [packed38, packed38, packed44, packed46, packed40, packed36] [packed14, packed14, packed14, packed1, packed2, packed31, packed54, packed63, packed57, packed49]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
