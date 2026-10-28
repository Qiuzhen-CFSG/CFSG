module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 27.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3802 : L0Gen 1 * L0Rep 3802 =
    L0Rep (L0Act 1 3802) * evalWord L1Gen (L0Factor 1 3802) := by
  apply step_of_packed_check rawBlock_spec 3802 [40, 40, 40, 40, 38, 42] [2, 2, 2, 2, 14, 0] [packed40, packed40, packed40, packed40, packed38, packed42] [packed2, packed2, packed2, packed2, packed14, packed0]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3805 : L0Gen 1 * L0Rep 3805 =
    L0Rep (L0Act 1 3805) * evalWord L1Gen (L0Factor 1 3805) := by
  apply step_of_packed_check rawBlock_spec 3805 [38, 44, 46, 40, 38, 42] [1, 13, 14, 14, 1, 51, 61, 54, 67, 56] [packed38, packed44, packed46, packed40, packed38, packed42] [packed1, packed13, packed14, packed14, packed1, packed51, packed61, packed54, packed67, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3812 : L0Gen 1 * L0Rep 3812 =
    L0Rep (L0Act 1 3812) * evalWord L1Gen (L0Factor 1 3812) := by
  apply step_of_packed_check rawBlock_spec 3812 [40, 46, 38, 46, 38, 42] [1, 14, 2, 2, 14, 34, 61, 73, 73, 73] [packed40, packed46, packed38, packed46, packed38, packed42] [packed1, packed14, packed2, packed2, packed14, packed34, packed61, packed73, packed73, packed73]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3814 : L0Gen 1 * L0Rep 3814 =
    L0Rep (L0Act 1 3814) * evalWord L1Gen (L0Factor 1 3814) := by
  apply step_of_packed_check rawBlock_spec 3814 [40, 38, 40, 46, 38, 42] [13, 1, 13, 13, 2, 26, 57, 50, 61, 57, 49] [packed40, packed38, packed40, packed46, packed38, packed42] [packed13, packed1, packed13, packed13, packed2, packed26, packed57, packed50, packed61, packed57, packed49]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3818 : L0Gen 1 * L0Rep 3818 =
    L0Rep (L0Act 1 3818) * evalWord L1Gen (L0Factor 1 3818) := by
  apply step_of_packed_check rawBlock_spec 3818 [40, 38, 46, 46, 38, 42] [2, 2, 13, 14, 13, 27, 67, 63, 55, 50, 47] [packed40, packed38, packed46, packed46, packed38, packed42] [packed2, packed2, packed13, packed14, packed13, packed27, packed67, packed63, packed55, packed50, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3820 : L0Gen 1 * L0Rep 3820 =
    L0Rep (L0Act 1 3820) * evalWord L1Gen (L0Factor 1 3820) := by
  apply step_of_packed_check rawBlock_spec 3820 [38, 40, 44, 38, 44, 42] [14, 14, 14, 2, 1, 68, 63, 67, 58] [packed38, packed40, packed44, packed38, packed44, packed42] [packed14, packed14, packed14, packed2, packed1, packed68, packed63, packed67, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3823 : L0Gen 1 * L0Rep 3823 =
    L0Rep (L0Act 1 3823) * evalWord L1Gen (L0Factor 1 3823) := by
  apply step_of_packed_check rawBlock_spec 3823 [40, 46, 44, 38, 44, 42] [13, 1, 2, 14, 1, 31, 54, 64, 63, 58] [packed40, packed46, packed44, packed38, packed44, packed42] [packed13, packed1, packed2, packed14, packed1, packed31, packed54, packed64, packed63, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3835 : L0Gen 1 * L0Rep 3835 =
    L0Rep (L0Act 1 3835) * evalWord L1Gen (L0Factor 1 3835) := by
  apply step_of_packed_check rawBlock_spec 3835 [38, 44, 44, 46, 44, 42] [2, 14, 1, 13, 1, 25, 72, 64, 63, 55, 52] [packed38, packed44, packed44, packed46, packed44, packed42] [packed2, packed14, packed1, packed13, packed1, packed25, packed72, packed64, packed63, packed55, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
