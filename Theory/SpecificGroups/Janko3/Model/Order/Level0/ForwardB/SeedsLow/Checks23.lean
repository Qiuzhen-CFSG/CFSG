module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 23.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3630 : L0Gen 1 * L0Rep 3630 =
    L0Rep (L0Act 1 3630) * evalWord L1Gen (L0Factor 1 3630) := by
  apply step_of_packed_check rawBlock_spec 3630 [40, 44, 38, 40, 38, 36] [2, 1, 2, 14, 13, 25, 73, 51, 61, 57] [packed40, packed44, packed38, packed40, packed38, packed36] [packed2, packed1, packed2, packed14, packed13, packed25, packed73, packed51, packed61, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3635 : L0Gen 1 * L0Rep 3635 =
    L0Rep (L0Act 1 3635) * evalWord L1Gen (L0Factor 1 3635) := by
  apply step_of_packed_check rawBlock_spec 3635 [40, 44, 44, 40, 38, 36] [1, 14, 13, 13, 2, 61, 73, 73, 50, 67, 58] [packed40, packed44, packed44, packed40, packed38, packed36] [packed1, packed14, packed13, packed13, packed2, packed61, packed73, packed73, packed50, packed67, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3643 : L0Gen 1 * L0Rep 3643 =
    L0Rep (L0Act 1 3643) * evalWord L1Gen (L0Factor 1 3643) := by
  apply step_of_packed_check rawBlock_spec 3643 [38, 46, 38, 46, 38, 36] [2, 13, 2, 13, 1, 30, 50, 67, 56] [packed38, packed46, packed38, packed46, packed38, packed36] [packed2, packed13, packed2, packed13, packed1, packed30, packed50, packed67, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3653 : L0Gen 1 * L0Rep 3653 =
    L0Rep (L0Act 1 3653) * evalWord L1Gen (L0Factor 1 3653) := by
  apply step_of_packed_check rawBlock_spec 3653 [38, 44, 38, 38, 44, 36] [1, 13, 14, 14, 14, 55, 75, 50, 47] [packed38, packed44, packed38, packed38, packed44, packed36] [packed1, packed13, packed14, packed14, packed14, packed55, packed75, packed50, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3666 : L0Gen 1 * L0Rep 3666 =
    L0Rep (L0Act 1 3666) * evalWord L1Gen (L0Factor 1 3666) := by
  apply step_of_packed_check rawBlock_spec 3666 [38, 46, 44, 44, 44, 36] [14, 14, 14, 13, 1, 61, 57, 54, 67, 58] [packed38, packed46, packed44, packed44, packed44, packed36] [packed14, packed14, packed14, packed13, packed1, packed61, packed57, packed54, packed67, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3673 : L0Gen 1 * L0Rep 3673 =
    L0Rep (L0Act 1 3673) * evalWord L1Gen (L0Factor 1 3673) := by
  apply step_of_packed_check rawBlock_spec 3673 [38, 38, 46, 44, 44, 36] [14, 13, 13, 1, 1, 67, 67, 57, 50, 67] [packed38, packed38, packed46, packed44, packed44, packed36] [packed14, packed13, packed13, packed1, packed1, packed67, packed67, packed57, packed50, packed67]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3681 : L0Gen 1 * L0Rep 3681 =
    L0Rep (L0Act 1 3681) * evalWord L1Gen (L0Factor 1 3681) := by
  apply step_of_packed_check rawBlock_spec 3681 [38, 40, 38, 46, 44, 36] [1, 14, 13, 2, 13, 50, 55, 50, 67, 67] [packed38, packed40, packed38, packed46, packed44, packed36] [packed1, packed14, packed13, packed2, packed13, packed50, packed55, packed50, packed67, packed67]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3683 : L0Gen 1 * L0Rep 3683 =
    L0Rep (L0Act 1 3683) * evalWord L1Gen (L0Factor 1 3683) := by
  apply step_of_packed_check rawBlock_spec 3683 [40, 46, 38, 46, 44, 36] [1, 2, 1, 14, 1, 33, 57, 50, 67, 62] [packed40, packed46, packed38, packed46, packed44, packed36] [packed1, packed2, packed1, packed14, packed1, packed33, packed57, packed50, packed67, packed62]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
