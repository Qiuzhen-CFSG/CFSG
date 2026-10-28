module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 26.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3772 : L0Gen 1 * L0Rep 3772 =
    L0Rep (L0Act 1 3772) * evalWord L1Gen (L0Factor 1 3772) := by
  apply step_of_packed_check rawBlock_spec 3772 [38, 38, 40, 46, 46, 36] [13, 2, 2, 13, 14, 33, 64, 67, 64, 59] [packed38, packed38, packed40, packed46, packed46, packed36] [packed13, packed2, packed2, packed13, packed14, packed33, packed64, packed67, packed64, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3778 : L0Gen 1 * L0Rep 3778 =
    L0Rep (L0Act 1 3778) * evalWord L1Gen (L0Factor 1 3778) := by
  apply step_of_packed_check rawBlock_spec 3778 [40, 46, 38, 38, 38, 42] [2, 13, 13, 1, 13, 75, 57, 51, 63, 57] [packed40, packed46, packed38, packed38, packed38, packed42] [packed2, packed13, packed13, packed1, packed13, packed75, packed57, packed51, packed63, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3780 : L0Gen 1 * L0Rep 3780 =
    L0Rep (L0Act 1 3780) * evalWord L1Gen (L0Factor 1 3780) := by
  apply step_of_packed_check rawBlock_spec 3780 [38, 38, 46, 38, 38, 42] [1, 14, 14, 14, 1, 72, 67, 67, 65] [packed38, packed38, packed46, packed38, packed38, packed42] [packed1, packed14, packed14, packed14, packed1, packed72, packed67, packed67, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3788 : L0Gen 1 * L0Rep 3788 =
    L0Rep (L0Act 1 3788) * evalWord L1Gen (L0Factor 1 3788) := by
  apply step_of_packed_check rawBlock_spec 3788 [38, 38, 46, 44, 38, 42] [1, 1, 2, 13, 1, 64, 67, 64] [packed38, packed38, packed46, packed44, packed38, packed42] [packed1, packed1, packed2, packed13, packed1, packed64, packed67, packed64]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3789 : L0Gen 1 * L0Rep 3789 =
    L0Rep (L0Act 1 3789) * evalWord L1Gen (L0Factor 1 3789) := by
  apply step_of_packed_check rawBlock_spec 3789 [40, 38, 46, 44, 38, 42] [2, 14, 13, 1, 1, 61, 73, 51, 61, 52] [packed40, packed38, packed46, packed44, packed38, packed42] [packed2, packed14, packed13, packed1, packed1, packed61, packed73, packed51, packed61, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3792 : L0Gen 1 * L0Rep 3792 =
    L0Rep (L0Act 1 3792) * evalWord L1Gen (L0Factor 1 3792) := by
  apply step_of_packed_check rawBlock_spec 3792 [38, 40, 38, 40, 38, 42] [14, 2, 2, 13, 14, 33, 55, 70] [packed38, packed40, packed38, packed40, packed38, packed42] [packed14, packed2, packed2, packed13, packed14, packed33, packed55, packed70]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3794 : L0Gen 1 * L0Rep 3794 =
    L0Rep (L0Act 1 3794) * evalWord L1Gen (L0Factor 1 3794) := by
  apply step_of_packed_check rawBlock_spec 3794 [38, 46, 38, 40, 38, 42] [14, 13, 13, 13, 13, 29, 67, 64, 58] [packed38, packed46, packed38, packed40, packed38, packed42] [packed14, packed13, packed13, packed13, packed13, packed29, packed67, packed64, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3797 : L0Gen 1 * L0Rep 3797 =
    L0Rep (L0Act 1 3797) * evalWord L1Gen (L0Factor 1 3797) := by
  apply step_of_packed_check rawBlock_spec 3797 [40, 44, 44, 40, 38, 42] [1, 2, 13, 13, 2, 75, 50, 61, 72, 63] [packed40, packed44, packed44, packed40, packed38, packed42] [packed1, packed2, packed13, packed13, packed2, packed75, packed50, packed61, packed72, packed63]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
