module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 31.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed4694 : L0Gen 1 * L0Rep 4694 =
    L0Rep (L0Act 1 4694) * evalWord L1Gen (L0Factor 1 4694) := by
  apply step_of_packed_check rawBlock_spec 4694 [38, 44, 40, 40, 44, 37] [1, 14, 13, 2, 1, 16, 73, 72, 67, 68, 59] [packed38, packed44, packed40, packed40, packed44, packed37] [packed1, packed14, packed13, packed2, packed1, packed16, packed73, packed72, packed67, packed68, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4700 : L0Gen 1 * L0Rep 4700 =
    L0Rep (L0Act 1 4700) * evalWord L1Gen (L0Factor 1 4700) := by
  apply step_of_packed_check rawBlock_spec 4700 [40, 44, 46, 40, 44, 37] [2, 1, 2, 14, 14, 17, 64, 61, 73, 75, 48] [packed40, packed44, packed46, packed40, packed44, packed37] [packed2, packed1, packed2, packed14, packed14, packed17, packed64, packed61, packed73, packed75, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4701 : L0Gen 1 * L0Rep 4701 =
    L0Rep (L0Act 1 4701) * evalWord L1Gen (L0Factor 1 4701) := by
  apply step_of_packed_check rawBlock_spec 4701 [40, 40, 38, 46, 44, 37] [1, 2, 13, 1, 13, 3, 55, 73, 50, 59] [packed40, packed40, packed38, packed46, packed44, packed37] [packed1, packed2, packed13, packed1, packed13, packed3, packed55, packed73, packed50, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4702 : L0Gen 1 * L0Rep 4702 =
    L0Rep (L0Act 1 4702) * evalWord L1Gen (L0Factor 1 4702) := by
  apply step_of_packed_check rawBlock_spec 4702 [38, 46, 38, 46, 44, 37] [2, 1, 14, 2, 14, 5, 64, 64, 61, 70] [packed38, packed46, packed38, packed46, packed44, packed37] [packed2, packed1, packed14, packed2, packed14, packed5, packed64, packed64, packed61, packed70]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4703 : L0Gen 1 * L0Rep 4703 =
    L0Rep (L0Act 1 4703) * evalWord L1Gen (L0Factor 1 4703) := by
  apply step_of_packed_check rawBlock_spec 4703 [38, 46, 44, 46, 44, 37] [2, 14, 2, 1, 13, 18, 64, 63, 59] [packed38, packed46, packed44, packed46, packed44, packed37] [packed2, packed14, packed2, packed1, packed13, packed18, packed64, packed63, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4704 : L0Gen 1 * L0Rep 4704 =
    L0Rep (L0Act 1 4704) * evalWord L1Gen (L0Factor 1 4704) := by
  apply step_of_packed_check rawBlock_spec 4704 [40, 46, 44, 46, 44, 37] [2, 1, 2, 13, 14, 19, 51, 63, 56] [packed40, packed46, packed44, packed46, packed44, packed37] [packed2, packed1, packed2, packed13, packed14, packed19, packed51, packed63, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4706 : L0Gen 1 * L0Rep 4706 =
    L0Rep (L0Act 1 4706) * evalWord L1Gen (L0Factor 1 4706) := by
  apply step_of_packed_check rawBlock_spec 4706 [40, 44, 40, 46, 44, 37] [14, 13, 2, 13, 13, 8, 67, 61, 70] [packed40, packed44, packed40, packed46, packed44, packed37] [packed14, packed13, packed2, packed13, packed13, packed8, packed67, packed61, packed70]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4708 : L0Gen 1 * L0Rep 4708 =
    L0Rep (L0Act 1 4708) * evalWord L1Gen (L0Factor 1 4708) := by
  apply step_of_packed_check rawBlock_spec 4708 [40, 40, 46, 38, 40, 37] [2, 2, 13, 1, 13, 15, 64, 64, 64, 64] [packed40, packed40, packed46, packed38, packed40, packed37] [packed2, packed2, packed13, packed1, packed13, packed15, packed64, packed64, packed64, packed64]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4713 : L0Gen 1 * L0Rep 4713 =
    L0Rep (L0Act 1 4713) * evalWord L1Gen (L0Factor 1 4713) := by
  apply step_of_packed_check rawBlock_spec 4713 [38, 38, 40, 40, 40, 37] [2, 14, 2, 14, 14, 15, 68, 63, 67, 59] [packed38, packed38, packed40, packed40, packed40, packed37] [packed2, packed14, packed2, packed14, packed14, packed15, packed68, packed63, packed67, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
