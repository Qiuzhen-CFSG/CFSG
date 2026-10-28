module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 25.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3735 : L0Gen 1 * L0Rep 3735 =
    L0Rep (L0Act 1 3735) * evalWord L1Gen (L0Factor 1 3735) := by
  apply step_of_packed_check rawBlock_spec 3735 [38, 46, 46, 46, 40, 36] [14, 1, 1, 14, 13, 31, 57, 72, 65] [packed38, packed46, packed46, packed46, packed40, packed36] [packed14, packed1, packed1, packed14, packed13, packed31, packed57, packed72, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3736 : L0Gen 1 * L0Rep 3736 =
    L0Rep (L0Act 1 3736) * evalWord L1Gen (L0Factor 1 3736) := by
  apply step_of_packed_check rawBlock_spec 3736 [40, 46, 46, 46, 40, 36] [14, 1, 2, 14, 1, 31, 72, 64, 65] [packed40, packed46, packed46, packed46, packed40, packed36] [packed14, packed1, packed2, packed14, packed1, packed31, packed72, packed64, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3739 : L0Gen 1 * L0Rep 3739 =
    L0Rep (L0Act 1 3739) * evalWord L1Gen (L0Factor 1 3739) := by
  apply step_of_packed_check rawBlock_spec 3739 [38, 40, 38, 38, 46, 36] [14, 14, 2, 13, 13, 31, 73, 73, 73, 70] [packed38, packed40, packed38, packed38, packed46, packed36] [packed14, packed14, packed2, packed13, packed13, packed31, packed73, packed73, packed73, packed70]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3749 : L0Gen 1 * L0Rep 3749 =
    L0Rep (L0Act 1 3749) * evalWord L1Gen (L0Factor 1 3749) := by
  apply step_of_packed_check rawBlock_spec 3749 [40, 46, 46, 38, 46, 36] [13, 13, 2, 13, 1, 68, 63, 68, 64, 59] [packed40, packed46, packed46, packed38, packed46, packed36] [packed13, packed13, packed2, packed13, packed1, packed68, packed63, packed68, packed64, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3754 : L0Gen 1 * L0Rep 3754 =
    L0Rep (L0Act 1 3754) * evalWord L1Gen (L0Factor 1 3754) := by
  apply step_of_packed_check rawBlock_spec 3754 [38, 46, 44, 40, 46, 36] [14, 2, 13, 14, 13, 54, 63, 57, 54, 58] [packed38, packed46, packed44, packed40, packed46, packed36] [packed14, packed2, packed13, packed14, packed13, packed54, packed63, packed57, packed54, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3757 : L0Gen 1 * L0Rep 3757 =
    L0Rep (L0Act 1 3757) * evalWord L1Gen (L0Factor 1 3757) := by
  apply step_of_packed_check rawBlock_spec 3757 [40, 38, 40, 40, 46, 36] [13, 1, 2, 2, 2, 50, 61, 72, 63, 56] [packed40, packed38, packed40, packed40, packed46, packed36] [packed13, packed1, packed2, packed2, packed2, packed50, packed61, packed72, packed63, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3763 : L0Gen 1 * L0Rep 3763 =
    L0Rep (L0Act 1 3763) * evalWord L1Gen (L0Factor 1 3763) := by
  apply step_of_packed_check rawBlock_spec 3763 [38, 46, 46, 40, 46, 36] [2, 13, 14, 1, 1, 68, 61, 57, 55] [packed38, packed46, packed46, packed40, packed46, packed36] [packed2, packed13, packed14, packed1, packed1, packed68, packed61, packed57, packed55]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3767 : L0Gen 1 * L0Rep 3767 =
    L0Rep (L0Act 1 3767) * evalWord L1Gen (L0Factor 1 3767) := by
  apply step_of_packed_check rawBlock_spec 3767 [40, 46, 38, 46, 46, 36] [13, 13, 14, 14, 13, 25, 57, 51, 64, 63, 52] [packed40, packed46, packed38, packed46, packed46, packed36] [packed13, packed13, packed14, packed14, packed13, packed25, packed57, packed51, packed64, packed63, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
