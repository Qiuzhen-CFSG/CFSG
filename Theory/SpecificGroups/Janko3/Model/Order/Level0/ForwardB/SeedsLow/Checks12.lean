module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 12.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed2413 : L0Gen 1 * L0Rep 2413 =
    L0Rep (L0Act 1 2413) * evalWord L1Gen (L0Factor 1 2413) := by
  apply step_of_packed_check rawBlock_spec 2413 [40, 40, 40, 46, 38] [2, 13, 14, 2, 16, 55, 51, 64, 63] [packed40, packed40, packed40, packed46, packed38] [packed2, packed13, packed14, packed2, packed16, packed55, packed51, packed64, packed63]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2415 : L0Gen 1 * L0Rep 2415 =
    L0Rep (L0Act 1 2415) * evalWord L1Gen (L0Factor 1 2415) := by
  apply step_of_packed_check rawBlock_spec 2415 [40, 46, 40, 46, 38] [13, 2, 2, 1, 23, 72, 67, 67, 67] [packed40, packed46, packed40, packed46, packed38] [packed13, packed2, packed2, packed1, packed23, packed72, packed67, packed67, packed67]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2420 : L0Gen 1 * L0Rep 2420 =
    L0Rep (L0Act 1 2420) * evalWord L1Gen (L0Factor 1 2420) := by
  apply step_of_packed_check rawBlock_spec 2420 [40, 40, 38, 38, 44] [1, 2, 13, 13, 23, 73, 72, 67, 66] [packed40, packed40, packed38, packed38, packed44] [packed1, packed2, packed13, packed13, packed23, packed73, packed72, packed67, packed66]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2427 : L0Gen 1 * L0Rep 2427 =
    L0Rep (L0Act 1 2427) * evalWord L1Gen (L0Factor 1 2427) := by
  apply step_of_packed_check rawBlock_spec 2427 [40, 46, 44, 38, 44] [13, 1, 2, 14, 15, 67, 67, 61, 54, 59] [packed40, packed46, packed44, packed38, packed44] [packed13, packed1, packed2, packed14, packed15, packed67, packed67, packed61, packed54, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2450 : L0Gen 1 * L0Rep 2450 =
    L0Rep (L0Act 1 2450) * evalWord L1Gen (L0Factor 1 2450) := by
  apply step_of_packed_check rawBlock_spec 2450 [38, 46, 40, 44, 44] [14, 2, 1, 13, 7, 50, 61, 57, 56] [packed38, packed46, packed40, packed44, packed44] [packed14, packed2, packed1, packed13, packed7, packed50, packed61, packed57, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2458 : L0Gen 1 * L0Rep 2458 =
    L0Rep (L0Act 1 2458) * evalWord L1Gen (L0Factor 1 2458) := by
  apply step_of_packed_check rawBlock_spec 2458 [40, 38, 38, 40, 44] [2, 1, 14, 13, 4, 50, 61, 52] [packed40, packed38, packed38, packed40, packed44] [packed2, packed1, packed14, packed13, packed4, packed50, packed61, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2466 : L0Gen 1 * L0Rep 2466 =
    L0Rep (L0Act 1 2466) * evalWord L1Gen (L0Factor 1 2466) := by
  apply step_of_packed_check rawBlock_spec 2466 [40, 44, 44, 40, 44] [13, 2, 13, 2, 4, 51, 64, 61, 56] [packed40, packed44, packed44, packed40, packed44] [packed13, packed2, packed13, packed2, packed4, packed51, packed64, packed61, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2478 : L0Gen 1 * L0Rep 2478 =
    L0Rep (L0Act 1 2478) * evalWord L1Gen (L0Factor 1 2478) := by
  apply step_of_packed_check rawBlock_spec 2478 [40, 44, 44, 46, 44] [14, 1, 1, 2, 16, 73, 51, 61, 48] [packed40, packed44, packed44, packed46, packed44] [packed14, packed1, packed1, packed2, packed16, packed73, packed51, packed61, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
