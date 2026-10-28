module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 9.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed2272 : L0Gen 1 * L0Rep 2272 =
    L0Rep (L0Act 1 2272) * evalWord L1Gen (L0Factor 1 2272) := by
  apply step_of_packed_check rawBlock_spec 2272 [38, 46, 38, 40, 39] [14, 14, 1, 2, 9, 67, 67, 57, 56] [packed38, packed46, packed38, packed40, packed39] [packed14, packed14, packed1, packed2, packed9, packed67, packed67, packed57, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2276 : L0Gen 1 * L0Rep 2276 =
    L0Rep (L0Act 1 2276) * evalWord L1Gen (L0Factor 1 2276) := by
  apply step_of_packed_check rawBlock_spec 2276 [40, 46, 44, 40, 39] [14, 13, 13, 2, 21, 67, 68, 63, 65] [packed40, packed46, packed44, packed40, packed39] [packed14, packed13, packed13, packed2, packed21, packed67, packed68, packed63, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2281 : L0Gen 1 * L0Rep 2281 =
    L0Rep (L0Act 1 2281) * evalWord L1Gen (L0Factor 1 2281) := by
  apply step_of_packed_check rawBlock_spec 2281 [38, 46, 40, 40, 39] [13, 2, 2, 1, 3, 64, 61, 54, 67, 66] [packed38, packed46, packed40, packed40, packed39] [packed13, packed2, packed2, packed1, packed3, packed64, packed61, packed54, packed67, packed66]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2295 : L0Gen 1 * L0Rep 2295 =
    L0Rep (L0Act 1 2295) * evalWord L1Gen (L0Factor 1 2295) := by
  apply step_of_packed_check rawBlock_spec 2295 [38, 46, 44, 46, 39] [2, 2, 1, 14, 4, 50, 68, 63, 67, 65] [packed38, packed46, packed44, packed46, packed39] [packed2, packed2, packed1, packed14, packed4, packed50, packed68, packed63, packed67, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2303 : L0Gen 1 * L0Rep 2303 =
    L0Rep (L0Act 1 2303) * evalWord L1Gen (L0Factor 1 2303) := by
  apply step_of_packed_check rawBlock_spec 2303 [38, 40, 46, 46, 39] [2, 14, 14, 14, 4, 72, 63, 57, 51, 63, 52] [packed38, packed40, packed46, packed46, packed39] [packed2, packed14, packed14, packed14, packed4, packed72, packed63, packed57, packed51, packed63, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2312 : L0Gen 1 * L0Rep 2312 =
    L0Rep (L0Act 1 2312) * evalWord L1Gen (L0Factor 1 2312) := by
  apply step_of_packed_check rawBlock_spec 2312 [40, 38, 38, 44, 45] [13, 1, 2, 2, 23, 73, 57, 69] [packed40, packed38, packed38, packed44, packed45] [packed13, packed1, packed2, packed2, packed23, packed73, packed57, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2329 : L0Gen 1 * L0Rep 2329 =
    L0Rep (L0Act 1 2329) * evalWord L1Gen (L0Factor 1 2329) := by
  apply step_of_packed_check rawBlock_spec 2329 [40, 38, 38, 40, 45] [13, 2, 2, 2, 18, 67, 61, 57, 54] [packed40, packed38, packed38, packed40, packed45] [packed13, packed2, packed2, packed2, packed18, packed67, packed61, packed57, packed54]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2332 : L0Gen 1 * L0Rep 2332 =
    L0Rep (L0Act 1 2332) * evalWord L1Gen (L0Factor 1 2332) := by
  apply step_of_packed_check rawBlock_spec 2332 [38, 38, 44, 40, 45] [14, 13, 1, 13, 7, 75, 50, 61, 70] [packed38, packed38, packed44, packed40, packed45] [packed14, packed13, packed1, packed13, packed7, packed75, packed50, packed61, packed70]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
