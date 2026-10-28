module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 10.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed2333 : L0Gen 1 * L0Rep 2333 =
    L0Rep (L0Act 1 2333) * evalWord L1Gen (L0Factor 1 2333) := by
  apply step_of_packed_check rawBlock_spec 2333 [40, 38, 44, 40, 45] [13, 2, 1, 14, 18, 67, 61, 57] [packed40, packed38, packed44, packed40, packed45] [packed13, packed2, packed1, packed14, packed18, packed67, packed61, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2339 : L0Gen 1 * L0Rep 2339 =
    L0Rep (L0Act 1 2339) * evalWord L1Gen (L0Factor 1 2339) := by
  apply step_of_packed_check rawBlock_spec 2339 [38, 38, 38, 46, 45] [13, 13, 14, 2, 3, 63, 55, 50, 61, 48] [packed38, packed38, packed38, packed46, packed45] [packed13, packed13, packed14, packed2, packed3, packed63, packed55, packed50, packed61, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2348 : L0Gen 1 * L0Rep 2348 =
    L0Rep (L0Act 1 2348) * evalWord L1Gen (L0Factor 1 2348) := by
  apply step_of_packed_check rawBlock_spec 2348 [38, 44, 44, 46, 45] [2, 2, 2, 14, 22, 64, 63, 55, 73, 47] [packed38, packed44, packed44, packed46, packed45] [packed2, packed2, packed2, packed14, packed22, packed64, packed63, packed55, packed73, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2349 : L0Gen 1 * L0Rep 2349 =
    L0Rep (L0Act 1 2349) * evalWord L1Gen (L0Factor 1 2349) := by
  apply step_of_packed_check rawBlock_spec 2349 [40, 44, 44, 46, 45] [1, 2, 2, 2, 22, 61, 73, 72, 59] [packed40, packed44, packed44, packed46, packed45] [packed1, packed2, packed2, packed2, packed22, packed61, packed73, packed72, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2361 : L0Gen 1 * L0Rep 2361 =
    L0Rep (L0Act 1 2361) * evalWord L1Gen (L0Factor 1 2361) := by
  apply step_of_packed_check rawBlock_spec 2361 [40, 46, 46, 46, 45] [2, 13, 14, 14, 17, 63, 57, 54, 63, 47] [packed40, packed46, packed46, packed46, packed45] [packed2, packed13, packed14, packed14, packed17, packed63, packed57, packed54, packed63, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2363 : L0Gen 1 * L0Rep 2363 =
    L0Rep (L0Act 1 2363) * evalWord L1Gen (L0Factor 1 2363) := by
  apply step_of_packed_check rawBlock_spec 2363 [40, 44, 40, 38, 38] [2, 13, 2, 14, 4, 72, 67, 57, 57, 69] [packed40, packed44, packed40, packed38, packed38] [packed2, packed13, packed2, packed14, packed4, packed72, packed67, packed57, packed57, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2366 : L0Gen 1 * L0Rep 2366 =
    L0Rep (L0Act 1 2366) * evalWord L1Gen (L0Factor 1 2366) := by
  apply step_of_packed_check rawBlock_spec 2366 [38, 44, 46, 38, 38] [1, 14, 14, 1, 4, 54, 67, 55, 50, 67] [packed38, packed44, packed46, packed38, packed38] [packed1, packed14, packed14, packed1, packed4, packed54, packed67, packed55, packed50, packed67]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2383 : L0Gen 1 * L0Rep 2383 =
    L0Rep (L0Act 1 2383) * evalWord L1Gen (L0Factor 1 2383) := by
  apply step_of_packed_check rawBlock_spec 2383 [38, 40, 46, 44, 38] [2, 13, 2, 2, 4, 51, 64, 64, 58] [packed38, packed40, packed46, packed44, packed38] [packed2, packed13, packed2, packed2, packed4, packed51, packed64, packed64, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
