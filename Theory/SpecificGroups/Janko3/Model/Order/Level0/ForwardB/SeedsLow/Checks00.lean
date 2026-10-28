module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 0.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed196 : L0Gen 1 * L0Rep 196 =
    L0Rep (L0Act 1 196) * evalWord L1Gen (L0Factor 1 196) := by
  apply step_of_packed_check rawBlock_spec 196 [40, 44, 43] [2, 13, 15, 67, 67, 64, 67, 67, 65] [packed40, packed44, packed43] [packed2, packed13, packed15, packed67, packed67, packed64, packed67, packed67, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed197 : L0Gen 1 * L0Rep 197 =
    L0Rep (L0Act 1 197) * evalWord L1Gen (L0Factor 1 197) := by
  apply step_of_packed_check rawBlock_spec 197 [38, 40, 43] [1, 14, 15, 63, 57, 51, 63, 55] [packed38, packed40, packed43] [packed1, packed14, packed15, packed63, packed57, packed51, packed63, packed55]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed209 : L0Gen 1 * L0Rep 209 =
    L0Rep (L0Act 1 209) * evalWord L1Gen (L0Factor 1 209) := by
  apply step_of_packed_check rawBlock_spec 209 [38, 38, 45] [1, 2, 19, 57, 51, 58] [packed38, packed38, packed45] [packed1, packed2, packed19, packed57, packed51, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed389 : L0Gen 1 * L0Rep 389 =
    L0Rep (L0Act 1 389) * evalWord L1Gen (L0Factor 1 389) := by
  apply step_of_packed_check rawBlock_spec 389 [38, 40, 38, 41] [1, 13, 2, 57, 73, 49] [packed38, packed40, packed38, packed41] [packed1, packed13, packed2, packed57, packed73, packed49]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed406 : L0Gen 1 * L0Rep 406 =
    L0Rep (L0Act 1 406) * evalWord L1Gen (L0Factor 1 406) := by
  apply step_of_packed_check rawBlock_spec 406 [38, 44, 46, 41] [2, 2, 14, 64, 63, 55, 73] [packed38, packed44, packed46, packed41] [packed2, packed2, packed14, packed64, packed63, packed55, packed73]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed423 : L0Gen 1 * L0Rep 423 =
    L0Rep (L0Act 1 423) * evalWord L1Gen (L0Factor 1 423) := by
  apply step_of_packed_check rawBlock_spec 423 [40, 46, 44, 36] [13, 13, 1, 25, 57, 73, 54, 67, 52] [packed40, packed46, packed44, packed36] [packed13, packed13, packed1, packed25, packed57, packed73, packed54, packed67, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed667 : L0Gen 1 * L0Rep 667 =
    L0Rep (L0Act 1 667) * evalWord L1Gen (L0Factor 1 667) := by
  apply step_of_packed_check rawBlock_spec 667 [38, 46, 38, 37] [14, 13, 1, 3, 61, 54, 63, 53] [packed38, packed46, packed38, packed37] [packed14, packed13, packed1, packed3, packed61, packed54, packed63, packed53]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed686 : L0Gen 1 * L0Rep 686 =
    L0Rep (L0Act 1 686) * evalWord L1Gen (L0Factor 1 686) := by
  apply step_of_packed_check rawBlock_spec 686 [38, 46, 46, 37] [14, 13, 14, 10, 57, 50, 67, 58] [packed38, packed46, packed46, packed37] [packed14, packed13, packed14, packed10, packed57, packed50, packed67, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
