module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 2.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed1232 : L0Gen 1 * L0Rep 1232 =
    L0Rep (L0Act 1 1232) * evalWord L1Gen (L0Factor 1 1232) := by
  apply step_of_packed_check rawBlock_spec 1232 [38, 46, 44, 44, 35] [13, 2, 1, 14, 50, 67, 63, 47] [packed38, packed46, packed44, packed44, packed35] [packed13, packed2, packed1, packed14, packed50, packed67, packed63, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1265 : L0Gen 1 * L0Rep 1265 =
    L0Rep (L0Act 1 1265) * evalWord L1Gen (L0Factor 1 1265) := by
  apply step_of_packed_check rawBlock_spec 1265 [40, 40, 44, 46, 35] [13, 14, 14, 2, 25, 73, 57, 73, 72, 63] [packed40, packed40, packed44, packed46, packed35] [packed13, packed14, packed14, packed2, packed25, packed73, packed57, packed73, packed72, packed63]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1277 : L0Gen 1 * L0Rep 1277 =
    L0Rep (L0Act 1 1277) * evalWord L1Gen (L0Factor 1 1277) := by
  apply step_of_packed_check rawBlock_spec 1277 [40, 46, 46, 46, 35] [14, 14, 14, 13, 73, 72, 64, 62] [packed40, packed46, packed46, packed46, packed35] [packed14, packed14, packed14, packed13, packed73, packed72, packed64, packed62]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1278 : L0Gen 1 * L0Rep 1278 =
    L0Rep (L0Act 1 1278) * evalWord L1Gen (L0Factor 1 1278) := by
  apply step_of_packed_check rawBlock_spec 1278 [38, 40, 38, 38, 41] [2, 14, 14, 13, 67, 67, 55, 73] [packed38, packed40, packed38, packed38, packed41] [packed2, packed14, packed14, packed13, packed67, packed67, packed55, packed73]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1288 : L0Gen 1 * L0Rep 1288 =
    L0Rep (L0Act 1 1288) * evalWord L1Gen (L0Factor 1 1288) := by
  apply step_of_packed_check rawBlock_spec 1288 [40, 46, 44, 38, 41] [2, 1, 14, 13, 33, 61, 72, 63, 55, 48] [packed40, packed46, packed44, packed38, packed41] [packed2, packed1, packed14, packed13, packed33, packed61, packed72, packed63, packed55, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1289 : L0Gen 1 * L0Rep 1289 =
    L0Rep (L0Act 1 1289) * evalWord L1Gen (L0Factor 1 1289) := by
  apply step_of_packed_check rawBlock_spec 1289 [38, 40, 40, 38, 41] [2, 1, 13, 13, 31, 57, 51, 64, 63, 52] [packed38, packed40, packed40, packed38, packed41] [packed2, packed1, packed13, packed13, packed31, packed57, packed51, packed64, packed63, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1293 : L0Gen 1 * L0Rep 1293 =
    L0Rep (L0Act 1 1293) * evalWord L1Gen (L0Factor 1 1293) := by
  apply step_of_packed_check rawBlock_spec 1293 [38, 38, 38, 44, 41] [1, 1, 2, 2, 63, 55, 74] [packed38, packed38, packed38, packed44, packed41] [packed1, packed1, packed2, packed2, packed63, packed55, packed74]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1310 : L0Gen 1 * L0Rep 1310 =
    L0Rep (L0Act 1 1310) * evalWord L1Gen (L0Factor 1 1310) := by
  apply step_of_packed_check rawBlock_spec 1310 [38, 40, 40, 44, 41] [1, 13, 13, 13, 73, 51, 61, 57, 55, 47] [packed38, packed40, packed40, packed44, packed41] [packed1, packed13, packed13, packed13, packed73, packed51, packed61, packed57, packed55, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
