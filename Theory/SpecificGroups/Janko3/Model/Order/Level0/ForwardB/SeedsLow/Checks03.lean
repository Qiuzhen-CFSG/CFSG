module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 3.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed1316 : L0Gen 1 * L0Rep 1316 =
    L0Rep (L0Act 1 1316) * evalWord L1Gen (L0Factor 1 1316) := by
  apply step_of_packed_check rawBlock_spec 1316 [38, 44, 46, 44, 41] [2, 2, 14, 2, 57, 57, 51, 61, 69] [packed38, packed44, packed46, packed44, packed41] [packed2, packed2, packed14, packed2, packed57, packed57, packed51, packed61, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1319 : L0Gen 1 * L0Rep 1319 =
    L0Rep (L0Act 1 1319) * evalWord L1Gen (L0Factor 1 1319) := by
  apply step_of_packed_check rawBlock_spec 1319 [40, 40, 46, 44, 41] [2, 2, 1, 14, 31, 50, 61, 57, 57] [packed40, packed40, packed46, packed44, packed41] [packed2, packed2, packed1, packed14, packed31, packed50, packed61, packed57, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1352 : L0Gen 1 * L0Rep 1352 =
    L0Rep (L0Act 1 1352) * evalWord L1Gen (L0Factor 1 1352) := by
  apply step_of_packed_check rawBlock_spec 1352 [40, 44, 46, 46, 41] [2, 13, 14, 1, 67, 67, 57, 57] [packed40, packed44, packed46, packed46, packed41] [packed2, packed13, packed14, packed1, packed67, packed67, packed57, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1357 : L0Gen 1 * L0Rep 1357 =
    L0Rep (L0Act 1 1357) * evalWord L1Gen (L0Factor 1 1357) := by
  apply step_of_packed_check rawBlock_spec 1357 [38, 38, 44, 38, 36] [14, 14, 14, 14, 28] [packed38, packed38, packed44, packed38, packed36] [packed14, packed14, packed14, packed14, packed28]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1377 : L0Gen 1 * L0Rep 1377 =
    L0Rep (L0Act 1 1377) * evalWord L1Gen (L0Factor 1 1377) := by
  apply step_of_packed_check rawBlock_spec 1377 [38, 38, 44, 44, 36] [2, 1, 2, 2, 26, 67, 67, 61, 53] [packed38, packed38, packed44, packed44, packed36] [packed2, packed1, packed2, packed2, packed26, packed67, packed67, packed61, packed53]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1399 : L0Gen 1 * L0Rep 1399 =
    L0Rep (L0Act 1 1399) * evalWord L1Gen (L0Factor 1 1399) := by
  apply step_of_packed_check rawBlock_spec 1399 [38, 46, 38, 40, 36] [14, 14, 14, 1, 72, 64, 61, 74] [packed38, packed46, packed38, packed40, packed36] [packed14, packed14, packed14, packed1, packed72, packed64, packed61, packed74]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1402 : L0Gen 1 * L0Rep 1402 =
    L0Rep (L0Act 1 1402) * evalWord L1Gen (L0Factor 1 1402) := by
  apply step_of_packed_check rawBlock_spec 1402 [40, 38, 44, 40, 36] [13, 13, 2, 2, 32] [packed40, packed38, packed44, packed40, packed36] [packed13, packed13, packed2, packed2, packed32]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1406 : L0Gen 1 * L0Rep 1406 =
    L0Rep (L0Act 1 1406) * evalWord L1Gen (L0Factor 1 1406) := by
  apply step_of_packed_check rawBlock_spec 1406 [38, 46, 44, 40, 36] [14, 14, 13, 2, 30, 50, 67, 67, 62] [packed38, packed46, packed44, packed40, packed36] [packed14, packed14, packed13, packed2, packed30, packed50, packed67, packed67, packed62]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
