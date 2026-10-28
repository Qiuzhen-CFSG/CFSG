module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 4.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed1408 : L0Gen 1 * L0Rep 1408 =
    L0Rep (L0Act 1 1408) * evalWord L1Gen (L0Factor 1 1408) := by
  apply step_of_packed_check rawBlock_spec 1408 [38, 38, 40, 40, 36] [2, 14, 14, 13, 33, 64, 67, 64, 62] [packed38, packed38, packed40, packed40, packed36] [packed2, packed14, packed14, packed13, packed33, packed64, packed67, packed64, packed62]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1457 : L0Gen 1 * L0Rep 1457 =
    L0Rep (L0Act 1 1457) * evalWord L1Gen (L0Factor 1 1457) := by
  apply step_of_packed_check rawBlock_spec 1457 [40, 38, 44, 38, 42] [2, 1, 14, 1, 27, 61, 54, 67, 53] [packed40, packed38, packed44, packed38, packed42] [packed2, packed1, packed14, packed1, packed27, packed61, packed54, packed67, packed53]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1472 : L0Gen 1 * L0Rep 1472 =
    L0Rep (L0Act 1 1472) * evalWord L1Gen (L0Factor 1 1472) := by
  apply step_of_packed_check rawBlock_spec 1472 [38, 44, 46, 38, 42] [2, 14, 1, 2, 57, 50, 61, 74] [packed38, packed44, packed46, packed38, packed42] [packed2, packed14, packed1, packed2, packed57, packed50, packed61, packed74]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1473 : L0Gen 1 * L0Rep 1473 =
    L0Rep (L0Act 1 1473) * evalWord L1Gen (L0Factor 1 1473) := by
  apply step_of_packed_check rawBlock_spec 1473 [40, 44, 46, 38, 42] [2, 13, 1, 2, 54, 67, 67, 67, 63] [packed40, packed44, packed46, packed38, packed42] [packed2, packed13, packed1, packed2, packed54, packed67, packed67, packed67, packed63]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1478 : L0Gen 1 * L0Rep 1478 =
    L0Rep (L0Act 1 1478) * evalWord L1Gen (L0Factor 1 1478) := by
  apply step_of_packed_check rawBlock_spec 1478 [38, 38, 38, 44, 42] [2, 2, 14, 14, 68, 64, 61, 57, 55] [packed38, packed38, packed38, packed44, packed42] [packed2, packed2, packed14, packed14, packed68, packed64, packed61, packed57, packed55]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1479 : L0Gen 1 * L0Rep 1479 =
    L0Rep (L0Act 1 1479) * evalWord L1Gen (L0Factor 1 1479) := by
  apply step_of_packed_check rawBlock_spec 1479 [40, 38, 38, 44, 42] [1, 2, 2, 13, 50, 68, 63, 68] [packed40, packed38, packed38, packed44, packed42] [packed1, packed2, packed2, packed13, packed50, packed68, packed63, packed68]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1504 : L0Gen 1 * L0Rep 1504 =
    L0Rep (L0Act 1 1504) * evalWord L1Gen (L0Factor 1 1504) := by
  apply step_of_packed_check rawBlock_spec 1504 [38, 44, 40, 40, 42] [14, 2, 1, 14, 30, 73, 50, 61, 47] [packed38, packed44, packed40, packed40, packed42] [packed14, packed2, packed1, packed14, packed30, packed73, packed50, packed61, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1509 : L0Gen 1 * L0Rep 1509 =
    L0Rep (L0Act 1 1509) * evalWord L1Gen (L0Factor 1 1509) := by
  apply step_of_packed_check rawBlock_spec 1509 [40, 46, 40, 40, 42] [2, 1, 1, 14, 33, 64, 63, 57, 54] [packed40, packed46, packed40, packed40, packed42] [packed2, packed1, packed1, packed14, packed33, packed64, packed63, packed57, packed54]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
