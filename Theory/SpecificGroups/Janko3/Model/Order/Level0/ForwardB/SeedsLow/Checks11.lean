module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 11.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed2395 : L0Gen 1 * L0Rep 2395 =
    L0Rep (L0Act 1 2395) * evalWord L1Gen (L0Factor 1 2395) := by
  apply step_of_packed_check rawBlock_spec 2395 [40, 40, 40, 40, 38] [2, 2, 2, 2, 12] [packed40, packed40, packed40, packed40, packed38] [packed2, packed2, packed2, packed2, packed12]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2400 : L0Gen 1 * L0Rep 2400 =
    L0Rep (L0Act 1 2400) * evalWord L1Gen (L0Factor 1 2400) := by
  apply step_of_packed_check rawBlock_spec 2400 [40, 44, 46, 40, 38] [2, 13, 14, 14, 3] [packed40, packed44, packed46, packed40, packed38] [packed2, packed13, packed14, packed14, packed3]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2402 : L0Gen 1 * L0Rep 2402 =
    L0Rep (L0Act 1 2402) * evalWord L1Gen (L0Factor 1 2402) := by
  apply step_of_packed_check rawBlock_spec 2402 [40, 40, 46, 40, 38] [14, 14, 1, 1, 17, 64, 61, 72, 64, 59] [packed40, packed40, packed46, packed40, packed38] [packed14, packed14, packed1, packed1, packed17, packed64, packed61, packed72, packed64, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2403 : L0Gen 1 * L0Rep 2403 =
    L0Rep (L0Act 1 2403) * evalWord L1Gen (L0Factor 1 2403) := by
  apply step_of_packed_check rawBlock_spec 2403 [38, 38, 38, 46, 38] [1, 13, 2, 2, 8, 67, 67, 67, 55, 48] [packed38, packed38, packed38, packed46, packed38] [packed1, packed13, packed2, packed2, packed8, packed67, packed67, packed67, packed55, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2404 : L0Gen 1 * L0Rep 2404 =
    L0Rep (L0Act 1 2404) * evalWord L1Gen (L0Factor 1 2404) := by
  apply step_of_packed_check rawBlock_spec 2404 [38, 44, 38, 46, 38] [2, 1, 13, 14, 15, 55, 75, 55, 51, 61] [packed38, packed44, packed38, packed46, packed38] [packed2, packed1, packed13, packed14, packed15, packed55, packed75, packed55, packed51, packed61]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2405 : L0Gen 1 * L0Rep 2405 =
    L0Rep (L0Act 1 2405) * evalWord L1Gen (L0Factor 1 2405) := by
  apply step_of_packed_check rawBlock_spec 2405 [40, 44, 38, 46, 38] [14, 2, 13, 14, 10, 73, 73, 75, 55, 69] [packed40, packed44, packed38, packed46, packed38] [packed14, packed2, packed13, packed14, packed10, packed73, packed73, packed75, packed55, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2408 : L0Gen 1 * L0Rep 2408 =
    L0Rep (L0Act 1 2408) * evalWord L1Gen (L0Factor 1 2408) := by
  apply step_of_packed_check rawBlock_spec 2408 [38, 38, 40, 46, 38] [14, 1, 2, 14, 4, 73, 75, 51] [packed38, packed38, packed40, packed46, packed38] [packed14, packed1, packed2, packed14, packed4, packed73, packed75, packed51]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2412 : L0Gen 1 * L0Rep 2412 =
    L0Rep (L0Act 1 2412) * evalWord L1Gen (L0Factor 1 2412) := by
  apply step_of_packed_check rawBlock_spec 2412 [38, 40, 40, 46, 38] [13, 2, 1, 2, 4, 54, 64, 63] [packed38, packed40, packed40, packed46, packed38] [packed13, packed2, packed1, packed2, packed4, packed54, packed64, packed63]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
