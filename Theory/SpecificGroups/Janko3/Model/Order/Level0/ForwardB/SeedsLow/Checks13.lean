module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 13.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed2481 : L0Gen 1 * L0Rep 2481 =
    L0Rep (L0Act 1 2481) * evalWord L1Gen (L0Factor 1 2481) := by
  apply step_of_packed_check rawBlock_spec 2481 [38, 46, 44, 46, 44] [1, 13, 13, 13, 3, 67, 67, 55] [packed38, packed46, packed44, packed46, packed44] [packed1, packed13, packed13, packed13, packed3, packed67, packed67, packed55]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2484 : L0Gen 1 * L0Rep 2484 =
    L0Rep (L0Act 1 2484) * evalWord L1Gen (L0Factor 1 2484) := by
  apply step_of_packed_check rawBlock_spec 2484 [40, 44, 40, 46, 44] [13, 14, 14, 13, 17, 67, 67, 68, 63, 67] [packed40, packed44, packed40, packed46, packed44] [packed13, packed14, packed14, packed13, packed17, packed67, packed67, packed68, packed63, packed67]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2490 : L0Gen 1 * L0Rep 2490 =
    L0Rep (L0Act 1 2490) * evalWord L1Gen (L0Factor 1 2490) := by
  apply step_of_packed_check rawBlock_spec 2490 [40, 38, 46, 46, 44] [13, 2, 14, 1, 16, 51, 63, 55, 51, 58] [packed40, packed38, packed46, packed46, packed44] [packed13, packed2, packed14, packed1, packed16, packed51, packed63, packed55, packed51, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2491 : L0Gen 1 * L0Rep 2491 =
    L0Rep (L0Act 1 2491) * evalWord L1Gen (L0Factor 1 2491) := by
  apply step_of_packed_check rawBlock_spec 2491 [38, 44, 46, 46, 44] [14, 2, 1, 1, 16, 73, 50, 61, 73, 71] [packed38, packed44, packed46, packed46, packed44] [packed14, packed2, packed1, packed1, packed16, packed73, packed50, packed61, packed73, packed71]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2497 : L0Gen 1 * L0Rep 2497 =
    L0Rep (L0Act 1 2497) * evalWord L1Gen (L0Factor 1 2497) := by
  apply step_of_packed_check rawBlock_spec 2497 [38, 44, 38, 38, 40] [2, 1, 13, 13, 21, 68, 64, 64, 60] [packed38, packed44, packed38, packed38, packed40] [packed2, packed1, packed13, packed13, packed21, packed68, packed64, packed64, packed60]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2499 : L0Gen 1 * L0Rep 2499 =
    L0Rep (L0Act 1 2499) * evalWord L1Gen (L0Factor 1 2499) := by
  apply step_of_packed_check rawBlock_spec 2499 [40, 40, 38, 38, 40] [13, 13, 1, 1, 16, 73, 50, 67, 67, 59] [packed40, packed40, packed38, packed38, packed40] [packed13, packed13, packed1, packed1, packed16, packed73, packed50, packed67, packed67, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2501 : L0Gen 1 * L0Rep 2501 =
    L0Rep (L0Act 1 2501) * evalWord L1Gen (L0Factor 1 2501) := by
  apply step_of_packed_check rawBlock_spec 2501 [40, 38, 44, 38, 40] [14, 14, 1, 13, 6, 67, 61, 57, 55, 48] [packed40, packed38, packed44, packed38, packed40] [packed14, packed14, packed1, packed13, packed6, packed67, packed61, packed57, packed55, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2508 : L0Gen 1 * L0Rep 2508 =
    L0Rep (L0Act 1 2508) * evalWord L1Gen (L0Factor 1 2508) := by
  apply step_of_packed_check rawBlock_spec 2508 [40, 38, 40, 38, 40] [2, 2, 14, 2, 3, 67, 67, 64, 67, 67, 65] [packed40, packed38, packed40, packed38, packed40] [packed2, packed2, packed14, packed2, packed3, packed67, packed67, packed64, packed67, packed67, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
