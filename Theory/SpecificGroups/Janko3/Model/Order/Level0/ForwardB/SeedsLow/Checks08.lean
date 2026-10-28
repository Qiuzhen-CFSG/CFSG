module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 8.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed2234 : L0Gen 1 * L0Rep 2234 =
    L0Rep (L0Act 1 2234) * evalWord L1Gen (L0Factor 1 2234) := by
  apply step_of_packed_check rawBlock_spec 2234 [40, 44, 38, 46, 43] [14, 2, 14, 14, 4, 72, 67, 67, 55, 48] [packed40, packed44, packed38, packed46, packed43] [packed14, packed2, packed14, packed14, packed4, packed72, packed67, packed67, packed55, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2235 : L0Gen 1 * L0Rep 2235 =
    L0Rep (L0Act 1 2235) * evalWord L1Gen (L0Factor 1 2235) := by
  apply step_of_packed_check rawBlock_spec 2235 [38, 40, 38, 46, 43] [1, 1, 1, 2, 5, 64, 64, 61, 73, 69] [packed38, packed40, packed38, packed46, packed43] [packed1, packed1, packed1, packed2, packed5, packed64, packed64, packed61, packed73, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2241 : L0Gen 1 * L0Rep 2241 =
    L0Rep (L0Act 1 2241) * evalWord L1Gen (L0Factor 1 2241) := by
  apply step_of_packed_check rawBlock_spec 2241 [38, 40, 44, 46, 43] [1, 1, 1, 14, 21, 64, 67, 55, 51, 65] [packed38, packed40, packed44, packed46, packed43] [packed1, packed1, packed1, packed14, packed21, packed64, packed67, packed55, packed51, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2252 : L0Gen 1 * L0Rep 2252 =
    L0Rep (L0Act 1 2252) * evalWord L1Gen (L0Factor 1 2252) := by
  apply step_of_packed_check rawBlock_spec 2252 [38, 40, 44, 38, 39] [1, 1, 2, 14, 10, 73, 54, 67, 47] [packed38, packed40, packed44, packed38, packed39] [packed1, packed1, packed2, packed14, packed10, packed73, packed54, packed67, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2253 : L0Gen 1 * L0Rep 2253 =
    L0Rep (L0Act 1 2253) * evalWord L1Gen (L0Factor 1 2253) := by
  apply step_of_packed_check rawBlock_spec 2253 [40, 38, 40, 38, 39] [14, 14, 1, 1, 9, 61, 72, 67, 57] [packed40, packed38, packed40, packed38, packed39] [packed14, packed14, packed1, packed1, packed9, packed61, packed72, packed67, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2264 : L0Gen 1 * L0Rep 2264 =
    L0Rep (L0Act 1 2264) * evalWord L1Gen (L0Factor 1 2264) := by
  apply step_of_packed_check rawBlock_spec 2264 [38, 44, 44, 44, 39] [14, 13, 13, 13, 10, 57, 51, 63, 55, 48] [packed38, packed44, packed44, packed44, packed39] [packed14, packed13, packed13, packed13, packed10, packed57, packed51, packed63, packed55, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2267 : L0Gen 1 * L0Rep 2267 =
    L0Rep (L0Act 1 2267) * evalWord L1Gen (L0Factor 1 2267) := by
  apply step_of_packed_check rawBlock_spec 2267 [40, 46, 44, 44, 39] [2, 13, 13, 2, 16, 73, 72, 67, 67, 61] [packed40, packed46, packed44, packed44, packed39] [packed2, packed13, packed13, packed2, packed16, packed73, packed72, packed67, packed67, packed61]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2271 : L0Gen 1 * L0Rep 2271 =
    L0Rep (L0Act 1 2271) * evalWord L1Gen (L0Factor 1 2271) := by
  apply step_of_packed_check rawBlock_spec 2271 [40, 40, 38, 40, 39] [14, 13, 13, 2, 3, 63, 55, 69] [packed40, packed40, packed38, packed40, packed39] [packed14, packed13, packed13, packed2, packed3, packed63, packed55, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
