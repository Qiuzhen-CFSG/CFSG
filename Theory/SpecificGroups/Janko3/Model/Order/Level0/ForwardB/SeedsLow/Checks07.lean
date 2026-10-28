module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 7.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed2175 : L0Gen 1 * L0Rep 2175 =
    L0Rep (L0Act 1 2175) * evalWord L1Gen (L0Factor 1 2175) := by
  apply step_of_packed_check rawBlock_spec 2175 [40, 46, 40, 40, 37] [13, 14, 13, 14, 22, 61, 72, 63, 57, 48] [packed40, packed46, packed40, packed40, packed37] [packed13, packed14, packed13, packed14, packed22, packed61, packed72, packed63, packed57, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2178 : L0Gen 1 * L0Rep 2178 =
    L0Rep (L0Act 1 2178) * evalWord L1Gen (L0Factor 1 2178) := by
  apply step_of_packed_check rawBlock_spec 2178 [40, 40, 46, 40, 37] [13, 14, 13, 13, 7, 73, 57, 47] [packed40, packed40, packed46, packed40, packed37] [packed13, packed14, packed13, packed13, packed7, packed73, packed57, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2183 : L0Gen 1 * L0Rep 2183 =
    L0Rep (L0Act 1 2183) * evalWord L1Gen (L0Factor 1 2183) := by
  apply step_of_packed_check rawBlock_spec 2183 [38, 44, 44, 46, 37] [1, 14, 2, 14, 7, 54, 63, 57] [packed38, packed44, packed44, packed46, packed37] [packed1, packed14, packed2, packed14, packed7, packed54, packed63, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2191 : L0Gen 1 * L0Rep 2191 =
    L0Rep (L0Act 1 2191) * evalWord L1Gen (L0Factor 1 2191) := by
  apply step_of_packed_check rawBlock_spec 2191 [40, 46, 40, 46, 37] [2, 1, 14, 13, 22, 64, 64, 67, 64, 58] [packed40, packed46, packed40, packed46, packed37] [packed2, packed1, packed14, packed13, packed22, packed64, packed64, packed67, packed64, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2201 : L0Gen 1 * L0Rep 2201 =
    L0Rep (L0Act 1 2201) * evalWord L1Gen (L0Factor 1 2201) := by
  apply step_of_packed_check rawBlock_spec 2201 [38, 44, 44, 38, 43] [1, 2, 1, 13, 6, 67, 67, 61, 57] [packed38, packed44, packed44, packed38, packed43] [packed1, packed2, packed1, packed13, packed6, packed67, packed67, packed61, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2203 : L0Gen 1 * L0Rep 2203 =
    L0Rep (L0Act 1 2203) * evalWord L1Gen (L0Factor 1 2203) := by
  apply step_of_packed_check rawBlock_spec 2203 [38, 40, 44, 38, 43] [2, 2, 14, 2, 21, 67, 68, 63, 67, 61] [packed38, packed40, packed44, packed38, packed43] [packed2, packed2, packed14, packed2, packed21, packed67, packed68, packed63, packed67, packed61]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2219 : L0Gen 1 * L0Rep 2219 =
    L0Rep (L0Act 1 2219) * evalWord L1Gen (L0Factor 1 2219) := by
  apply step_of_packed_check rawBlock_spec 2219 [38, 38, 44, 40, 43] [1, 2, 14, 1, 7, 72, 63, 53] [packed38, packed38, packed44, packed40, packed43] [packed1, packed2, packed14, packed1, packed7, packed72, packed63, packed53]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2229 : L0Gen 1 * L0Rep 2229 =
    L0Rep (L0Act 1 2229) * evalWord L1Gen (L0Factor 1 2229) := by
  apply step_of_packed_check rawBlock_spec 2229 [40, 38, 46, 40, 43] [13, 2, 13, 14, 7, 50, 67, 57] [packed40, packed38, packed46, packed40, packed43] [packed13, packed2, packed13, packed14, packed7, packed50, packed67, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
