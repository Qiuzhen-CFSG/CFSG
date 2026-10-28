module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 1.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed695 : L0Gen 1 * L0Rep 695 =
    L0Rep (L0Act 1 695) * evalWord L1Gen (L0Factor 1 695) := by
  apply step_of_packed_check rawBlock_spec 695 [40, 46, 44, 43] [14, 14, 2, 9, 64, 61, 57, 47] [packed40, packed46, packed44, packed43] [packed14, packed14, packed2, packed9, packed64, packed61, packed57, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed697 : L0Gen 1 * L0Rep 697 =
    L0Rep (L0Act 1 697) * evalWord L1Gen (L0Factor 1 697) := by
  apply step_of_packed_check rawBlock_spec 697 [40, 44, 40, 43] [14, 13, 2, 17, 67, 67, 55, 71] [packed40, packed44, packed40, packed43] [packed14, packed13, packed2, packed17, packed67, packed67, packed55, packed71]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed807 : L0Gen 1 * L0Rep 807 =
    L0Rep (L0Act 1 807) * evalWord L1Gen (L0Factor 1 807) := by
  apply step_of_packed_check rawBlock_spec 807 [38, 46, 38, 40] [2, 1, 14, 21, 68, 64, 64, 60] [packed38, packed46, packed38, packed40] [packed2, packed1, packed14, packed21, packed68, packed64, packed64, packed60]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed820 : L0Gen 1 * L0Rep 820 =
    L0Rep (L0Act 1 820) * evalWord L1Gen (L0Factor 1 820) := by
  apply step_of_packed_check rawBlock_spec 820 [40, 44, 40, 40] [2, 13, 13, 10, 73, 57, 73, 72, 63, 47] [packed40, packed44, packed40, packed40] [packed2, packed13, packed13, packed10, packed73, packed57, packed73, packed72, packed63, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed821 : L0Gen 1 * L0Rep 821 =
    L0Rep (L0Act 1 821) * evalWord L1Gen (L0Factor 1 821) := by
  apply step_of_packed_check rawBlock_spec 821 [38, 40, 40, 40] [1, 1, 14, 18, 61, 54, 67, 67] [packed38, packed40, packed40, packed40] [packed1, packed1, packed14, packed18, packed61, packed54, packed67, packed67]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed830 : L0Gen 1 * L0Rep 830 =
    L0Rep (L0Act 1 830) * evalWord L1Gen (L0Factor 1 830) := by
  apply step_of_packed_check rawBlock_spec 830 [40, 44, 38, 46] [14, 1, 2, 16, 54, 67, 67, 67, 59] [packed40, packed44, packed38, packed46] [packed14, packed1, packed2, packed16, packed54, packed67, packed67, packed67, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1203 : L0Gen 1 * L0Rep 1203 =
    L0Rep (L0Act 1 1203) * evalWord L1Gen (L0Factor 1 1203) := by
  apply step_of_packed_check rawBlock_spec 1203 [38, 38, 44, 38, 35] [14, 13, 1, 2, 63, 55, 50, 61, 47] [packed38, packed38, packed44, packed38, packed35] [packed14, packed13, packed1, packed2, packed63, packed55, packed50, packed61, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed1220 : L0Gen 1 * L0Rep 1220 =
    L0Rep (L0Act 1 1220) * evalWord L1Gen (L0Factor 1 1220) := by
  apply step_of_packed_check rawBlock_spec 1220 [38, 38, 38, 44, 35] [1, 13, 2, 2, 57, 54, 64, 63, 58] [packed38, packed38, packed38, packed44, packed35] [packed1, packed13, packed2, packed2, packed57, packed54, packed64, packed63, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
