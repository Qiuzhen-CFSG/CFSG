module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 6.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed2150 : L0Gen 1 * L0Rep 2150 =
    L0Rep (L0Act 1 2150) * evalWord L1Gen (L0Factor 1 2150) := by
  apply step_of_packed_check rawBlock_spec 2150 [38, 46, 40, 44, 37] [1, 13, 2, 14, 15, 55, 72, 63, 54] [packed38, packed46, packed40, packed44, packed37] [packed1, packed13, packed2, packed14, packed15, packed55, packed72, packed63, packed54]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2155 : L0Gen 1 * L0Rep 2155 =
    L0Rep (L0Act 1 2155) * evalWord L1Gen (L0Factor 1 2155) := by
  apply step_of_packed_check rawBlock_spec 2155 [38, 40, 46, 44, 37] [2, 13, 2, 1, 15, 67, 67, 64, 66] [packed38, packed40, packed46, packed44, packed37] [packed2, packed13, packed2, packed1, packed15, packed67, packed67, packed64, packed66]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2161 : L0Gen 1 * L0Rep 2161 =
    L0Rep (L0Act 1 2161) * evalWord L1Gen (L0Factor 1 2161) := by
  apply step_of_packed_check rawBlock_spec 2161 [40, 40, 38, 40, 37] [2, 13, 13, 14, 7, 73, 57, 72, 64] [packed40, packed40, packed38, packed40, packed37] [packed2, packed13, packed13, packed14, packed7, packed73, packed57, packed72, packed64]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2164 : L0Gen 1 * L0Rep 2164 =
    L0Rep (L0Act 1 2164) * evalWord L1Gen (L0Factor 1 2164) := by
  apply step_of_packed_check rawBlock_spec 2164 [38, 38, 44, 40, 37] [13, 13, 13, 1, 15, 67, 57, 69] [packed38, packed38, packed44, packed40, packed37] [packed13, packed13, packed13, packed1, packed15, packed67, packed57, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2165 : L0Gen 1 * L0Rep 2165 =
    L0Rep (L0Act 1 2165) * evalWord L1Gen (L0Factor 1 2165) := by
  apply step_of_packed_check rawBlock_spec 2165 [38, 44, 44, 40, 37] [14, 14, 14, 2, 21, 64, 63, 57] [packed38, packed44, packed44, packed40, packed37] [packed14, packed14, packed14, packed2, packed21, packed64, packed63, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2171 : L0Gen 1 * L0Rep 2171 =
    L0Rep (L0Act 1 2171) * evalWord L1Gen (L0Factor 1 2171) := by
  apply step_of_packed_check rawBlock_spec 2171 [40, 44, 40, 40, 37] [13, 14, 14, 2, 23, 72, 67, 57, 54, 64] [packed40, packed44, packed40, packed40, packed37] [packed13, packed14, packed14, packed2, packed23, packed72, packed67, packed57, packed54, packed64]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2173 : L0Gen 1 * L0Rep 2173 =
    L0Rep (L0Act 1 2173) * evalWord L1Gen (L0Factor 1 2173) := by
  apply step_of_packed_check rawBlock_spec 2173 [40, 40, 40, 40, 37] [2, 2, 2, 2, 11] [packed40, packed40, packed40, packed40, packed37] [packed2, packed2, packed2, packed2, packed11]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2174 : L0Gen 1 * L0Rep 2174 =
    L0Rep (L0Act 1 2174) * evalWord L1Gen (L0Factor 1 2174) := by
  apply step_of_packed_check rawBlock_spec 2174 [38, 46, 40, 40, 37] [13, 13, 13, 14, 8, 57, 50, 67, 61, 52] [packed38, packed46, packed40, packed40, packed37] [packed13, packed13, packed13, packed14, packed8, packed57, packed50, packed67, packed61, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
