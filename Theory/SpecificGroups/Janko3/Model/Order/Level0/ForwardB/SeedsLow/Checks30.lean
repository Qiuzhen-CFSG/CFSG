module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 30.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed4673 : L0Gen 1 * L0Rep 4673 =
    L0Rep (L0Act 1 4673) * evalWord L1Gen (L0Factor 1 4673) := by
  apply step_of_packed_check rawBlock_spec 4673 [38, 46, 38, 40, 38, 37] [2, 2, 1, 14, 13, 9, 67, 55, 51, 64, 60] [packed38, packed46, packed38, packed40, packed38, packed37] [packed2, packed2, packed1, packed14, packed13, packed9, packed67, packed55, packed51, packed64, packed60]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4675 : L0Gen 1 * L0Rep 4675 =
    L0Rep (L0Act 1 4675) * evalWord L1Gen (L0Factor 1 4675) := by
  apply step_of_packed_check rawBlock_spec 4675 [38, 40, 44, 40, 38, 37] [2, 1, 14, 14, 2, 5, 64, 64, 64, 67, 47] [packed38, packed40, packed44, packed40, packed38, packed37] [packed2, packed1, packed14, packed14, packed2, packed5, packed64, packed64, packed64, packed67, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4676 : L0Gen 1 * L0Rep 4676 =
    L0Rep (L0Act 1 4676) * evalWord L1Gen (L0Factor 1 4676) := by
  apply step_of_packed_check rawBlock_spec 4676 [40, 40, 44, 40, 38, 37] [13, 13, 2, 14, 1, 10] [packed40, packed40, packed44, packed40, packed38, packed37] [packed13, packed13, packed2, packed14, packed1, packed10]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4677 : L0Gen 1 * L0Rep 4677 =
    L0Rep (L0Act 1 4677) * evalWord L1Gen (L0Factor 1 4677) := by
  apply step_of_packed_check rawBlock_spec 4677 [38, 44, 40, 40, 38, 37] [2, 13, 2, 14, 14, 17, 64, 61, 73, 75, 48] [packed38, packed44, packed40, packed40, packed38, packed37] [packed2, packed13, packed2, packed14, packed14, packed17, packed64, packed61, packed73, packed75, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4678 : L0Gen 1 * L0Rep 4678 =
    L0Rep (L0Act 1 4678) * evalWord L1Gen (L0Factor 1 4678) := by
  apply step_of_packed_check rawBlock_spec 4678 [40, 44, 40, 40, 38, 37] [13, 1, 2, 2, 14, 3, 57, 57, 54, 65] [packed40, packed44, packed40, packed40, packed38, packed37] [packed13, packed1, packed2, packed2, packed14, packed3, packed57, packed57, packed54, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4679 : L0Gen 1 * L0Rep 4679 =
    L0Rep (L0Act 1 4679) * evalWord L1Gen (L0Factor 1 4679) := by
  apply step_of_packed_check rawBlock_spec 4679 [40, 46, 40, 40, 38, 37] [1, 2, 13, 1, 14, 3, 64, 61, 73, 73, 48] [packed40, packed46, packed40, packed40, packed38, packed37] [packed1, packed2, packed13, packed1, packed14, packed3, packed64, packed61, packed73, packed73, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4683 : L0Gen 1 * L0Rep 4683 =
    L0Rep (L0Act 1 4683) * evalWord L1Gen (L0Factor 1 4683) := by
  apply step_of_packed_check rawBlock_spec 4683 [38, 46, 44, 46, 38, 37] [2, 13, 14, 14, 14, 21, 64, 63, 55, 72, 58] [packed38, packed46, packed44, packed46, packed38, packed37] [packed2, packed13, packed14, packed14, packed14, packed21, packed64, packed63, packed55, packed72, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4692 : L0Gen 1 * L0Rep 4692 =
    L0Rep (L0Act 1 4692) * evalWord L1Gen (L0Factor 1 4692) := by
  apply step_of_packed_check rawBlock_spec 4692 [40, 40, 44, 40, 44, 37] [14, 2, 13, 14, 13, 7, 50, 61, 57, 69] [packed40, packed40, packed44, packed40, packed44, packed37] [packed14, packed2, packed13, packed14, packed13, packed7, packed50, packed61, packed57, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
