module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 29.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3870 : L0Gen 1 * L0Rep 3870 =
    L0Rep (L0Act 1 3870) * evalWord L1Gen (L0Factor 1 3870) := by
  apply step_of_packed_check rawBlock_spec 3870 [38, 38, 46, 46, 40, 42] [2, 2, 1, 14, 14, 50, 55, 73, 56] [packed38, packed38, packed46, packed46, packed40, packed42] [packed2, packed2, packed1, packed14, packed14, packed50, packed55, packed73, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3875 : L0Gen 1 * L0Rep 3875 =
    L0Rep (L0Act 1 3875) * evalWord L1Gen (L0Factor 1 3875) := by
  apply step_of_packed_check rawBlock_spec 3875 [38, 46, 38, 44, 46, 42] [2, 14, 1, 13, 14, 33, 61, 57, 57, 55, 47] [packed38, packed46, packed38, packed44, packed46, packed42] [packed2, packed14, packed1, packed13, packed14, packed33, packed61, packed57, packed57, packed55, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3876 : L0Gen 1 * L0Rep 3876 =
    L0Rep (L0Act 1 3876) * evalWord L1Gen (L0Factor 1 3876) := by
  apply step_of_packed_check rawBlock_spec 3876 [40, 38, 44, 44, 46, 42] [2, 2, 13, 1, 2, 33, 61, 72, 64, 63, 60] [packed40, packed38, packed44, packed44, packed46, packed42] [packed2, packed2, packed13, packed1, packed2, packed33, packed61, packed72, packed64, packed63, packed60]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3899 : L0Gen 1 * L0Rep 3899 =
    L0Rep (L0Act 1 3899) * evalWord L1Gen (L0Factor 1 3899) := by
  apply step_of_packed_check rawBlock_spec 3899 [38, 38, 40, 46, 46, 42] [1, 2, 2, 13, 14, 33, 64, 67, 64, 59] [packed38, packed38, packed40, packed46, packed46, packed42] [packed1, packed2, packed2, packed13, packed14, packed33, packed64, packed67, packed64, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3901 : L0Gen 1 * L0Rep 3901 =
    L0Rep (L0Act 1 3901) * evalWord L1Gen (L0Factor 1 3901) := by
  apply step_of_packed_check rawBlock_spec 3901 [38, 44, 40, 46, 46, 42] [1, 1, 2, 13, 2, 30, 73, 50, 67, 52] [packed38, packed44, packed40, packed46, packed46, packed42] [packed1, packed1, packed2, packed13, packed2, packed30, packed73, packed50, packed67, packed52]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3903 : L0Gen 1 * L0Rep 3903 =
    L0Rep (L0Act 1 3903) * evalWord L1Gen (L0Factor 1 3903) := by
  apply step_of_packed_check rawBlock_spec 3903 [38, 40, 40, 46, 46, 42] [14, 1, 14, 13, 1, 26, 55, 50, 67, 57] [packed38, packed40, packed40, packed46, packed46, packed42] [packed14, packed1, packed14, packed13, packed1, packed26, packed55, packed50, packed67, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4669 : L0Gen 1 * L0Rep 4669 =
    L0Rep (L0Act 1 4669) * evalWord L1Gen (L0Factor 1 4669) := by
  apply step_of_packed_check rawBlock_spec 4669 [38, 40, 44, 44, 38, 37] [2, 13, 2, 14, 1, 5, 67, 56] [packed38, packed40, packed44, packed44, packed38, packed37] [packed2, packed13, packed2, packed14, packed1, packed5, packed67, packed56]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed4671 : L0Gen 1 * L0Rep 4671 =
    L0Rep (L0Act 1 4671) * evalWord L1Gen (L0Factor 1 4671) := by
  apply step_of_packed_check rawBlock_spec 4671 [40, 46, 40, 44, 38, 37] [1, 14, 1, 13, 1, 8, 61, 73, 73, 47] [packed40, packed46, packed40, packed44, packed38, packed37] [packed1, packed14, packed1, packed13, packed1, packed8, packed61, packed73, packed73, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
