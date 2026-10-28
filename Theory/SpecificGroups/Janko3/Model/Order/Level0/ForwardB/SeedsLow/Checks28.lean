module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 28.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed3836 : L0Gen 1 * L0Rep 3836 =
    L0Rep (L0Act 1 3836) * evalWord L1Gen (L0Factor 1 3836) := by
  apply step_of_packed_check rawBlock_spec 3836 [38, 38, 40, 46, 44, 42] [14, 14, 13, 14, 13, 25, 50, 67, 60] [packed38, packed38, packed40, packed46, packed44, packed42] [packed14, packed14, packed13, packed14, packed13, packed25, packed50, packed67, packed60]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3837 : L0Gen 1 * L0Rep 3837 =
    L0Rep (L0Act 1 3837) * evalWord L1Gen (L0Factor 1 3837) := by
  apply step_of_packed_check rawBlock_spec 3837 [40, 38, 40, 46, 44, 42] [2, 2, 2, 14, 14, 30, 51, 64, 64, 63, 47] [packed40, packed38, packed40, packed46, packed44, packed42] [packed2, packed2, packed2, packed14, packed14, packed30, packed51, packed64, packed64, packed63, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3840 : L0Gen 1 * L0Rep 3840 =
    L0Rep (L0Act 1 3840) * evalWord L1Gen (L0Factor 1 3840) := by
  apply step_of_packed_check rawBlock_spec 3840 [38, 40, 46, 46, 44, 42] [2, 13, 2, 14, 2, 57, 57, 57, 57, 50, 58] [packed38, packed40, packed46, packed46, packed44, packed42] [packed2, packed13, packed2, packed14, packed2, packed57, packed57, packed57, packed57, packed50, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3844 : L0Gen 1 * L0Rep 3844 =
    L0Rep (L0Act 1 3844) * evalWord L1Gen (L0Factor 1 3844) := by
  apply step_of_packed_check rawBlock_spec 3844 [40, 40, 38, 38, 40, 42] [14, 13, 1, 13, 14, 50, 55, 50, 61, 70] [packed40, packed40, packed38, packed38, packed40, packed42] [packed14, packed13, packed1, packed13, packed14, packed50, packed55, packed50, packed61, packed70]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3857 : L0Gen 1 * L0Rep 3857 =
    L0Rep (L0Act 1 3857) * evalWord L1Gen (L0Factor 1 3857) := by
  apply step_of_packed_check rawBlock_spec 3857 [40, 38, 40, 40, 40, 42] [2, 2, 1, 14, 13, 69] [packed40, packed38, packed40, packed40, packed40, packed42] [packed2, packed2, packed1, packed14, packed13, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3862 : L0Gen 1 * L0Rep 3862 =
    L0Rep (L0Act 1 3862) * evalWord L1Gen (L0Factor 1 3862) := by
  apply step_of_packed_check rawBlock_spec 3862 [38, 38, 46, 40, 40, 42] [1, 1, 14, 13, 1, 26, 57, 57, 57, 55, 47] [packed38, packed38, packed46, packed40, packed40, packed42] [packed1, packed1, packed14, packed13, packed1, packed26, packed57, packed57, packed57, packed55, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3868 : L0Gen 1 * L0Rep 3868 =
    L0Rep (L0Act 1 3868) * evalWord L1Gen (L0Factor 1 3868) := by
  apply step_of_packed_check rawBlock_spec 3868 [38, 46, 40, 46, 40, 42] [13, 2, 13, 13, 14, 27, 63, 55] [packed38, packed46, packed40, packed46, packed40, packed42] [packed13, packed2, packed13, packed13, packed14, packed27, packed63, packed55]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3869 : L0Gen 1 * L0Rep 3869 =
    L0Rep (L0Act 1 3869) * evalWord L1Gen (L0Factor 1 3869) := by
  apply step_of_packed_check rawBlock_spec 3869 [40, 46, 40, 46, 40, 42] [1, 2, 1, 13, 1, 31, 72, 64, 63, 59] [packed40, packed46, packed40, packed46, packed40, packed42] [packed1, packed2, packed1, packed13, packed1, packed31, packed72, packed64, packed63, packed59]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
