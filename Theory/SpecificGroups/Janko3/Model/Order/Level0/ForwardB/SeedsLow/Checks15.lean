module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 15.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed2580 : L0Gen 1 * L0Rep 2580 =
    L0Rep (L0Act 1 2580) * evalWord L1Gen (L0Factor 1 2580) := by
  apply step_of_packed_check rawBlock_spec 2580 [38, 44, 46, 44, 46] [14, 1, 2, 1, 4, 55, 75, 57, 50, 61] [packed38, packed44, packed46, packed44, packed46] [packed14, packed1, packed2, packed1, packed4, packed55, packed75, packed57, packed50, packed61]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2587 : L0Gen 1 * L0Rep 2587 =
    L0Rep (L0Act 1 2587) * evalWord L1Gen (L0Factor 1 2587) := by
  apply step_of_packed_check rawBlock_spec 2587 [40, 38, 40, 40, 46] [13, 2, 2, 14, 18, 61, 73, 75, 49] [packed40, packed38, packed40, packed40, packed46] [packed13, packed2, packed2, packed14, packed18, packed61, packed73, packed75, packed49]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3354 : L0Gen 1 * L0Rep 3354 =
    L0Rep (L0Act 1 3354) * evalWord L1Gen (L0Factor 1 3354) := by
  apply step_of_packed_check rawBlock_spec 3354 [38, 44, 40, 38, 38, 35] [2, 14, 14, 1, 2, 73, 72, 63, 57, 69] [packed38, packed44, packed40, packed38, packed38, packed35] [packed2, packed14, packed14, packed1, packed2, packed73, packed72, packed63, packed57, packed69]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3358 : L0Gen 1 * L0Rep 3358 =
    L0Rep (L0Act 1 3358) * evalWord L1Gen (L0Factor 1 3358) := by
  apply step_of_packed_check rawBlock_spec 3358 [40, 46, 40, 38, 38, 35] [14, 13, 14, 1, 14, 27, 64, 63, 68, 64, 62] [packed40, packed46, packed40, packed38, packed38, packed35] [packed14, packed13, packed14, packed1, packed14, packed27, packed64, packed63, packed68, packed64, packed62]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3359 : L0Gen 1 * L0Rep 3359 =
    L0Rep (L0Act 1 3359) * evalWord L1Gen (L0Factor 1 3359) := by
  apply step_of_packed_check rawBlock_spec 3359 [38, 44, 46, 38, 38, 35] [14, 14, 1, 1, 14, 33, 67, 57, 48] [packed38, packed44, packed46, packed38, packed38, packed35] [packed14, packed14, packed1, packed1, packed14, packed33, packed67, packed57, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3360 : L0Gen 1 * L0Rep 3360 =
    L0Rep (L0Act 1 3360) * evalWord L1Gen (L0Factor 1 3360) := by
  apply step_of_packed_check rawBlock_spec 3360 [40, 44, 46, 38, 38, 35] [2, 14, 14, 13, 14, 27, 64, 64, 64, 61] [packed40, packed44, packed46, packed38, packed38, packed35] [packed2, packed14, packed14, packed13, packed14, packed27, packed64, packed64, packed64, packed61]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3370 : L0Gen 1 * L0Rep 3370 =
    L0Rep (L0Act 1 3370) * evalWord L1Gen (L0Factor 1 3370) := by
  apply step_of_packed_check rawBlock_spec 3370 [38, 40, 40, 44, 38, 35] [13, 14, 2, 2, 1, 51, 61, 73, 72, 63, 58] [packed38, packed40, packed40, packed44, packed38, packed35] [packed13, packed14, packed2, packed2, packed1, packed51, packed61, packed73, packed72, packed63, packed58]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3380 : L0Gen 1 * L0Rep 3380 =
    L0Rep (L0Act 1 3380) * evalWord L1Gen (L0Factor 1 3380) := by
  apply step_of_packed_check rawBlock_spec 3380 [40, 38, 38, 46, 38, 35] [1, 14, 2, 14, 13, 51, 64, 64, 64, 63, 65] [packed40, packed38, packed38, packed46, packed38, packed35] [packed1, packed14, packed2, packed14, packed13, packed51, packed64, packed64, packed64, packed63, packed65]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed3382 : L0Gen 1 * L0Rep 3382 =
    L0Rep (L0Act 1 3382) * evalWord L1Gen (L0Factor 1 3382) := by
  apply step_of_packed_check rawBlock_spec 3382 [40, 44, 38, 46, 38, 35] [13, 2, 1, 14, 1, 31, 57, 55, 75, 57] [packed40, packed44, packed38, packed46, packed38, packed35] [packed13, packed2, packed1, packed14, packed1, packed31, packed57, packed55, packed75, packed57]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
