module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.Blocks

/-! Full-permutation certificates for lower J3 B-row seeds, batch 5.
The shared block specifications reduce these to the published witnesses.
Source: ATLAS J3G1-p6156B0 and Order/data/witnesses.json. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem seed2123 : L0Gen 1 * L0Rep 2123 =
    L0Rep (L0Act 1 2123) * evalWord L1Gen (L0Factor 1 2123) := by
  apply step_of_packed_check rawBlock_spec 2123 [38, 38, 44, 38, 37] [14, 14, 14, 14, 20] [packed38, packed38, packed44, packed38, packed37] [packed14, packed14, packed14, packed14, packed20]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2129 : L0Gen 1 * L0Rep 2129 =
    L0Rep (L0Act 1 2129) * evalWord L1Gen (L0Factor 1 2129) := by
  apply step_of_packed_check rawBlock_spec 2129 [38, 46, 44, 38, 37] [13, 1, 1, 1, 17, 64, 61, 72] [packed38, packed46, packed44, packed38, packed37] [packed13, packed1, packed1, packed1, packed17, packed64, packed61, packed72]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2131 : L0Gen 1 * L0Rep 2131 =
    L0Rep (L0Act 1 2131) * evalWord L1Gen (L0Factor 1 2131) := by
  apply step_of_packed_check rawBlock_spec 2131 [40, 38, 40, 38, 37] [13, 14, 2, 14, 22, 64, 64, 61, 72, 60] [packed40, packed38, packed40, packed38, packed37] [packed13, packed14, packed2, packed14, packed22, packed64, packed64, packed61, packed72, packed60]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2133 : L0Gen 1 * L0Rep 2133 =
    L0Rep (L0Act 1 2133) * evalWord L1Gen (L0Factor 1 2133) := by
  apply step_of_packed_check rawBlock_spec 2133 [38, 40, 40, 38, 37] [14, 1, 1, 2, 8, 61, 54, 63, 53] [packed38, packed40, packed40, packed38, packed37] [packed14, packed1, packed1, packed2, packed8, packed61, packed54, packed63, packed53]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2142 : L0Gen 1 * L0Rep 2142 =
    L0Rep (L0Act 1 2142) * evalWord L1Gen (L0Factor 1 2142) := by
  apply step_of_packed_check rawBlock_spec 2142 [38, 44, 44, 44, 37] [2, 2, 13, 1, 8] [packed38, packed44, packed44, packed44, packed37] [packed2, packed2, packed13, packed1, packed8]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2143 : L0Gen 1 * L0Rep 2143 =
    L0Rep (L0Act 1 2143) * evalWord L1Gen (L0Factor 1 2143) := by
  apply step_of_packed_check rawBlock_spec 2143 [40, 44, 44, 44, 37] [13, 1, 2, 14, 8, 68, 64, 64, 61] [packed40, packed44, packed44, packed44, packed37] [packed13, packed1, packed2, packed14, packed8, packed68, packed64, packed64, packed61]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2146 : L0Gen 1 * L0Rep 2146 =
    L0Rep (L0Act 1 2146) * evalWord L1Gen (L0Factor 1 2146) := by
  apply step_of_packed_check rawBlock_spec 2146 [38, 44, 40, 44, 37] [1, 1, 13, 13, 9, 61, 54, 67, 57, 48] [packed38, packed44, packed40, packed44, packed37] [packed1, packed1, packed13, packed13, packed9, packed61, packed54, packed67, packed57, packed48]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

set_option maxRecDepth 40000 in
public theorem seed2148 : L0Gen 1 * L0Rep 2148 =
    L0Rep (L0Act 1 2148) * evalWord L1Gen (L0Factor 1 2148) := by
  apply step_of_packed_check rawBlock_spec 2148 [38, 40, 40, 44, 37] [2, 14, 1, 2, 3, 57, 54, 64, 63, 47] [packed38, packed40, packed40, packed44, packed37] [packed2, packed14, packed1, packed2, packed3, packed57, packed54, packed64, packed63, packed47]
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
