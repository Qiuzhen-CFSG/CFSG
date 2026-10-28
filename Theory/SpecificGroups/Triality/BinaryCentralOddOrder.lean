module
public import Theory.SpecificGroups.Triality.BinaryThreeFreeSylow
public import Theory.SpecificGroups.Triality.BinaryParabolicThreeRank
import all Theory.SpecificGroups.Triality.BinaryThreeFreeSylow

/-!
# Odd subgroup orders in the binary triality central parabolic

The central local factor has order 2^12 times three and index dividing
seven in the full parabolic. Coprimality therefore bounds every odd
subgroup order by a divisor of 21. The internal import reuses the checked
local-factor order in this binary-triality family.

This is used by the original local Cartan consumer to bound a minus torus
placed in its actual containing component. No cyclicity or splitting is
assumed. Source: GLS3 sections 2.3--2.6 for the genuine root parabolics;
Aschbacher--Smith 5.1.13, printed pp.636--638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.BinaryCentralOddOrder
open Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "M" => BinaryCarrier 1 Nat.zero_lt_one

/-- Every odd subgroup of the actual central parabolic has order dividing 21. -/
theorem card_dvd_twentyOne (E : Subgroup M) (ho : Odd (Nat.card E))
    (hE : E ≤ parabolic P .central) : Nat.card E ∣ 21 := by
  let N := (localFactor P .central).subgroupOf (parabolic P .central)
  have hi : N.index ∣ 7 := localFactor_relIndex_dvd_seven P rfl .central
  have hc := N.card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (localFactor_le_parabolic P .central)).toEquiv,
    BinaryThreeFreeSylow.central_local_card] at hc
  have hd : Nat.card (parabolic P .central) ∣ 2^12 * 21 := by
    rw [←hc]
    exact (Nat.mul_dvd_mul_left 12288 hi)
  exact (ho.coprime_two_right.pow_right 12).dvd_of_dvd_mul_left
    ((card_dvd_of_le hE).trans hd)
end Triality.Standard.BinaryCentralOddOrder
end
