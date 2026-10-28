module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Reduction
public import Theory.Mathieu.M22.Properties.InvolutionFixedOrders

/-!
# The actual M₂₂ seven-action inspection

The certified degree-22 Sylow three action has odd centralizer. The resulting
fixed-order theorem for every abstract involution excludes a factor of nine,
hence either seven model. Cauchy's theorem then treats an arbitrary two-group
of automorphisms with its original common fixed subgroup.

Source: Aschbacher–Smith E.6.18, printed p.252.
-/
public section
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection

/-- Every involutory fixed subgroup has order not divisible by nine. -/
theorem mathieu_twenty_two : SevenActionInspection Sporadic.Mathieu.M22 :=
  of_involution_fixed_card Sporadic.Mathieu.m22_involution_not_2520_dvd_fixed_card

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
