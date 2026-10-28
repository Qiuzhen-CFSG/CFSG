module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.MathieuTwentyFour
public import Theory.Mathieu.M24.Properties.InvolutionFixedOrders

/-!
# The complete M₂₄ seven-component inspection

The fixed-order theorem supplies the last marked centralizer bound on the
actual Witt-design carrier and its full automorphism group.
Source: Aschbacher–Smith E.6.18, printed p.252.
-/
public section
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection

theorem mathieu_twenty_four : SevenActionInspection Sporadic.Mathieu.M24 :=
  m24_of_second_centralizer Sporadic.Mathieu.M24InvolutionFixedOrders.centralizer_twoB_not_nine

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
