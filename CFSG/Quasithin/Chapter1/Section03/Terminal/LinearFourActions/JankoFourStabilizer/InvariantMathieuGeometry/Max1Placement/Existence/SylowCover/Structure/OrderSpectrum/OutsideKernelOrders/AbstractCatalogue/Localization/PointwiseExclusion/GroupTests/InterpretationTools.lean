module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Basic

/-! Polynomial sums can be evaluated in bounded pieces, retaining the balanced
XOR syntax of Boolean.equations. This is ordinary fold associativity. -/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests
open PointwiseCalculation Symbolic

theorem polyValue_append (p q : Poly) (v : Monomial) :
    polyValue (p ++ q) v = (polyValue p v ^^ polyValue q v) := by
  induction p with
  | nil => simp
  | cons m p ih =>
    simp only [List.cons_append, polyValue_cons, ih, Bool.xor_assoc]

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests
