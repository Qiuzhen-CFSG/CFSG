module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Setup
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.WordCalculus.Conjugation
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.WordCalculus.Kernel
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.WordCalculus.Square

/-!
# Certified word calculus for the six-coordinate presentation interval

The core is normal in the presented group, and the six quotient generators
are commuting involutions. Their binary products give envelope coverage and
the xor multiplication law. The literal conjugation relations give the five
displacements. Checked products of the eleven marked kernel words prove both
kernel inclusions. Finally, normal-form uniqueness at order 2^21 detects the
two square coordinates.

This discharges all six fields consumed by `closedCoordinates_of_subgroup`
and `catalogue_in_interval`. Localization of arbitrary outside-kernel normal
elementary subgroups is the separate input of the parent catalogue assembly.

Source context: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988),
pp.484–510; the literal PC-word provenance in
`SylowNormalEights/source/README.md` and `OutsideKernelOrders/source/README.md`.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue
open Janko4.LocalStructure.SylowNormalEights Presentation

/-- The actual presentation word calculus, with only normal-form consistency assumed. -/
theorem wordCalculus_of_card (hcard : Nat.card Carrier = 2 ^ 21) : WordCalculus where
  core_kernel := WordProof.core_kernel
  cover := WordProof.envelope_cover
  mul a b := by
    apply WordProof.q_eq_one.mp
    rw [map_mul, map_mul, map_inv]
    change WordProof.v a * WordProof.v b * (WordProof.v (codeXor a b))⁻¹ = 1
    rw [WordProof.v_mul, mul_inv_cancel]
  conjugate := WordProof.conjugate_mem
  square := WordProof.square_zero_of_card hcard
  kernel := WordProof.slice_kernel

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue
