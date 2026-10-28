module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.FourGeometry
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.PlaneCentralizer.LowerBound
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.PlaneCentralizer.UpperBound
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.PlaneCentralizer.SingleOrbit

/-!
# The full centralizer bound for the literal max4 plane

The relative lower bound and the marked single-orbit upper bound both equal
15728640. Hence the full ambient centralizer lies in max4, and FourGeometry
makes its normalizer strictly smaller than max4. The checked single-orbit
certificate supplies 1386 distinct actual conjugates in the original max2
subgroup, leaving only the literal marking as a premise. The parent exception
task supplies that marking and the conjugacy to the kernel candidate.

This supplies the plane-normalizer obstruction used in the J4 branch of
Aschbacher--Smith A.3.12, pp.47--48. Literal words and their source attribution
come from the imported ATLAS max2/max4 modules.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
open Subgroup Janko4 Janko4.LocalStructure.SymmetricLinear
open Janko4.LocalStructure.SymmetricLinear.NormalEight
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup


/-- The numerical bounds give full ambient containment, with the finite orbit
certificate still explicit. The marking is discharged by the parent exception task. -/
theorem max4Plane_centralizer_le_of_marking_and_orbit
    (hm : Max4EightCentralizer.Marking) (ho : PlaneCentralizer.SingleOrbitWitness) :
    centralizer (max4Plane : Set Model) ≤ max4Subgroup :=
  PlaneCentralizer.centralizer_le_of_card_le
    (PlaneCentralizer.centralizer_card_le_of_marking_and_orbit hm ho)

/-- Actual application to the strict plane-normalizer bound from FourGeometry. -/
theorem max4Plane_normalizer_lt_of_marking_and_orbit
    (hm : Max4EightCentralizer.Marking) (ho : PlaneCentralizer.SingleOrbitWitness) :
    normalizer (max4Plane : Set Model) < max4Subgroup :=
  max4Plane_normalizer_lt_of_centralizer
    (max4Plane_centralizer_le_of_marking_and_orbit hm ho)

/-- The full ambient centralizer of the literal plane lies in max4. The actual
single-orbit certificate discharges the only counting premise; only the first
two equations of the marking are used. -/
theorem max4Plane_centralizer_le_of_marking
    (hm : Max4EightCentralizer.Marking) :
    centralizer (max4Plane : Set Model) ≤ max4Subgroup :=
  max4Plane_centralizer_le_of_marking_and_orbit hm PlaneCentralizer.single_orbit_witness

/-- The strict plane-normalizer obstruction, conditional only on the literal
marking supplied by the parent exception argument. -/
theorem max4Plane_normalizer_lt_of_marking
    (hm : Max4EightCentralizer.Marking) :
    normalizer (max4Plane : Set Model) < max4Subgroup :=
  max4Plane_normalizer_lt_of_centralizer (max4Plane_centralizer_le_of_marking hm)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
