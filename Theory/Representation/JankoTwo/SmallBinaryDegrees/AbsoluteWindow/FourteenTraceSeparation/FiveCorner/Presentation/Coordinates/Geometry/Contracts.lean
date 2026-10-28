module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Model

/-!
# Finite inputs for the literal J₂ right-coset geometry

The Schreier input consists only of actual group elements, an identity row,
and generator-edge equations. The independent orbit input concerns walks on
the fixed tables. Geometry.lean proves coverage and uniqueness from generation
and the existing group order, and derives all fields of RightCosetGeometry.
Neither finite certificate is asserted by these definitions.

Source: Presentation/source/README.md and Coordinates/source/README.md;
the literal corner application is Guralnick--Malle Proposition 5.1.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry
open Sporadic.LeechRelated.J2

/-- Actual carrier representatives and their right generator transitions.
No injectivity, coset identification, or coverage is assumed. -/
structure SchreierCertificate where
  repr : Point → Carrier
  at_zero : repr 0 = 1
  edge : ∀ x l, ∃ p : subgroup, repr x * letter l = (p : Carrier) * repr (step l x)

/-- Finite reachability checks on the fixed tables: the saved words reach their
roots, and the 25 subgroup power words reach every point from its orbit root. -/
structure OrbitCertificate : Prop where
  representatives : ∀ i, walk (representativeWord i) 0 = root i
  orbits : ∀ x, ∃ t : CoefficientTheory.PowerIndex,
    walk (subgroupWord t) (root (orbit x)) = x

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry
