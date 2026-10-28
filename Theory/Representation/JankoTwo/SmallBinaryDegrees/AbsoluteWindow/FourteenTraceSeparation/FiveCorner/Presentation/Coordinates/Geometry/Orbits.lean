module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Contracts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Orbits.Representatives
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Orbits.Reachability

/-!
# The literal J₂ orbit-walk certificate

Every saved representative word reaches its fixed root, and the retained
subgroup-power pair reaches each point from the root of its labeled orbit.
The compact tables are proved equal to the original arrays, and the cached
subgroup actions are proved equal to the full literal words.

This discharges exactly the OrbitCertificate input of
Geometry.rightCosetGeometry_of_checks. The independent edge certificate and
unconditional coset geometry assembly remain with that consumer.

Source: Presentation/source/README.md and Coordinates/source/README.md.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry

/-- Unconditional reachability on the unchanged fixed tables and word decoder. -/
theorem orbitCertificate : OrbitCertificate where
  representatives := Orbits.representatives
  orbits := Orbits.orbits

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry
