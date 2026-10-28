module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.ActorData

/-!
# Outputs required from the cubic coordinate calculation

This interface records the remaining natural-action calculation, separately
from the kernel, order and generation arguments. It asserts no existence.
Its producer must prove these statements from the actual image of Y and
literal conjugation compatibility; the CaseOne assembly must supply that
producer before it proves existence of a plane actor pair.

The index denotes the centralized plane, so the moving plane always has
the other index. Both labels are retained symmetrically.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the plane
construction on printed pp.1121–1122 and 15.3.39–40 on pp.1137–1138.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G]

/-- Required conclusions of the literal cubic coordinate calculation. -/
structure FullActionCoordinateFacts {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (Y : Subgroup G) : Prop where
  image_card : ∀ i : OrthogonalPlaneIndex,
    Nat.card (d.image (centralizingFactor Y (d.plane i))) = 3
  commutator : ∀ i j : OrthogonalPlaneIndex, i ≠ j →
    ⁅V, centralizingFactor Y (d.plane i)⁆ = d.plane j
  commutator_self : ∀ i j : OrthogonalPlaneIndex, i ≠ j →
    ⁅d.plane j, centralizingFactor Y (d.plane i)⁆ = d.plane j

end CFSG.Quasithin.Chapter15.Section03.RankTwo
