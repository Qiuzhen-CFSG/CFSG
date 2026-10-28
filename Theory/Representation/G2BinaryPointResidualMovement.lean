module
public import Theory.Representation.G2BinaryCubicIntersection
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction

/-!
# Noncommuting cubics on the binary point seed

The point-parabolic cubic and its conjugate by the native C--D root pair
act noncommutatively on the marked three-space. One coordinate witnesses
this. Consequently an action through a cyclic quotient of order three
cannot realize this seed action. The original point-core movement in
Aschbacher--Smith 13.3.14(c), pp.891--892, is the source consumer.
-/

public section
open Subgroup
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.BinaryCore
local notation "α" => Restricted.NaturalCoordinates.action F
/-- Two literal residual cubics do not commute on the seed. -/
theorem point_residual_cubics_do_not_commute : α (movingActor * ((rootC 1 * rootD 1) * movingActor * (rootC 1 * rootD 1)⁻¹)) (Pi.single 1 1) ≠
    α (((rootC 1 * rootD 1) * movingActor * (rootC 1 * rootD 1)⁻¹) * movingActor) (Pi.single 1 1) := by
  intro hh
  have h0 := congrFun hh 0
  have hc : (rootC (1 : F) * rootD 1)⁻¹ = rootD 1 * rootC 1 := by
    rw [mul_inv_rev]
    have hd : (rootD (1:F))⁻¹ = rootD 1 := by
      apply inv_eq_of_mul_eq_one_right
      rw [rootD_add,show (1:F)+1=0 by decide,rootD_zero]
    have hc : (rootC (1:F))⁻¹ = rootC 1 := by
      apply inv_eq_of_mul_eq_one_right
      rw [rootC_add,show (1:F)+1=0 by decide,rootC_zero]
    rw [hd,hc]
  simp [hc,movingActor,map_mul,Module.End.mul_apply] at h0
end Atlas.G2.Natural.BinaryPointFlag
