module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates.Transport
public import Theory.GroupTheory.BinarySquareForm

/-!
# Quadratic square descent for the actual M₁₂ cover core

The coordinate map from `CoreLiftData` has the actual core center as kernel.
That center is the join of the fourth-orbit root square and the ambient
order-two center, and every central element squares to one. The general
binary square descent therefore constructs a quadratic form with zero set
precisely the representatives whose squares lie in the chosen cyclic group.

The transport results then supply the invariance and fusion markings. The
construction of `CoreLiftData` from the original cover hypotheses remains
with the source assembly; no actor or quadratic-form premise is added here.

Source: Aschbacher–Smith, I.2.2(5), printed p.412 / PDF p.423.
-/

public section
open Subgroup Theory.LinearAlgebra.BinaryCubicOrbits
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
namespace CoverCoordinates.CoreLiftData
variable {K : Type*} [Group K]
variable {e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12} {u : K}
variable (d : CoverCoordinates.CoreLiftData e u)
    (m : Sporadic.Mathieu.M12SmallPair.CoverOrbitData)

/-- The genuine quadratic square map on the pulled-back model coordinates,
modulo the chosen fourth-orbit square. -/
theorem exists_square_form (hZ : Nat.card (center K) = 2) :
    ∃ q : QuadraticForm (ZMod 2) Space,
      ∀ r : centralizerCore u,
        q (d.coordinates m r).toAdd = 0 ↔ r ^ 2 ∈ zpowers (d.root m ^ 2) := by
  exact Theory.GroupTheory.BinarySquareForm.exists_quadraticForm
    (d.coordinates m) (d.coordinates_ker m) (d.coordinates_surjective m)
    d.center_square (d.root m ^ 2) (d.square_central m _)
    ((center K).subgroupOf (centralizerCore u)) (d.center_eq m)
    (d.ambient_center_card hZ) (d.root_square_not_mem_ambient_center m)

include d in
/-- All marked coordinates now follow from the uncoordinatized core data.
The independent core producer remains the source-theorem assembly's input. -/
theorem marked_coordinates [Finite K] (hZ : Nat.card (center K) = 2)
    (hu : CoverCoordinates.projection e u = Sporadic.Mathieu.M12SmallPair.z) :
    orderOf u = 2 ∧ Nonempty (MarkedSquareCoordinates e u m) := by
  obtain ⟨q, hq⟩ := d.exists_square_form m hZ
  exact d.marked_of_square_form m hZ hu q hq

end CoverCoordinates.CoreLiftData
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
