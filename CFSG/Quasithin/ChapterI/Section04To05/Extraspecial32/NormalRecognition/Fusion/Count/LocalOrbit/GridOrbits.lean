module

public import Theory.GroupAction.SymmetricThreeDiagonalGrid
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.LocalOrbit.Action

/-!
# The three- and six-point orbits of the local grid action

The symmetric-three grid theorem applies to the two factor homomorphisms of
`GridModel`, using the actual isomorphism H/Q ≃ S₃ from `Hypotheses`.
Equivariance and surjectivity of the literal quotient map identify the image
of every H-orbit with its grid orbit. Pulling back the short grid orbit gives
`CosetProfile`, the precise input consumed by the separate lifting argument.

This proves the orbit calculation conditional on `GridModel`. Its construction
from the source's quaternion-normality hypotheses remains with the geometric
assembly; no such normality or coordinate construction is assumed proved here.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 2.3(2)(b).
-/

namespace CFSG.Quasithin.Extraspecial32
open Subgroup Theory.GroupTheory
open Theory.GroupAction.SymmetricThreeDiagonalGrid
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace FusionCount.LocalOrbit

/-- Equivariant grid coordinates and the source's actual S₃ quotient give
precisely the central-coset orbit profile required by the lifting argument. -/
public theorem cosetProfile_of_gridModel (h : Hypotheses z) (m : GridModel z) : CosetProfile z := by
  obtain ⟨T, hT, hshort, hlong⟩ := exists_profile h.quotient_model.some
    m.left m.right m.left_three m.right_three
  have horbit (v : CentralInvolutionCosets (Core z)) :
      m.coordinates '' cosetOrbit z v = orbit m.left m.right (m.coordinates v) := by
    ext w
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk' (Core z) a, (m.equivariant a v).symm⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Core z) a
      exact ⟨cosetAction z b v, ⟨b, rfl⟩, m.equivariant b v⟩
  refine ⟨m.coordinates.symm '' T, ?_, ?_, ?_⟩
  · rw [Set.ncard_image_of_injective _ m.coordinates.symm.injective, hT]
  · intro v hv
    have hv' : m.coordinates v ∈ T := by simpa using hv
    apply (m.coordinates.image_eq_iff_eq _ _).mp
    rw [horbit, hshort _ hv']
    simp
  · intro v hv
    have hv' : m.coordinates v ∉ T := by simpa using hv
    rw [← Set.ncard_image_of_injective _ m.coordinates.injective, horbit]
    exact hlong _ hv'

end FusionCount.LocalOrbit
end CFSG.Quasithin.Extraspecial32
