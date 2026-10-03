module

public import Theory.SpecificGroups.UnitaryThree.MatrixAction
public import Theory.SpecificGroups.UnitaryThree.MatrixGeneration

/-!
# Identification of the matrix and permutation models of SU₃(3)

The faithful action of the full determinant-one Hermitian isometry group has
image exactly `Model`. Indeed, the root, torus and swap matrices generate the
full matrix group, and their actions are precisely the defining generators of
the permutation model. Restricting the faithful action to this image gives an
isomorphism with the full matrix group.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Section VI.
-/

public section

namespace UnitaryThree

/-- The full matrix group acts onto the generated permutation model. -/
theorem matrixAction_range : matrixAction.range = Model := by
  rw [MonoidHom.range_eq_map, ← matrixGroup_generated, MonoidHom.map_closure]
  simp only [Set.image_union, ← Set.range_comp', Set.image_singleton,
    matrixAction_swap, matrixAction_root, matrixAction_torus, Model]

/-- The faithful matrix action identifies the full matrix and permutation groups. -/
noncomputable def matrixEquivModel : matrixGroup ≃* Model :=
  (MonoidHom.ofInjective matrixAction_injective).trans
    (MulEquiv.subgroupCongr matrixAction_range)

end UnitaryThree

end
