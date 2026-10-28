module

public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence

/-!
# Coordinates for an invariant orthogonal three-line decomposition

A frame is the union of the punctured lines through the columns of an
invertible matrix. If the frame is invariant and its Gram matrix is the
identity, change of basis places the subgroup in the concrete monomial
subgroup. The same change of basis descends to the actual projective image;
in that case invariance is required of the full special-unitary preimage.

This module only converts a geometric witness. Existence of an invariant
frame is the solvable representation argument in GLS3, proof of Theorem
6.5.3(a)–(d), particularly equation (6.5.1). It is not assumed to follow
from an abstract subgroup-family label.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram
open scoped Pointwise

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement

variable {E : Type*} [Field E] {J : HermitianForm 3 E}

/-- The actual natural action preserves the three lines of the given basis. -/
@[expose] def PreservesFrame (H : Subgroup J.specialSubgroup) (C : GL (Fin 3) E) : Prop :=
  ∀ a ∈ H, (a : GL (Fin 3) E) •
      (C • HermitianForm.OddThreeLocal.Monomial.coordinateVectors (E := E)) =
    C • HermitianForm.OddThreeLocal.Monomial.coordinateVectors (E := E)

/-- An invariant three-line decomposition, with no orthogonality assertion. -/
@[expose] def HasFrame (H : Subgroup J.specialSubgroup) : Prop :=
  ∃ C : GL (Fin 3) E, PreservesFrame H C

/-- An orthonormal basis whose three lines are preserved as a set. -/
@[expose] def HasOrthogonalFrame (H : Subgroup J.specialSubgroup) : Prop :=
  ∃ C : GL (Fin 3) E,
    J.conjTranspose C.val * J.form * C.val = 1 ∧ PreservesFrame H C

/-- Changing to the frame coordinates gives the actual monomial containment. -/
theorem special_map_le_monomial_of_frame (H : Subgroup J.specialSubgroup)
    (C : GL (Fin 3) E)
    (hC : J.conjTranspose C.val * J.form * C.val = (identityGram J).form)
    (hframe : PreservesFrame H C) :
    H.map (specialEquiv J C hC).toMonoidHom ≤
      HermitianForm.OddThreeLocal.Monomial.special (identityGram J) := by
  rintro _ ⟨a, ha, rfl⟩
  change ((specialEquiv J C hC a : GL (Fin 3) E) •
    HermitianForm.OddThreeLocal.Monomial.coordinateVectors (E := E)) = _
  rw [specialEquiv_apply, mul_smul, mul_smul, hframe a ha, inv_smul_smul]

/-- Special and projective coordinate changes commute with the projection. -/
theorem projectiveEquiv_specialToProjective (C : GL (Fin 3) E)
    (hC : J.conjTranspose C.val * J.form * C.val = (identityGram J).form)
    (a : J.specialSubgroup) :
    projectiveEquiv J C hC (J.specialToProjective a) =
      (identityGram J).specialToProjective (specialEquiv J C hC a) := by
  apply Subtype.ext
  rw [projectiveEquiv_apply, HermitianForm.specialToProjective_apply_val,
    HermitianForm.specialToProjective_apply_val, specialEquiv_apply]
  simp only [map_mul, map_inv]

/-- The full preimage gives projective containment without choosing an
injective section or discarding the scalar kernel. -/
theorem projective_map_le_monomial_of_frame
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (C : GL (Fin 3) E)
    (hC : J.conjTranspose C.val * J.form * C.val = (identityGram J).form)
    (hframe : PreservesFrame (H.comap J.specialToProjective) C) :
    H.map (projectiveEquiv J C hC).toMonoidHom ≤
      HermitianForm.OddThreeLocal.Monomial.projective (identityGram J) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, rfl⟩ := J.specialToProjective_surjective a
  change projectiveEquiv J C hC (J.specialToProjective b) ∈ _
  rw [projectiveEquiv_specialToProjective (J := J) C hC b]
  apply mem_map_of_mem
  exact special_map_le_monomial_of_frame (H.comap J.specialToProjective) C hC hframe
    (mem_map_of_mem _ ha)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement
