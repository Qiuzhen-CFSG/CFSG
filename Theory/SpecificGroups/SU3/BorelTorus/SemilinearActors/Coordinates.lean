module

public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors

/-!
# Entrywise field action on the unitary root and full torus

Every automorphism of the finite matrix field commutes with the Hermitian
involution. Applying it to both Heisenberg coordinates gives an actual
automorphism of the root coordinate group; applying it to the full torus
parameter gives the entrywise image of the diagonal matrix. These formulas
allow root normalization to be separated from the unitary conjugating
matrix in a semilinear formula.

Source: the matrix coordinates of Huppert II.10.12 and GLS3 Section 2.7.
-/

public section

open BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.SemilinearActors
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

theorem field_conj_commute (σ : E ≃+* E) (x : E) :
    σ (J.conj x) = J.conj (σ x) := by
  let := finiteFieldAut_isCyclic (E := E)
  let := IsCyclic.commGroup (α := E ≃+* E)
  exact congrArg (fun f : E ≃+* E => f x) (Commute.all σ J.conj).eq

private def rootFieldMap (σ : E ≃+* E) (z : hermitianUnipotentCoord J) :
    hermitianUnipotentCoord J :=
  ⟨(σ z.val.1, σ z.val.2), by
    have h := congrArg σ z.property
    simpa only [map_add, map_mul, map_zero, field_conj_commute] using h⟩

/-- The field automorphism acts on the genuine Hermitian Heisenberg group. -/
def rootFieldEquiv (σ : E ≃+* E) : hermitianUnipotentCoord J ≃*
    hermitianUnipotentCoord J where
  toFun := rootFieldMap J σ
  invFun := rootFieldMap J σ.symm
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext (σ.symm_apply_apply _) (σ.symm_apply_apply _)
  right_inv z := by
    apply Subtype.ext
    exact Prod.ext (σ.apply_symm_apply _) (σ.apply_symm_apply _)
  map_mul' z w := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_add σ _ _
    · change σ (z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1) =
        σ z.val.2 + σ w.val.2 - σ z.val.1 * J.conj (σ w.val.1)
      rw [map_sub, map_add, map_mul, field_conj_commute]

theorem rootFieldEquiv_val (σ : E ≃+* E) (z : hermitianUnipotentCoord J) :
    (rootFieldEquiv J σ z).val = (σ z.val.1, σ z.val.2) := by rfl

/-- Entrywise field action on the root is equality of GL representatives. -/
theorem field_map_root (σ : E ≃+* E) (z : hermitianUnipotentCoord J) :
    Matrix.GeneralLinearGroup.map σ.toRingHom (hermitianUnipotentGL J z) =
      hermitianUnipotentGL J (rootFieldEquiv J σ z) := by
  apply Units.ext
  ext i j
  change σ (hermitianUnipotentMatrix J z i j) =
    hermitianUnipotentMatrix J (rootFieldEquiv J σ z) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianUnipotentMatrix, rootFieldEquiv_val, field_conj_commute]

/-- The field parameter acts on all of `Eˣ`, not just its norm-one subgroup. -/
theorem field_map_torus (σ : E ≃+* E) (k : Eˣ) :
    Matrix.GeneralLinearGroup.map σ.toRingHom (hermitianTorusGL J k) =
      hermitianTorusGL J (Units.map σ.toMonoidHom k) := by
  apply Units.ext
  ext i j
  change σ (hermitianTorusMatrix J k i j) =
    hermitianTorusMatrix J (Units.map σ.toMonoidHom k) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, field_conj_commute]

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.SemilinearActors
