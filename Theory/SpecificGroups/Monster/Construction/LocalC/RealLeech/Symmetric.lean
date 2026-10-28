module

public import Theory.SpecificGroups.Monster.Construction.LocalC.RealLeech.ProjectiveKernel

/-!
# The symmetric-square action of the full Leech isometry group

For the left natural action with matrix `M`, the induced action is
`A ↦ M * A * Mᵀ`, hence `symmetricConjugate Mᵀ` under the existing API.
This convention gives the group law and covariance of rank-one tensors.
Orthogonality preserves the trace form and the symmetric product.

Equality of real rank-one tensors determines their vectors up to sign.
The concrete short-line kernel theorem therefore identifies the symmetric
kernel with `{1, negationIsometry}`, also the exact binary-action kernel.
These results supply the action and descent ingredients for the local
Monster group; they do not assume or construct that group's pullback.

Source: Aschbacher, *Sporadic Groups*, Section 27, printed pp. 147–149,
and the symmetric summand in (28.1). The lattice model is the attributed
ATLAS construction of Gerald Höhn.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open Atlas.Codes Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC

theorem realLeechRepresentation_mulVec (g : LeechIsometryGroup) (v : NaturalSpace) :
    realLeechRepresentation g v = realLeechMatrix g *ᵥ v := rfl

@[simp] theorem realLeechMatrix_one : realLeechMatrix 1 = 1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_one]
  exact realLeechMap_one

theorem realLeechMatrix_mul (g h : LeechIsometryGroup) :
    realLeechMatrix (g * h) = realLeechMatrix g * realLeechMatrix h := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul]
  exact realLeechMap_mul g h

theorem realLeechMatrix_orthogonal (g : LeechIsometryGroup) :
    (realLeechMatrix g)ᵀ * realLeechMatrix g = 1 := by
  ext i j
  have h := realLeechRepresentation_form g
    ((Pi.basisFun ℝ (Fin 24)) i) ((Pi.basisFun ℝ (Fin 24)) j)
  rw [naturalForm_basis, realLeechRepresentation_mulVec,
    realLeechRepresentation_mulVec] at h
  simp only [Pi.basisFun_apply, Matrix.mulVec_single_one] at h
  change (∑ k, realLeechMatrix g k i * realLeechMatrix g k j) = _ at h
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

@[simp] theorem realLeechMatrix_negation : realLeechMatrix negationIsometry = -1 := by
  apply Matrix.mulVec_injective
  funext v
  rw [← realLeechRepresentation_mulVec, realLeechRepresentation_negation]
  simp [Matrix.neg_mulVec]

/-- Transpose the natural matrix to obtain the left symmetric-square action. -/
def symmetricLeechMap (g : LeechIsometryGroup) : SymmetricPart →ₗ[ℝ] SymmetricPart where
  toFun := symmetricConjugate (realLeechMatrix g)ᵀ
  map_add' A B := by
    apply Subtype.ext
    simp [symmetricConjugate, Matrix.mul_add, Matrix.add_mul]
  map_smul' r A := by
    apply Subtype.ext
    simp [symmetricConjugate]

theorem symmetricLeechMap_one : symmetricLeechMap 1 = LinearMap.id := by
  ext A : 1
  apply Subtype.ext
  simp [symmetricLeechMap, symmetricConjugate]

theorem symmetricLeechMap_mul (g h : LeechIsometryGroup) :
    symmetricLeechMap (g * h) = (symmetricLeechMap g).comp (symmetricLeechMap h) := by
  ext A : 1
  apply Subtype.ext
  simp [symmetricLeechMap, symmetricConjugate, realLeechMatrix_mul,
    Matrix.transpose_mul, Matrix.mul_assoc]

def symmetricLeechEquiv (g : LeechIsometryGroup) : SymmetricPart ≃ₗ[ℝ] SymmetricPart where
  toFun := fun A => symmetricLeechMap g A
  map_add' := (symmetricLeechMap g).map_add
  map_smul' := (symmetricLeechMap g).map_smul
  invFun := symmetricLeechMap g⁻¹
  left_inv A := by
    have h := congrArg (fun f : SymmetricPart →ₗ[ℝ] SymmetricPart => f A)
      (symmetricLeechMap_mul g⁻¹ g)
    simpa only [inv_mul_cancel, symmetricLeechMap_one, LinearMap.id_apply,
      LinearMap.comp_apply] using h.symm
  right_inv A := by
    have h := congrArg (fun f : SymmetricPart →ₗ[ℝ] SymmetricPart => f A)
      (symmetricLeechMap_mul g g⁻¹)
    simpa only [mul_inv_cancel, symmetricLeechMap_one, LinearMap.id_apply,
      LinearMap.comp_apply] using h.symm

/-- The induced action on the fixed 300-dimensional symmetric space. -/
def symmetricLeechRepresentation : LeechIsometryGroup →* (SymmetricPart ≃ₗ[ℝ] SymmetricPart) where
  toFun := symmetricLeechEquiv
  map_one' := LinearEquiv.toLinearMap_injective symmetricLeechMap_one
  map_mul' g h := LinearEquiv.toLinearMap_injective (symmetricLeechMap_mul g h)

theorem symmetricLeechRepresentation_apply (g : LeechIsometryGroup) (A : SymmetricPart) :
    symmetricLeechRepresentation g A = symmetricConjugate (realLeechMatrix g)ᵀ A := rfl

theorem symmetricLeechRepresentation_rankOne (g : LeechIsometryGroup) (v : NaturalSpace) :
    symmetricLeechRepresentation g (rankOne v) = rankOne (realLeechRepresentation g v) := by
  rw [symmetricLeechRepresentation_apply, rankOne_conjugate, Matrix.transpose_transpose,
    realLeechRepresentation_mulVec]

theorem symmetricLeechRepresentation_shortTensor (g : LeechIsometryGroup) (a : ShortClass) :
    symmetricLeechRepresentation g (shortTensor a) = shortTensor (shortClassRepresentation g a) := by
  symm
  apply shortTensor_covariant
  intro x
  rw [Matrix.transpose_transpose, ← realLeechRepresentation_mulVec,
    realLeechRepresentation_agrees]

theorem symmetricLeechRepresentation_form (g : LeechIsometryGroup) (A B : SymmetricPart) :
    symmetricGamma (symmetricLeechRepresentation g A) (symmetricLeechRepresentation g B) =
      symmetricGamma A B := by
  apply symmetricConjugate_gamma
  simpa only [Matrix.transpose_transpose] using realLeechMatrix_orthogonal g

theorem symmetricLeechRepresentation_product (g : LeechIsometryGroup) (A B : SymmetricPart) :
    symmetricProduct (symmetricLeechRepresentation g A) (symmetricLeechRepresentation g B) =
      symmetricLeechRepresentation g (symmetricProduct A B) := by
  apply symmetricConjugate_product
  simpa only [Matrix.transpose_transpose] using realLeechMatrix_orthogonal g

/-- Real rank-one symmetric tensors determine a vector up to sign. -/
theorem rankOne_eq_iff (v w : NaturalSpace) : rankOne v = rankOne w ↔ v = w ∨ v = -w := by
  constructor
  · intro h
    have he (i j : Fin 24) : v i * v j = w i * w j :=
      congrArg (fun A : SymmetricPart => A.val i j) h
    by_cases hw : w = 0
    · left
      subst w
      ext i
      have hi : v i * v i = 0 := by simpa using he i i
      exact mul_self_eq_zero.mp hi
    · obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := Function.ne_iff.mp hw
      rcases (mul_self_eq_mul_self_iff).mp (he k k) with hsign | hsign
      · left
        ext i
        apply mul_right_cancel₀ hk
        simpa only [hsign] using he i k
      · right
        ext i
        apply mul_right_cancel₀ hk
        have hi := he i k
        rw [hsign] at hi
        change v i * w k = -w i * w k
        nlinarith
  · rintro (rfl | rfl)
    · rfl
    · exact rankOne_neg w

@[simp] theorem symmetricLeechRepresentation_negation :
    symmetricLeechRepresentation negationIsometry = 1 := by
  apply LinearEquiv.ext
  intro A
  apply Subtype.ext
  simp [symmetricLeechRepresentation_apply, symmetricConjugate]

/-- The exact kernel on the symmetric square, proved from concrete short lines. -/
theorem symmetricLeechRepresentation_kernel (g : LeechIsometryGroup) :
    symmetricLeechRepresentation g = 1 ↔ g = 1 ∨ g = negationIsometry := by
  constructor
  · intro hg
    apply (leech_short_lines_kernel g).mp
    intro x
    have he : rankOne (leechVector (g.val x.val)) = rankOne (leechVector x.val) := by
      rw [← realLeechRepresentation_agrees, ← symmetricLeechRepresentation_rankOne, hg]
      rfl
    rcases (rankOne_eq_iff _ _).mp he with h | h
    · exact Or.inl (leechVector_injective h)
    · right
      apply leechVector_injective
      rw [leechVector_neg]
      exact h
  · rintro (rfl | rfl)
    · exact map_one _
    · exact symmetricLeechRepresentation_negation

theorem symmetricLeechRepresentation_ker_eq_modTwo :
    symmetricLeechRepresentation.ker = leechModTwoRepresentation.ker := by
  ext g
  exact (symmetricLeechRepresentation_kernel g).trans (leechModTwoRepresentation_kernel g).symm

end Sporadic.Monster.Construction.LocalC
