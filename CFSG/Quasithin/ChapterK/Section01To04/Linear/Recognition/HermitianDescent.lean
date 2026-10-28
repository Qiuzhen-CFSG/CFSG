module

public import Theory.Representation.HermitianTensorThree
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Geometry
public import Theory.Representation.SL3.BinaryFieldDescent.BaseChange

/-!
# Scalar extension and binary descent of the Hermitian three-space tensor

The canonical map sends c ⊗ X to cX. Every matrix is a linear combination
of X + X* and σ(t)X + tX*, with σ(t) ≠ t, so this map is onto. Equality of
extension-field dimensions makes it an equivalence, and matrix congruence
identifies its action with the genuine natural tensor coefficient-twisted
natural action. Descent of equivalences then supplies a binary intertwiner
for any module whose scalar extension has this tensor action.

This proves a concrete comparison used in K.3.2(c); it does not select the
tensor alternative from the cubic ratio. Source: Aschbacher–Smith, combined
1 March 2004 manuscript, H.4.2 and K.3.2, printed pp.380 and 454–456.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open Representation
open Representation.HermitianTensorThree
noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.HermitianDescent
variable (n : ℕ) [NeZero n]

local instance : Module (ZMod 2) (F n) := (fixedBinaryAlgebra n).toModule

/-- Multiplication of scalars with the actual Hermitian matrix inclusion. -/
def scalarExtensionMap : E n ⊗[F n] Space n →ₗ[E n] Mat n :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun c => c • (hermitian n).toSubmodule.subtype
      map_add' := by intros; simp [add_smul]
      map_smul' := by intros; simp [mul_smul] }

@[simp] theorem scalarExtensionMap_tmul (c : E n) (X : Space n) :
    scalarExtensionMap n (c ⊗ₜ[F n] X) = c • X.val := rfl

private def hermitianSum (X : Mat n) : Space n :=
  ⟨X + adjoint n X, by
    change adjoint n (X + adjoint n X) = X + adjoint n X
    rw [adjoint_add, adjoint_involutive, add_comm]⟩

private def hermitianWeighted (t : E n) (X : Mat n) : Space n :=
  ⟨sigma n t • X + t • adjoint n X, by
    change adjoint n (sigma n t • X + t • adjoint n X) = _
    rw [adjoint_add, adjoint_smul, adjoint_smul, sigma_involutive, adjoint_involutive,
      add_comm]⟩

/-- Two conjugate-symmetric combinations span every matrix over E. -/
theorem scalarExtensionMap_surjective : Function.Surjective (scalarExtensionMap n) := by
  obtain ⟨t, ht⟩ := OrthogonalFourMinus.FiniteModel.exists_conjugation_ne n
  have hd : sigma n t + t ≠ 0 := by
    simpa only [← CharTwo.sub_eq_add, sub_ne_zero] using ht
  intro X
  refine ⟨(sigma n t + t)⁻¹ ⊗ₜ[F n] hermitianWeighted n t X +
    ((sigma n t + t)⁻¹ * t) ⊗ₜ[F n] hermitianSum n X, ?_⟩
  simp only [map_add, scalarExtensionMap_tmul, hermitianWeighted, hermitianSum]
  ext i j
  change (sigma n t + t)⁻¹ * (sigma n t * X i j + t * adjoint n X i j) +
    ((sigma n t + t)⁻¹ * t) * (X i j + adjoint n X i j) = X i j
  have hz : t * adjoint n X i j + t * adjoint n X i j = 0 := CharTwo.add_self_eq_zero _
  calc
    _ = (sigma n t + t)⁻¹ * ((sigma n t + t) * X i j +
      (t * adjoint n X i j + t * adjoint n X i j)) := by ring
    _ = X i j := by rw [hz, add_zero, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

def scalarExtensionEquiv : (E n ⊗[F n] Space n) ≃ₗ[E n] Mat n :=
  LinearEquiv.ofBijective (scalarExtensionMap n) ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_baseChange, finrank_space]
      simp [Mat, Module.finrank_matrix])).mpr (scalarExtensionMap_surjective n),
    scalarExtensionMap_surjective n⟩

theorem scalarExtensionEquiv_intertwines (g : Cover n)
    (u : E n ⊗[F n] Space n) :
    scalarExtensionEquiv n (extendScalars (E n) (action n) g u) =
      matrixAction n g (scalarExtensionEquiv n u) := by
  change scalarExtensionMap n (extendScalars (E n) (action n) g u) =
    matrixAction n g (scalarExtensionMap n u)
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul c X =>
    change c • (action n g X).val = matrixAction n g (c • X.val)
    rw [map_smul]
    rfl

/-- The scalar-extended descended space is the literal twisted tensor. -/
def scalarExtensionTensorEquiv : (E n ⊗[F n] Space n) ≃ₗ[E n] Tensor n :=
  (scalarExtensionEquiv n).trans (tensorCoordinates n).symm

theorem scalarExtensionTensorEquiv_intertwines (g : Cover n)
    (u : E n ⊗[F n] Space n) :
    scalarExtensionTensorEquiv n (extendScalars (E n) (action n) g u) =
      tensorAction n g (scalarExtensionTensorEquiv n u) := by
  apply (tensorCoordinates n).injective
  simp only [scalarExtensionTensorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, tensorCoordinates_action]
  exact scalarExtensionEquiv_intertwines n g u

/-- The scalar-extension comparison as an equivalence of representations. -/
def scalarExtensionTensorRepresentationEquiv :
    (extendScalars (E n) (action n)).Equiv (tensorAction n) :=
  .mk (scalarExtensionTensorEquiv n) (fun g => LinearMap.ext
    (scalarExtensionTensorEquiv_intertwines n g))

/-- A module with the specified genuine scalar-extension tensor has a binary
intertwiner with the descended model. This is the comparison consumed by the
recognition assembly, independent of the selection of the tensor alternative. -/
theorem binary_equiv_of_scalarExtension
    {W : Type*} [AddCommGroup W] [Module (F n) W] [Module (ZMod 2) W]
    [FiniteDimensional (F n) W] (τ : Representation (F n) (Cover n) W)
    (h : Nonempty ((extendScalars (E n) τ).Equiv (tensorAction n))) :
    Nonempty ((restrictScalars (k := ZMod 2) τ).Equiv (binaryAction n)) := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := BinaryFieldDescent.equiv_of_extendScalars (K := E n) τ (action n)
    ⟨e.trans (scalarExtensionTensorRepresentationEquiv n).symm⟩
  exact ⟨BinaryFieldDescent.restrictBinaryEquiv f⟩

end CFSG.Quasithin.ChapterK.Linear.Recognition.HermitianDescent
