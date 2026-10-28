module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation on the entire unitary-four plane radical

Every element g of the determinant-one plane local acts on the Hermitian
restriction kernel by X ↦ A X A†, where A is its actual restriction to the
invariant plane. Unitarity gives g⁻¹ = J g† J for the antidiagonal Gram matrix J.
Writing the unipotent as I + N(X), the identity contribution cancels against
g⁻¹ and the zero lower-left block leaves precisely N(A X A†). The upper-right
block of g contributes nothing. Thus this computation needs no Levi section
or surjectivity hypothesis.

The formulas hold in SU₄, inside the normal kernel via `MulAut.conjNormal`,
and under the exhaustive `radicalEquiv` and `coordinatesOfRadical` maps.
This supplies the literal action needed for the Ω₄⁻ block in
Aschbacher--Smith F.1.12(I)(6), `refs/quasithin.pdf`, printed pp.263–264.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneLocal
open Representation.OrthogonalFourMinus
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
variable (F : Type*) [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)
/-- Congruence by an SL₂ matrix preserves the entire Hermitian space. -/
def hermitianCongruence (A : SpecialLinearGroup (Fin 2) F) (X : hermitianMatrices F σ) :
    hermitianMatrices F σ :=
  ⟨A.val * X.val * adjoint σ A.val, by
    change adjoint σ (A.val * X.val * adjoint σ A.val) = _
    rw [adjoint_mul, adjoint_mul, adjoint_involutive σ hσ, X.property, mul_assoc]⟩

@[simp] theorem hermitianCongruence_val (A : SpecialLinearGroup (Fin 2) F)
    (X : hermitianMatrices F σ) :
    (hermitianCongruence F σ hσ A X).val = A.val * X.val * adjoint σ A.val := rfl

private theorem su_inv_val (g : SU F (form F σ hσ)) :
    (g⁻¹).val.val = gram F * (form F σ hσ).conjTranspose g.val.val * gram F := by
  have hu := g.property.1
  change (form F σ hσ).conjTranspose g.val.val * gram F * g.val.val = gram F at hu
  have hl : (gram F * (form F σ hσ).conjTranspose g.val.val * gram F) * g.val.val = 1 := by
    calc
      _ = gram F * ((form F σ hσ).conjTranspose g.val.val * gram F * g.val.val) := by
        simp only [mul_assoc]
      _ = 1 := by rw [hu, gram_sq]
  calc
    (g⁻¹).val.val = ((gram F * (form F σ hσ).conjTranspose g.val.val * gram F) *
        g.val.val) * (g⁻¹).val.val := by rw [hl, one_mul]
    _ = gram F * (form F σ hσ).conjTranspose g.val.val * gram F := by
      rw [mul_assoc, show g.val.val * (g⁻¹).val.val = 1 from g.val.val_inv, mul_one]

private def upperPart (X : Mat F) : Matrix (Fin 4) (Fin 4) F :=
  !![0,0,X 0 1,X 0 0; 0,0,X 1 1,X 1 0; 0,0,0,0; 0,0,0,0]

private theorem unipotentMatrix_eq (X : Mat F) :
    unipotentMatrix F X = 1 + upperPart F X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentMatrix, upperPart]

variable [Finite F]
/-- Literal conjugation by any element of the embedded local factor. -/
theorem unipotentMatrix_conj (g : localFactor F (form F σ hσ)) (X : Mat F) :
    g.val.val.val * unipotentMatrix F X * (g⁻¹).val.val.val =
      unipotentMatrix F ((factorRestriction F (form F σ hσ) g).val * X *
        adjoint σ (factorRestriction F (form F σ hσ) g).val) := by
  have hpart : g.val.val.val * upperPart F X * (g⁻¹).val.val.val =
      upperPart F ((factorRestriction F (form F σ hσ) g).val * X *
        adjoint σ (factorRestriction F (form F σ hσ) g).val) := by
    obtain ⟨h20,h30,h21,h31⟩ := (mem_planeParabolicSU F _ g.val).mp
      (local_le_planeParabolic F _ g.property)
    rw [show (g⁻¹).val.val.val = gram F *
      (form F σ hσ).conjTranspose g.val.val.val * gram F from su_inv_val F σ hσ g.val]
    rw [factorRestriction_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperPart, adjoint, form, gram, HermitianForm.conjTranspose,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, h20,h30,h21,h31] <;> ring
  rw [unipotentMatrix_eq, unipotentMatrix_eq, mul_add, add_mul, mul_one,
    show g.val.val.val * (g⁻¹).val.val.val = 1 from g.val.val.val_inv, hpart]

variable [CharP F 2]
/-- The matrix formula holds in the actual special unitary group. -/
theorem unipotentSU_conj (g : localFactor F (form F σ hσ)) (X : hermitianMatrices F σ) :
    g.val * unipotentSU F σ hσ X * g.val⁻¹ =
      unipotentSU F σ hσ (hermitianCongruence F σ hσ (factorRestriction F (form F σ hσ) g) X) := by
  apply Subtype.ext
  apply Units.ext
  exact unipotentMatrix_conj F σ hσ g X.val

/-- Conjugation inside the normal restriction kernel in Hermitian coordinates. -/
theorem unipotent_conj (g : localFactor F (form F σ hσ))
    (X : Multiplicative (hermitianMatrices F σ)) :
    MulAut.conjNormal g (unipotent F σ hσ X) =
      unipotent F σ hσ (Multiplicative.ofAdd
        (hermitianCongruence F σ hσ (factorRestriction F (form F σ hσ) g) X.toAdd)) := by
  apply Subtype.ext
  apply Subtype.ext
  exact unipotentSU_conj F σ hσ g X.toAdd

/-- Equivariance of the full Hermitian parametrization, without a Levi premise. -/
theorem radicalEquiv_conj (g : localFactor F (form F σ hσ))
    (X : Multiplicative (hermitianMatrices F σ)) :
    MulAut.conjNormal g (radicalEquiv F σ hσ X) =
      radicalEquiv F σ hσ (Multiplicative.ofAdd
        (hermitianCongruence F σ hσ (factorRestriction F (form F σ hσ) g) X.toAdd)) :=
  unipotent_conj F σ hσ g X

/-- Extracting coordinates intertwines actual conjugation and Hermitian congruence. -/
theorem coordinatesOfRadical_conj (g : localFactor F (form F σ hσ))
    (u : radical F σ hσ) :
    coordinatesOfRadical F σ hσ (MulAut.conjNormal g u) =
      hermitianCongruence F σ hσ (factorRestriction F (form F σ hσ) g)
        (coordinatesOfRadical F σ hσ u) := by
  obtain ⟨X, rfl⟩ := (radicalEquiv F σ hσ).surjective u
  simp only [radicalEquiv_apply, unipotent_conj, coordinatesOfRadical_unipotent]
  rfl

/-- The inverse parametrization is equivariant on every element of the kernel. -/
theorem radicalEquiv_symm_conj (g : localFactor F (form F σ hσ))
    (u : radical F σ hσ) :
    (radicalEquiv F σ hσ).symm (MulAut.conjNormal g u) =
      Multiplicative.ofAdd (hermitianCongruence F σ hσ
        (factorRestriction F (form F σ hσ) g) ((radicalEquiv F σ hσ).symm u).toAdd) := by
  obtain ⟨X, rfl⟩ := (radicalEquiv F σ hσ).surjective u
  rw [radicalEquiv_conj, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

/-- Literal matrix entries of the coordinate action on an arbitrary kernel element. -/
theorem coordinatesOfRadical_conj_val (g : localFactor F (form F σ hσ))
    (u : radical F σ hσ) :
    (coordinatesOfRadical F σ hσ (MulAut.conjNormal g u)).val =
      (factorRestriction F (form F σ hσ) g).val *
        (coordinatesOfRadical F σ hσ u).val *
          adjoint σ (factorRestriction F (form F σ hσ) g).val := by
  rw [coordinatesOfRadical_conj, hermitianCongruence_val]

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
