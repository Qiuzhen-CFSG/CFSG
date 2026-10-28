module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Conjugation transport for binary defining words

The four concrete factors and their successive Frobenius tensor products commute
with coefficient embeddings. Over an algebraically closed coefficient field,
rescaling any invertible ternary matrix makes its determinant one. Its action in
the coefficient-field SL₃ word then intertwines two conjugate matrix embeddings.
This proves transport for all four factors at once, including the trace-zero
adjoint factor, without replacing their actual carriers or actions.

This supplies the representation part of arbitrary Hermitian-form transport in
the SU₃ instance of GLS III, 2.8.2 and 2.8.6(a).
-/

public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MatrixGroups TensorProduct
open Representation
namespace Representation.SL3.BinaryDefiningFactors
section
variable {F E K : Type*} [Field F] [Field E] [Field K]

/-- Coefficient embeddings commute with each of the four concrete factor actions. -/
theorem factorRep_map (κ : E →+* K) (ι : F →+* E) (a : Factor)
    (g : SL(3,F)) :
    factorRep κ a (Matrix.SpecialLinearGroup.map ι g) = factorRep (κ.comp ι) a g := by
  cases a with
  | trivial => rfl
  | natural => rfl
  | dual =>
    apply LinearMap.ext
    intro f
    change Module.Dual K (Fin 3 → K) at f
    apply LinearMap.ext
    intro v
    change f (natural κ ((Matrix.SpecialLinearGroup.map ι g)⁻¹) v) = _
    rw [← map_inv]
    rfl
  | adjoint =>
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change natural κ (Matrix.SpecialLinearGroup.map ι g) ∘ₗ f.val ∘ₗ
      natural κ ((Matrix.SpecialLinearGroup.map ι g)⁻¹) = _
    rw [← map_inv]
    rfl

/-- Coefficient embeddings commute with the full recursive Frobenius tensor action. -/
theorem wordRep_map [CharP K 2] (κ : E →+* K) (ι : F →+* E)
    (w : List Factor) (g : SL(3,F)) :
    wordRep κ w (Matrix.SpecialLinearGroup.map ι g) = wordRep (κ.comp ι) w g := by
  induction w generalizing κ with
  | nil => rfl
  | cons a w ih =>
    change TensorProduct.map _ _ = TensorProduct.map _ _
    rw [factorRep_map, ih]
    rfl


end

section
variable {K : Type*} [Field K] [IsAlgClosed K]
open Matrix

private theorem exists_sl_scalar (C : GL (Fin 3) K) :
    ∃ D : SL(3,K), ∃ c : K, D.val = c • C.val := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq C.val.det⁻¹ (by decide : 0 < 3)
  have hd : C.val.det ≠ 0 := (GeneralLinearGroup.det C).ne_zero
  refine ⟨⟨c • C.val, ?_⟩, c, rfl⟩
  rw [Matrix.det_smul]
  simpa [hc] using inv_mul_cancel₀ hd

variable [CharP K 2] {F G : Type*} [Field F] [Group G]

private def conjugateWordEquiv (ι : F →+* K) (w : List Factor)
    (α β : G →* SL(3,F)) (D : SL(3,K))
    (hD : ∀ g, D * Matrix.SpecialLinearGroup.map ι (β g) =
      Matrix.SpecialLinearGroup.map ι (α g) * D) :
    Representation.Equiv ((wordRep ι w).comp β) ((wordRep ι w).comp α) := by
  let ρ := wordRep (RingHom.id K) w
  refine Representation.Equiv.mk (LinearMap.GeneralLinearGroup.generalLinearEquiv K (WordSpace K w) (ρ.asGroupHom D)) ?_
  intro g
  change ρ D * wordRep ι w (β g) = wordRep ι w (α g) * ρ D
  have hβ := wordRep_map (RingHom.id K) ι w (β g)
  have hα := wordRep_map (RingHom.id K) ι w (α g)
  simp only [RingHom.id_comp] at hα hβ
  rw [← hβ, ← hα]
  change ρ D * ρ _ = ρ _ * ρ D
  rw [← map_mul, ← map_mul, hD]


end

section
open Matrix
variable {F K G : Type*} [Field F] [Field K] [IsAlgClosed K] [CharP K 2] [Group G]

/-- Conjugate matrix embeddings give equivalent concrete tensor words.
The conjugating matrix is allowed to have arbitrary nonzero determinant. -/
theorem wordEquiv_of_matrix_conjugacy (ι : F →+* K) (w : List Factor)
    (α β : G →* SL(3,F)) (C : GL (Fin 3) F)
    (hC : ∀ g, C * SpecialLinearGroup.toGL (β g) = SpecialLinearGroup.toGL (α g) * C) :
    Nonempty (Representation.Equiv ((wordRep ι w).comp β) ((wordRep ι w).comp α)) := by
  obtain ⟨D, c, hc⟩ := exists_sl_scalar (GeneralLinearGroup.map ι C)
  refine ⟨conjugateWordEquiv ι w α β D ?_⟩
  intro g
  apply Subtype.ext
  change D.val * (β g).val.map ι = (α g).val.map ι * D.val
  rw [hc, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  have hm (A : SL(3,F)) :
      (GeneralLinearGroup.map ι (SpecialLinearGroup.toGL A)).val = A.val.map ι := by
    ext i j
    rfl
  simpa only [map_mul, Units.val_mul, hm] using
    congrArg (fun A : GL (Fin 3) F => (GeneralLinearGroup.map ι A).val) (hC g)


end

end Representation.SL3.BinaryDefiningFactors
