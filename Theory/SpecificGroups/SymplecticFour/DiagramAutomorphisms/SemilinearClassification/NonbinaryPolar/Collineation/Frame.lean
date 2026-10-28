module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar.Collineation.Incidence
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Normalizing a projective frame in four-space

The images of the four coordinate points span the whole space by subspace
transport, so any nonzero representatives form a basis. Every coordinate of
the image of the all-ones point in that basis is nonzero: otherwise subspace
transport would put the original all-ones point into a coordinate hyperplane.
Rescaling the basis by these coordinates realizes the entire image frame by
a linear equivalence. Removing that equivalence yields a collineation fixing
the standard frame.

This is only the frame-normalization step of projective coordinatization.
Reconstructing the field automorphism from the normalized collineation and
recovering its action on every projective point remain separate obligations.

Source context: the geometric automorphism fact used in Aschbacher--Smith
F.1.12, printed pp.263--264 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Projectivization Module
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.Collineation
variable {F : Type*} [Field F]

private theorem span_image_axes (φ : Equiv.Perm (ProjectivePoint F)) (hφ : PreservesLines φ) :
    Submodule.span F (Set.range (fun i => (φ (axis i)).rep)) = ⊤ := by
  rw [Submodule.span_range_eq_iSup]
  simp_rw [← submodule_eq, ← submoduleOrderIso_point φ hφ]
  rw [← OrderIso.map_iSup, iSup_axis, OrderIso.map_top]

private def imageBasis (φ : Equiv.Perm (ProjectivePoint F)) (hφ : PreservesLines φ) :
    Basis Index F (Vector F) :=
  basisOfTopLeSpanOfCardEqFinrank (fun i => (φ (axis i)).rep)
    (span_image_axes φ hφ).ge (Module.finrank_fintype_fun_eq_card F).symm

@[simp] private theorem imageBasis_apply (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : PreservesLines φ) (i : Index) : imageBasis φ hφ i = (φ (axis i)).rep := by
  simp only [imageBasis, coe_basisOfTopLeSpanOfCardEqFinrank]

private theorem imageBasis_span (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : PreservesLines φ) (s : Set Index) :
    submoduleOrderIso φ hφ (Submodule.span F ((Pi.basisFun F Index) '' s)) =
      Submodule.span F (imageBasis φ hφ '' s) := by
  conv_lhs => rw [Submodule.span_eq_iSup_of_singleton_spans]
  conv_rhs => rw [Submodule.span_eq_iSup_of_singleton_spans]
  simp only [iSup_image, OrderIso.map_iSup, Pi.basisFun_apply, ← axis_submodule]
  simp only [submoduleOrderIso_point]
  simp only [submodule_eq, imageBasis_apply]

private theorem image_diagonal_coordinates_ne_zero (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : PreservesLines φ) (i : Index) :
    (imageBasis φ hφ).repr (φ diagonalPoint).rep i ≠ 0 := by
  intro hi
  let s : Set Index := {j | j ≠ i}
  have hx : (φ diagonalPoint).rep ∈ Submodule.span F (imageBasis φ hφ '' s) := by
    apply (imageBasis φ hφ).mem_span_image.mpr
    intro j hj
    change j ≠ i
    intro hji
    subst j
    exact (Finsupp.mem_support_iff.mp hj) hi
  have hle : (φ diagonalPoint).submodule ≤
      Submodule.span F (imageBasis φ hφ '' s) := by
    simpa only [submodule_eq, Submodule.span_singleton_le_iff_mem] using hx
  rw [← imageBasis_span φ hφ s, ← submoduleOrderIso_point φ hφ diagonalPoint] at hle
  have hle' := (submoduleOrderIso φ hφ).le_iff_le.mp hle
  have hm : (fun _ : Index => (1 : F)) ∈ Submodule.span F (Pi.basisFun F Index '' s) := by
    simpa only [diagonalPoint, submodule_mk, Submodule.span_singleton_le_iff_mem] using hle'
  have hs := (Pi.basisFun F Index).mem_span_image.mp hm
  exact hs (by simp [Pi.basisFun_repr]) rfl

/-- The image of the standard projective frame is realized by an invertible
linear map. This theorem constructs that map from incidence alone. -/
theorem exists_linear_frame (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : PreservesLines φ) :
    ∃ A : Vector F ≃ₗ[F] Vector F,
      (∀ i, linearProjective A (axis i) = φ (axis i)) ∧
      linearProjective A diagonalPoint = φ diagonalPoint := by
  let b := imageBasis φ hφ
  let x := (φ diagonalPoint).rep
  have hc (i : Index) : IsUnit (b.repr x i) :=
    isUnit_iff_ne_zero.mpr (image_diagonal_coordinates_ne_zero φ hφ i)
  let d := b.isUnitSMul hc
  let A : Vector F ≃ₗ[F] Vector F := d.equivFun.symm
  have hA (i : Index) : A (Pi.single i 1) = b.repr x i • b i := by
    have hd : d.equivFun (d i) = Pi.single i 1 := by
      ext j
      simp only [Basis.equivFun_self, Pi.single_apply]
      split_ifs <;> simp_all
    change d.equivFun.symm (Pi.single i 1) = _
    rw [← hd, LinearEquiv.symm_apply_apply, Basis.isUnitSMul_apply]
  have hAx : A (fun _ => 1) = x := by
    change d.equivFun.symm _ = _
    rw [Basis.equivFun_symm_apply]
    simp only [one_smul, d, Basis.isUnitSMul_apply]
    exact b.sum_repr x
  refine ⟨A, ?_, ?_⟩
  · intro i
    rw [linearProjective_apply]
    change mk F (A (Pi.single i 1)) _ = φ (axis i)
    rw [← (φ (axis i)).mk_rep]
    apply (mk_eq_mk_iff' F _ _ _ _).mpr
    refine ⟨b.repr x i, ?_⟩
    simpa only [b, imageBasis_apply] using (hA i).symm
  · rw [linearProjective_apply]
    change mk F (A (fun _ => 1)) _ = φ diagonalPoint
    simp only [hAx, x, mk_rep]

/-- Remove an invertible linear map so that the remaining collineation fixes
every coordinate point and the all-ones point. -/
theorem exists_normalized (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : PreservesLines φ) :
    ∃ (A : Vector F ≃ₗ[F] Vector F) (ψ : Equiv.Perm (ProjectivePoint F)),
      PreservesLines ψ ∧ (∀ i, ψ (axis i) = axis i) ∧
      ψ diagonalPoint = diagonalPoint ∧ ∀ p, φ p = linearProjective A (ψ p) := by
  obtain ⟨A, haxes, hdiag⟩ := exists_linear_frame φ hφ
  let ψ := φ.trans (linearProjective A).symm
  refine ⟨A, ψ, hφ.trans (linearProjective_preservesLines A).symm, ?_, ?_, ?_⟩
  · intro i
    change (linearProjective A).symm (φ (axis i)) = axis i
    rw [← haxes, Equiv.symm_apply_apply]
  · change (linearProjective A).symm (φ diagonalPoint) = diagonalPoint
    rw [← hdiag, Equiv.symm_apply_apply]
  · intro p
    exact ((linearProjective A).apply_symm_apply (φ p)).symm
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.Collineation
