module
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.Projective
/-!
# Geometry for the Hermitian orthogonal commutator

Conjugation is an involutive isometry of negative determinant and normalizes
SL₂ congruences. The diagonal vectors and off-diagonal norm plane give the
coordinates used by the singular-frame and stabilizer arguments.

For a finite quadratic extension, the Galois group consists of the identity
and the given nontrivial conjugation. Consequently the coordinate norm is the
field norm and is surjective. This replaces characteristic-two square-root
extraction in the singular-frame argument.

Sources: GLS3 §2.7 and Aschbacher–Smith A.2.17, printed pp.38–39
(`refs/quasithin.pdf`). The coordinate proofs extend the binary implementation
in `Representation.OrthogonalFourMinus.HermitianEquiv.CommutatorImage.Basic`.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
open Representation.OrthogonalFourMinus
universe u
variable {E : Type u} [Field E] (σ : E ≃+* E) (hσ : Function.Involutive σ)
/-- Entrywise conjugation on Hermitian matrices, expressed as transpose. -/
def conjugationLinear : Space σ hσ ≃ₗ[fixedField σ] Space σ hσ where
  toFun X := ⟨X.val.transpose, by
    ext i j
    exact entry_conjugate σ hσ X j i⟩
  invFun X := ⟨X.val.transpose, by
    ext i j
    exact entry_conjugate σ hσ X j i⟩
  left_inv X := by apply Subtype.ext; rfl
  right_inv X := by apply Subtype.ext; rfl
  map_add' X Y := by apply Subtype.ext; rfl
  map_smul' c X := by apply Subtype.ext; rfl

@[simp] theorem conjugationLinear_val (X : Space σ hσ) :
    (conjugationLinear σ hσ X).val = X.val.transpose := rfl

/-- The conjugation involution in the full determinant-isometry group. -/
def conjugationOrthogonal : Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ) :=
  ⟨conjugationLinear σ hσ, (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr (by
    intro X
    change -(determinant σ hσ _) = -(determinant σ hσ _)
    congr 1
    apply Subtype.ext
    exact Matrix.det_transpose _)⟩

@[simp] theorem conjugationOrthogonal_sq : conjugationOrthogonal σ hσ * conjugationOrthogonal σ hσ = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  rfl

theorem conjugationOrthogonal_mul_action (A : Matrix.SpecialLinearGroup (Fin 2) E) :
    conjugationOrthogonal σ hσ * orthogonalAction σ hσ A =
      orthogonalAction σ hσ (Matrix.SpecialLinearGroup.map σ.toRingHom A) *
        conjugationOrthogonal σ hσ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  change (A.val * X.val * adjoint σ A.val).transpose =
    A.val.map σ * X.val.transpose *
      adjoint σ (A.val.map σ)
  have h : adjoint σ (A.val.map σ) = A.val.transpose := by
    ext i j
    exact hσ _
  rw [h, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [adjoint, Matrix.transpose_map, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- The first diagonal matrix unit. -/
def firstDiagonal : Space σ hσ := (coordinates σ hσ).symm ((1, 0), 0)

/-- The second diagonal matrix unit. -/
def secondDiagonal : Space σ hσ := (coordinates σ hσ).symm ((0, 1), 0)

/-- The anisotropic norm plane, with coordinate `z` in the quadratic extension. -/
def offDiagonal : E →ₗ[fixedField σ] Space σ hσ where
  toFun z := (coordinates σ hσ).symm ((0, 0), z)
  map_add' x y := by
    apply (coordinates σ hσ).injective
    simp
  map_smul' c z := by
    apply (coordinates σ hσ).injective
    simp

@[simp] theorem coordinates_offDiagonal (z : E) :
    coordinates σ hσ (offDiagonal σ hσ z) = ((0, 0), z) := by
  exact (coordinates σ hσ).apply_symm_apply _

/-- Every full quadratic isometry preserves the polar pairing. -/
theorem polar_preserved
    (g : Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ)) (X Y : Space σ hσ) :
    (form σ hσ).polarBilin (g.val X) (g.val Y) = (form σ hσ).polarBilin X Y := by
  have hg (X : Space σ hσ) : form σ hσ (g.val X) = form σ hσ X := by
    have h := (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp g.property X
    exact neg_injective h
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hg]


lemma form_eq_coordinates (X : Space σ hσ) :
    form σ hσ X = (coordinates σ hσ X).1.1 * (coordinates σ hσ X).1.2 -
      norm σ hσ (coordinates σ hσ X).2 := by
  simpa only [LinearEquiv.symm_apply_apply] using form_coordinates σ hσ (coordinates σ hσ X)

lemma coe_polar_coordinates (v w : Space σ hσ) :
    ((form σ hσ).polarBilin v w : E) =
    (coordinates σ hσ v).1.1.val * (coordinates σ hσ w).1.2.val +
    (coordinates σ hσ v).1.2.val * (coordinates σ hσ w).1.1.val -
    ((coordinates σ hσ v).2 * σ (coordinates σ hσ w).2 +
      (coordinates σ hσ w).2 * σ (coordinates σ hσ v).2) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    form_eq_coordinates, map_add, Prod.fst_add, Prod.snd_add,
    Subfield.coe_sub, Subfield.coe_mul, Subfield.coe_add, norm]
  ring

lemma form_preserved_of_orthogonal
    (g : Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ)) (X : Space σ hσ) :
    form σ hσ (g.val X) = form σ hσ X := by
  exact neg_injective ((Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp g.property X)

lemma norm_eq_algebraNorm [Finite E]
    (hdegree : Module.finrank (fixedField σ) E = 2) (hne : ∃ t : E, σ t ≠ t) (z : E) :
    norm σ hσ z = Algebra.norm (fixedField σ) z := by
  classical
  have hc : conjugationAlg σ ≠ 1 := by
    intro h
    obtain ⟨t, ht⟩ := hne
    exact ht (congrArg (fun e : E ≃ₐ[fixedField σ] E => e t) h)
  have hcard : Fintype.card (E ≃ₐ[fixedField σ] E) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdegree]
  have hall : (Finset.univ : Finset (E ≃ₐ[fixedField σ] E)) = {1, conjugationAlg σ} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hcard, hc.symm]
  apply Subtype.ext
  change z * σ z = algebraMap (fixedField σ) E (Algebra.norm (fixedField σ) z)
  rw [Algebra.norm_eq_prod_automorphisms, hall]
  rw [Finset.prod_pair hc.symm]
  rfl

lemma norm_surjective [Finite E]
    (hdegree : Module.finrank (fixedField σ) E = 2) (hne : ∃ t : E, σ t ≠ t) :
    Function.Surjective (norm σ hσ) := by
  intro a
  obtain ⟨z, hz⟩ := FiniteField.norm_surjective (fixedField σ) E a
  exact ⟨z, (norm_eq_algebraNorm σ hσ hdegree hne z).trans hz⟩

end ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
