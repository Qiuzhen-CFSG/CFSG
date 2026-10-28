module

public import Theory.Representation.SL2.BinaryHermitianRecognition.Setup
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Geometry

/-!
# Scalar extension of the finite Hermitian matrix action

The map `c ⊗ X ↦ c • X.val.map β` identifies the scalar extension of the
actual Hermitian action with the matrix action of the two Frobenius twists.
The coefficient-field compatibility makes this tensor map well-defined, and
the group-field compatibility identifies the two factors in its action.

For surjectivity, choose an element `t` outside the fixed field. The two
coordinate diagonal matrices and the off-diagonal Hermitian matrices with
upper-right entries `1` and `t` span all matrices after scalar extension:
the off-diagonal determinant is `β (conjugation s t) - β t ≠ 0`.
The explicit surjection between four-dimensional spaces is then injective.
This works for every positive `s`, including `s = 1`, with no bound on `j`.

This is the Hermitian-to-tensor comparison used in the repeated-pair case of
Aschbacher--Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), G.9.3(7), printed pp.354,356–357, and GLS volume 3,
§§2.8.6, 2.8.8, 2.8.10(b). Recognition from the highest weight is a separate step.
-/

public section

open scoped MatrixGroups TensorProduct
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
namespace Representation.SL2.BinaryHermitian
noncomputable section
variable {K : Type*} [Field K] {E : Type*} [Field E]
    {L : Type*} [Field L] [Algebra E L] {s : ℕ} [NeZero s]
    (θ : E ≃+* fixedField s) (β : Field s →+* L)
    (hθ : ∀ a, β (θ a).val = algebraMap E L a)

set_option backward.isDefEq.respectTransparency false in
private def entryMap : letI := coefficientModule θ; Space s →ₗ[E] Mat L := by
  let := coefficientModule θ
  exact {
    toFun X := X.val.map β
    map_add' X Y := by ext i j; exact β.map_add _ _
    map_smul' a X := by
      ext i j
      change β ((θ a) • X.val i j) = a • β (X.val i j)
      simp only [Algebra.smul_def, map_mul]
      exact congrArg (fun z : L => z * β (X.val i j)) (hθ a) }

/-- Extend the entrywise embedding of Hermitian matrices to an `L`-linear map. -/
def scalarExtensionMap : letI := coefficientModule θ; L ⊗[E] Space s →ₗ[L] Mat L := by
  let := coefficientModule θ
  exact TensorProduct.AlgebraTensorModule.lift
    { toFun := fun c => c • entryMap θ β hθ
      map_add' := by intros; exact add_smul _ _ _
      map_smul' := by intros; exact mul_smul _ _ _ }

/-- On a pure tensor, the comparison is the entrywise field embedding followed
by scalar multiplication. -/
@[simp] theorem scalarExtensionMap_tmul (c : L) (X : Space s) :
    letI := coefficientModule θ
    scalarExtensionMap θ β hθ (c ⊗ₜ[E] X) = c • X.val.map β := (rfl)

private lemma coefficient_finrank :
    letI := coefficientModule θ
    Module.finrank E (Space s) = 4 := by
  let := coefficientModule θ
  let : Finite E := Finite.of_injective θ θ.injective
  have : Module.Finite E (Space s) := Module.Finite.of_finite
  have h₁ := Module.natCard_eq_pow_finrank (K := E) (V := Space s)
  have h₂ := Module.natCard_eq_pow_finrank (K := fixedField s) (V := Space s)
  rw [finrank_space] at h₂
  rw [Nat.card_congr θ.toEquiv, card_fixedField] at h₁
  rw [card_fixedField] at h₂
  exact (pow_right_inj₀ (pow_pos (by decide : 0 < (2 : ℕ)) s)
    (Nat.one_lt_pow (NeZero.ne s) (by decide : 1 < (2 : ℕ))).ne').mp (h₁.symm.trans h₂)

private lemma scalarExtensionMap_surjective :
    letI := coefficientModule θ
    Function.Surjective (scalarExtensionMap θ β hθ) := by
  let := coefficientModule θ
  obtain ⟨t, ht⟩ := exists_conjugation_ne s
  have hd : β (conjugation s t) - β t ≠ 0 :=
    sub_ne_zero.mpr (fun h => ht (β.injective h))
  intro M
  let r := (M 1 0 - M 0 1) / (β (conjugation s t) - β t)
  let q := M 0 1 - r * β t
  refine ⟨(M 0 0) ⊗ₜ[E] (coordinates s).symm ((1, 0), 0) +
    (M 1 1) ⊗ₜ[E] (coordinates s).symm ((0, 1), 0) +
    q ⊗ₜ[E] (coordinates s).symm ((0, 0), 1) +
    r ⊗ₜ[E] (coordinates s).symm ((0, 0), t), ?_⟩
  simp only [map_add, scalarExtensionMap_tmul, coordinates_symm_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, q, r]
  field_simp [hd]
  ring

private lemma scalarExtensionMap_bijective :
    letI := coefficientModule θ
    Function.Bijective (scalarExtensionMap θ β hθ) := by
  let := coefficientModule θ
  have : Module.Finite E (Space s) := Module.Finite.of_finite
  have hd : Module.finrank L (L ⊗[E] Space s) = Module.finrank L (Mat L) := by
    rw [Module.finrank_baseChange, coefficient_finrank θ]
    simp [Mat, Module.finrank_matrix]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
    (scalarExtensionMap_surjective θ β hθ), scalarExtensionMap_surjective θ β hθ⟩

variable [CharP L 2] [PerfectRing L 2]
    (e : K →+* L) (f : K ≃+* Field s) (j : ℕ)
    (hf : ∀ x, β (f x) = e x ^ (2 ^ j))

include hf in
private lemma entryMap_intertwines (g : SL(2,K)) (X : Space s) :
    letI := coefficientModule θ
    entryMap θ β hθ (model θ f g X) = pair e s j g (entryMap θ β hθ X) := by
  let := coefficientModule θ
  change (model θ f g X).val.map β = pair e s j g (X.val.map β)
  rw [model_apply, Matrix.map_mul, Matrix.map_mul, pair_apply]
  have hA : (g.val.map f).map β = g.val.map (fun x => e x ^ (2 ^ j)) := by
    ext a b
    exact hf _
  have hB : (adjoint (conjugation s) (g.val.map f)).map β =
      (g.val.map (fun x => e x ^ (2 ^ (j+s)))).transpose := by
    ext a b
    change β (conjugation s (f (g.val b a))) = _
    change β ((f (g.val b a)) ^ (2 ^ s)) = _
    rw [map_pow, hf, ← pow_mul, ← pow_add]
    rfl
  rw [hA, hB]

include hf in
private lemma scalarExtensionMap_intertwines (g : SL(2,K)) :
    letI := coefficientModule θ
    (scalarExtensionMap θ β hθ).comp (extendScalars L (model θ f) g) =
      (pair e s j g).comp (scalarExtensionMap θ β hθ) := by
  let := coefficientModule θ
  apply TensorProduct.AlgebraTensorModule.ext
  intro c X
  simp only [LinearMap.comp_apply, extendScalars_apply, LinearMap.baseChange_tmul,
    scalarExtensionMap_tmul, map_smul]
  exact congrArg (fun Y : Mat L => c • Y) (entryMap_intertwines θ β hθ e f j hf g X)

/-- Scalar extension of the actual Hermitian action is the Frobenius matrix
pair action, via the entrywise embedding of Hermitian matrices. -/
def scalarExtensionEquiv :
    letI := coefficientModule θ
    (extendScalars L (model θ f)).Equiv (pair e s j) := by
  let := coefficientModule θ
  exact Representation.Equiv.mk
    (LinearEquiv.ofBijective (scalarExtensionMap θ β hθ) (scalarExtensionMap_bijective θ β hθ))
    (scalarExtensionMap_intertwines θ β hθ e f j hf)

/-- The representation equivalence retains the prescribed pure-tensor map. -/
@[simp] theorem scalarExtensionEquiv_tmul (c : L) (X : Space s) :
    letI := coefficientModule θ
    scalarExtensionEquiv θ β hθ e f j hf (c ⊗ₜ[E] X) = c • X.val.map β := (rfl)

include hθ hf in
/-- The Hermitian scalar-extension comparison under exactly the two compatible
field-identification hypotheses. -/
theorem nonempty_extendScalars_model_equiv_pair :
    letI := coefficientModule θ
    Nonempty ((extendScalars L (model θ f)).Equiv (pair e s j)) :=
  ⟨scalarExtensionEquiv θ β hθ e f j hf⟩

end
end Representation.SL2.BinaryHermitian
