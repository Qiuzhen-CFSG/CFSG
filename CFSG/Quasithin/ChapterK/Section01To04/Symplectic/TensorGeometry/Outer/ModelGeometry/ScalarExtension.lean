module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.ModelGeometry.Coordinates

/-!
# Scalar extension of the Hermitian symplectic model

The canonical map sends `c ⊗ X` to `c • X.val`. For a coefficient `t` moved
by conjugation, the two Hermitian matrices `X + X*` and `σ(t)X + tX*`
span `X` over the extension field. This proves surjectivity, and the checked
dimension 16 proves injectivity. The pure-tensor equation directly intertwines
the extended model action with the literal coefficient-twisted matrix action.
No identification by dimension alone is used.

Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457; compare the scalar
extension argument in `Theory.Representation.SL2.BinaryHermitianRecognition`.
-/

@[expose] public section

open Matrix Representation
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
noncomputable section
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ)

open scoped TensorProduct

/-- The literal scalar-extension map sends a pure tensor to scalar multiplication
of its Hermitian matrix. -/
def scalarExtensionMap : F ⊗[k] Space σ hσ →ₗ[F] Mat (F := F) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun c => c • (hermitian σ hσ).toSubmodule.subtype
      map_add' := by intros; exact add_smul _ _ _
      map_smul' := by intros; exact mul_smul _ _ _ }

@[simp] lemma scalarExtensionMap_tmul (c : F) (X : Space σ hσ) :
    scalarExtensionMap σ hσ (c ⊗ₜ[k] X) = c • X.val := rfl

lemma scalarExtensionMap_surjective (hne : σ ≠ AlgEquiv.refl) :
    Function.Surjective (scalarExtensionMap σ hσ) := by
  have hex : ∃ t : F, σ t ≠ t := by
    by_contra! he
    exact hne (AlgEquiv.ext he)
  obtain ⟨t, ht⟩ := hex
  have hd : t - σ t ≠ 0 := sub_ne_zero.mpr ht.symm
  intro M
  let Y : Space σ hσ := ⟨M + adjoint σ M, by
    ext i j
    change σ (M j i + σ (M i j)) = M i j + σ (M j i)
    rw [map_add, hσ]
    exact add_comm _ _⟩
  let Z : Space σ hσ := ⟨σ t • M + t • adjoint σ M, by
    ext i j
    change σ (σ t * M j i + t * σ (M i j)) = σ t * M i j + t * σ (M j i)
    rw [map_add, map_mul, map_mul, hσ, hσ]
    exact add_comm _ _⟩
  refine ⟨(t / (t - σ t)) ⊗ₜ[k] Y - (1 / (t - σ t)) ⊗ₜ[k] Z, ?_⟩
  rw [map_sub, scalarExtensionMap_tmul, scalarExtensionMap_tmul]
  ext i j
  change t / (t - σ t) * (M i j + σ (M j i)) -
    (1 / (t - σ t)) * (σ t * M i j + t * σ (M j i)) = M i j
  field_simp [hd]
  ring

lemma scalarExtensionMap_bijective [FiniteDimensional k F]
    (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl) :
    Function.Bijective (scalarExtensionMap σ hσ) := by
  have hd : Module.finrank F (F ⊗[k] Space σ hσ) = Module.finrank F (Mat (F := F)) := by
    rw [Module.finrank_baseChange, finrank_space σ hσ hdeg hne]
    simp [Mat, Module.finrank_matrix]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
    (scalarExtensionMap_surjective σ hσ hne), scalarExtensionMap_surjective σ hσ hne⟩

/-- The canonical equivalence with the genuine matrix tensor model. -/
def eM [FiniteDimensional k F]
    (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl) :
    (F ⊗[k] Space σ hσ) ≃ₗ[F] Mat (F := F) :=
  LinearEquiv.ofBijective (scalarExtensionMap σ hσ)
    (scalarExtensionMap_bijective σ hσ hdeg hne)

@[simp] lemma eM_tmul [FiniteDimensional k F]
    (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl)
    (c : F) (X : Space σ hσ) : eM σ hσ hdeg hne (c ⊗ₜ[k] X) = c • X.val := rfl

lemma eM_intertwines [FiniteDimensional k F]
    (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl)
    (g : Sp F) (v : F ⊗[k] Space σ hσ) :
    eM σ hσ hdeg hne (extendScalars F (action σ hσ) g v) =
      matrixAction σ.toRingEquiv g (eM σ hσ hdeg hne v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul c X =>
    rw [extendScalars_apply, LinearMap.baseChange_tmul, eM_tmul, eM_tmul, map_smul]
    rfl


end
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
