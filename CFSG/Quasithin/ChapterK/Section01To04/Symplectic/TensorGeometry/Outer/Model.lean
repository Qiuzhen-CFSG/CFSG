module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Plane

/-!
# A concrete Hermitian model for the symplectic tensor

The fixed matrices of conjugate transposition carry the coefficient-twisted
matrix action already constructed in `Plane`. Transposition on this fixed
space is the coefficient-field involution and intertwines the literal field
automorphism of the symplectic group. The coordinates theorem connects this
action with the original tensor product. Fixed and displacement subspaces and
the common fixed space with a native actor are defined for further calculations.

This is a concrete model, not yet an identification of the original descended
module. Its scalar-extension equivalence, section dimensions and original-module
transport remain separate obligations. The construction follows the analogous
`Theory.Representation.HermitianTensorThree` definitions.
Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457, and H.4.4(6), p.381.
-/

@[expose] public section

open Matrix Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (σ : F ≃ₐ[k] F)

noncomputable def adjoint (X : Mat (F := F)) : Mat (F := F) := X.transpose.map σ

lemma adjoint_mul (X Y : Mat (F := F)) : adjoint σ (X * Y) = adjoint σ Y * adjoint σ X := by
  simp only [adjoint, Matrix.transpose_mul, Matrix.map_mul]

lemma adjoint_involutive (hσ : Function.Involutive σ) : Function.Involutive (adjoint σ) := by
  intro X
  ext i j
  exact hσ (X i j)

lemma adjoint_action (hσ : Function.Involutive σ) (g : Sp F) (X : Mat (F := F)) :
    adjoint σ (matrixAction σ.toRingEquiv g X) = matrixAction σ.toRingEquiv g (adjoint σ X) := by
  change adjoint σ (g.val * X * adjoint σ g.val) = g.val * adjoint σ X * adjoint σ g.val
  rw [adjoint_mul, adjoint_mul, adjoint_involutive σ hσ, Matrix.mul_assoc]

noncomputable def hermitian (hσ : Function.Involutive σ) :
    Subrepresentation (restrictScalars (k := k) (matrixAction σ.toRingEquiv)) where
  toSubmodule := {
    carrier := {X | adjoint σ X = X}
    zero_mem' := by ext i j; exact map_zero σ
    add_mem' := by
      intro X Y hX hY
      change adjoint σ (X + Y) = X + Y
      have he : adjoint σ (X + Y) = adjoint σ X + adjoint σ Y := by
        ext i j; exact map_add σ _ _
      rw [he, hX, hY]
    smul_mem' := by
      intro c X hX
      change adjoint σ (c • X) = c • X
      have he : adjoint σ (c • X) = c • adjoint σ X := by
        ext i j; exact σ.toLinearMap.map_smul c (X j i)
      rw [he, hX] }
  apply_mem_toSubmodule := by
    intro g X hX
    change adjoint σ (matrixAction σ.toRingEquiv g X) = matrixAction σ.toRingEquiv g X
    rw [adjoint_action σ hσ, hX]

noncomputable abbrev Space (hσ : Function.Involutive σ) := (hermitian σ hσ).toSubmodule

noncomputable def action (hσ : Function.Involutive σ) :
    Representation k (Sp F) (Space σ hσ) := (hermitian σ hσ).toRepresentation

lemma action_apply (hσ : Function.Involutive σ) (g : Sp F) (X : Space σ hσ) :
    (action σ hσ g X).val = matrixAction σ.toRingEquiv g X.val := rfl

lemma tensor_intertwines (hσ : Function.Involutive σ) (g : Sp F) (X : Space σ hσ) :
    coordinates.symm (action σ hσ g X).val =
      twistedTensor σ.toRingEquiv g (coordinates.symm X.val) := by
  apply coordinates.injective
  rw [LinearEquiv.apply_symm_apply, coordinates_action, LinearEquiv.apply_symm_apply]
  rfl

lemma entry_conjugate (hσ : Function.Involutive σ) (X : Space σ hσ)
    (i j : Fin 2 ⊕ Fin 2) : σ (X.val j i) = X.val i j :=
  congrFun (congrFun X.property i) j

noncomputable def fieldSwap (hσ : Function.Involutive σ) : Space σ hσ ≃ₗ[k] Space σ hσ where
  toFun X := ⟨X.val.transpose, by ext i j; exact entry_conjugate σ hσ X j i⟩
  invFun X := ⟨X.val.transpose, by ext i j; exact entry_conjugate σ hσ X j i⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma fieldSwap_apply (hσ : Function.Involutive σ) (X : Space σ hσ) :
    (fieldSwap σ hσ X).val = X.val.transpose := rfl

lemma fieldSwap_eq_map (hσ : Function.Involutive σ) (X : Space σ hσ) :
    (fieldSwap σ hσ X).val = X.val.map σ := by
  ext i j
  exact (entry_conjugate σ hσ X j i).symm

lemma fieldSwap_sq (hσ : Function.Involutive σ) : fieldSwap σ hσ * fieldSwap σ hσ = 1 := by
  ext X i j
  rfl

lemma fieldSwap_action (hσ : Function.Involutive σ) (g : Sp F) (X : Space σ hσ) :
    fieldSwap σ hσ (action σ hσ g X) =
      action σ hσ (fieldAutomorphism σ.toRingEquiv g) (fieldSwap σ hσ X) := by
  apply Subtype.ext
  change (g.val * X.val * adjoint σ g.val).transpose =
    g.val.map σ * X.val.transpose * adjoint σ (g.val.map σ)
  have he : adjoint σ (g.val.map σ) = g.val.transpose := by
    ext i j
    exact hσ (g.val j i)
  rw [he, Matrix.transpose_mul, Matrix.transpose_mul]
  exact (Matrix.mul_assoc _ _ _).symm

noncomputable def fieldFixed (hσ : Function.Involutive σ) : Submodule k (Space σ hσ) :=
  LinearMap.ker ((fieldSwap σ hσ).toLinearMap - LinearMap.id)

noncomputable def fieldMoved (hσ : Function.Involutive σ) : Submodule k (Space σ hσ) :=
  LinearMap.range ((fieldSwap σ hσ).toLinearMap - LinearMap.id)

lemma mem_fieldFixed (hσ : Function.Involutive σ) (X : Space σ hσ) :
    X ∈ fieldFixed σ hσ ↔ X.val.transpose = X.val := by
  change fieldSwap σ hσ X - X = 0 ↔ _
  rw [sub_eq_zero, Subtype.ext_iff]
  rfl

noncomputable def commonFixed (hσ : Function.Involutive σ) (B : Subgroup (Sp F)) :
    Submodule k (Space σ hσ) :=
  fieldFixed σ hσ ⊓ Representation.invariants ((action σ hσ).comp B.subtype)

lemma mem_commonFixed (hσ : Function.Involutive σ) (B : Subgroup (Sp F))
    (X : Space σ hσ) : X ∈ commonFixed σ hσ B ↔
      X.val.transpose = X.val ∧ ∀ b : B, action σ hσ b.val X = X := by
  change (X ∈ fieldFixed σ hσ ∧ _) ↔ _
  rw [mem_fieldFixed]
  rfl

end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model
