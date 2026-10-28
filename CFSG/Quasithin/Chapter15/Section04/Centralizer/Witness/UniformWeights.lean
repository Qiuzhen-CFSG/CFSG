module

public import Theory.Representation.AffineNine.BinaryWeights
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The two actual affine-nine uniform-weight consumers

The source models are the literal semidirect products `Special` and `Full`.
The character-coordinate comparison and orbit calculation are discharged by
the natural `SL₂(3)`/`GL₂(3)` actions.  The binary consumers extend the original
representation to the algebraic closure and retain its trivial weight separately.

Source: Aschbacher--Smith, Lemma 15.4.10, printed p.1159; this is the weight
input to the direct fixed-codimension proof, not the full strict-bound theorem.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness

open Representation
open Representation.AffineNine
open Matrix
open scoped MatrixGroups

variable {E V : Type*} [Field E] [IsAlgClosed E]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

private theorem algebraicClosure_translation_order :
    (Nat.card Translation : AlgebraicClosure (ZMod 2)) ≠ 0 := by
  have hcard : Nat.card Translation = 9 := by
    change Nat.card Plane = 9
    rw [Nat.card_eq_fintype_card, card_plane]
  rw [hcard]
  have h8 : (8 : AlgebraicClosure (ZMod 2)) = 0 :=
    (CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod 2)) 2 8).2 (by decide)
  calc
    (9 : AlgebraicClosure (ZMod 2)) = 8 + 1 := by norm_num
    _ = 1 := by rw [h8, zero_add]
    _ ≠ 0 := one_ne_zero

/-- Uniform nontrivial translation weights for the actual full affine-nine
model, from the contragredient character comparison. -/
public noncomputable def full_uniformWeights
    (rho : Representation E Full V) (hfaith : Function.Injective rho)
    (horder : (Nat.card Translation : E) ≠ 0)
    (coords : CharacterCoordinates (E := E) (MonoidHom.id LinearGroup)) :
    UniformWeights (MonoidHom.id LinearGroup) rho := by
  apply uniformWeights_of_transitive (j := (MonoidHom.id LinearGroup)) rho hfaith horder
  exact characterTransitive_of_coordinates (E := E)
    (j := (MonoidHom.id LinearGroup))
    coords dualPerm_full_transitive

/-- Uniform nontrivial translation weights for the actual special affine-nine
model, from the contragredient character comparison. -/
public noncomputable def special_uniformWeights
    (rho : Representation E Special V) (hfaith : Function.Injective rho)
    (horder : (Nat.card Translation : E) ≠ 0)
    (coords : CharacterCoordinates (E := E)
      (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup)) :
    UniformWeights (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup) rho := by
  apply uniformWeights_of_transitive
    (j := (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup)) rho hfaith horder
  exact characterTransitive_of_coordinates (E := E)
    (j := (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup))
    coords dualPerm_special_transitive

/-- The full-model consumer over the specified algebraic closure of the binary
base field.  A scalar-extended faithful binary action supplies `rho` and the
coordinate comparison. -/
public noncomputable def full_uniformWeights_algebraicClosure
    {W : Type*} [AddCommGroup W]
    [Module (AlgebraicClosure (ZMod 2)) W]
    [FiniteDimensional (AlgebraicClosure (ZMod 2)) W]
    (rho : Representation (AlgebraicClosure (ZMod 2)) Full W)
    (hfaith : Function.Injective rho)
    (coords : CharacterCoordinates (E := AlgebraicClosure (ZMod 2))
      (MonoidHom.id LinearGroup)) :
    UniformWeights (MonoidHom.id LinearGroup) rho :=
  full_uniformWeights rho hfaith algebraicClosure_translation_order coords

/-- The special-model consumer over the specified algebraic closure of the
binary base field. -/
public noncomputable def special_uniformWeights_algebraicClosure
    {W : Type*} [AddCommGroup W]
    [Module (AlgebraicClosure (ZMod 2)) W]
    [FiniteDimensional (AlgebraicClosure (ZMod 2)) W]
    (rho : Representation (AlgebraicClosure (ZMod 2)) Special W)
    (hfaith : Function.Injective rho)
    (coords : CharacterCoordinates (E := AlgebraicClosure (ZMod 2))
      (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup)) :
    UniformWeights (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup) rho :=
  special_uniformWeights rho hfaith algebraicClosure_translation_order coords

/-- The full affine-nine uniformity result with the canonical character table
over `AlgebraicClosure (ZMod 2)`. -/
public noncomputable def full_uniformWeights_algebraicClosure_model
    {W : Type*} [AddCommGroup W]
    [Module (AlgebraicClosure (ZMod 2)) W]
    [FiniteDimensional (AlgebraicClosure (ZMod 2)) W]
    (rho : Representation (AlgebraicClosure (ZMod 2)) Full W)
    (hfaith : Function.Injective rho) :
    UniformWeights (MonoidHom.id LinearGroup) rho :=
  full_uniformWeights_algebraicClosure rho hfaith
    algebraicClosureFullCharacterCoordinates

/-- The special affine-nine uniformity result with the canonical character
table over `AlgebraicClosure (ZMod 2)`. -/
public noncomputable def special_uniformWeights_algebraicClosure_model
    {W : Type*} [AddCommGroup W]
    [Module (AlgebraicClosure (ZMod 2)) W]
    [FiniteDimensional (AlgebraicClosure (ZMod 2)) W]
    (rho : Representation (AlgebraicClosure (ZMod 2)) Special W)
    (hfaith : Function.Injective rho) :
    UniformWeights (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup) rho :=
  special_uniformWeights_algebraicClosure rho hfaith
    algebraicClosureSpecialCharacterCoordinates

/-- The exact full-model binary input to the affine fixed-codimension bound.
The common positive dimension applies precisely to the eight nonzero points;
the zero weight has the original translation-fixed dimension. -/
public theorem full_binary_weight_dimensions
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (rho : Representation (ZMod 2) Full W) (hfaith : Function.Injective rho) :
    ∃ m : ℕ, 0 < m ∧
      (∀ w : Plane, w ≠ 0 → Module.finrank algebraicClosureE9
        (planeWeightSpace (MonoidHom.id LinearGroup)
          (rho.extendScalars algebraicClosureE9) w) = m) ∧
      Module.finrank algebraicClosureE9
        (planeWeightSpace (MonoidHom.id LinearGroup)
          (rho.extendScalars algebraicClosureE9) 0) =
        Module.finrank (ZMod 2)
          (translationRepresentation (MonoidHom.id LinearGroup) rho).invariants := by
  let u := full_binary_uniformWeights rho hfaith
  refine ⟨u.nontrivialDim, u.positive, ?_, ?_⟩
  · exact planeWeightSpace_finrank_nonzero _ _ u
  · exact finrank_planeWeightSpace_zero_extendScalars _ rho

/-- The exact special-model binary input, with both the character comparison
and the transitivity of the determinant-one complement discharged. -/
public theorem special_binary_weight_dimensions
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (rho : Representation (ZMod 2) Special W) (hfaith : Function.Injective rho) :
    ∃ m : ℕ, 0 < m ∧
      (∀ w : Plane, w ≠ 0 → Module.finrank algebraicClosureE9
        (planeWeightSpace (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup)
          (rho.extendScalars algebraicClosureE9) w) = m) ∧
      Module.finrank algebraicClosureE9
        (planeWeightSpace (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup)
          (rho.extendScalars algebraicClosureE9) 0) =
        Module.finrank (ZMod 2)
          (translationRepresentation (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup)
            rho).invariants := by
  let u := special_binary_uniformWeights rho hfaith
  refine ⟨u.nontrivialDim, u.positive, ?_, ?_⟩
  · exact planeWeightSpace_finrank_nonzero _ _ u
  · exact finrank_planeWeightSpace_zero_extendScalars _ rho

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness
