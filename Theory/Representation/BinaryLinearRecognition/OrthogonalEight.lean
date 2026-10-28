module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Mathlib.RepresentationTheory.Basic

/-!
# The literal six-dimensional orthogonal action of A₈

Restrict the checked deleted-module embedding S₈ → O⁺₆(2) to A₈ and
forget the isometry proof to obtain its binary representation. The action
is faithful and preserves the explicit split quadratic form. The imported
ATLAS comparison supplies the actual PSL₄(2) ≃ A₈ equivalence; all ATLAS
source attribution and licensing remain in its owning modules.

This is the model in Aschbacher--Smith G.9.3(12), printed p.354.
It is not an assertion that these are all small irreducible modules.
-/

@[expose] public section
namespace Representation.BinaryLinearRecognition
open Atlas.Order20160A8

/-- The actual alternating subgroup acting on the split quadratic six-space. -/
noncomputable def orthogonalEightAction : Representation (ZMod 2)
    (alternatingGroup (Fin 8)) (ClassicalOrthogonal.VectorD 3 (ZMod 2)) where
  toFun g := (DeletedEight.orthogonalHom g.val).val.toLinearMap
  map_one' := by
    change (DeletedEight.orthogonalHom 1).val.toLinearMap = 1
    rw [map_one]
    rfl
  map_mul' g h := by
    change (DeletedEight.orthogonalHom (g.val * h.val)).val.toLinearMap = _
    rw [map_mul]
    rfl

/-- Faithfulness is inherited from the deleted permutation action. -/
theorem orthogonalEightAction_injective : Function.Injective orthogonalEightAction := by
  intro x y hxy
  apply Subtype.ext
  apply DeletedEight.orthogonalHom_injective
  apply Subtype.ext
  exact LinearEquiv.toLinearMap_injective hxy

/-- The representation preserves the literal split quadratic form. -/
theorem orthogonalEightAction_preserves_form (g : alternatingGroup (Fin 8)) (v : ClassicalOrthogonal.VectorD 3 (ZMod 2)) :
    ClassicalOrthogonal.formD 3 (ZMod 2) (orthogonalEightAction g v) =
      ClassicalOrthogonal.formD 3 (ZMod 2) v :=
  (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp
    (DeletedEight.orthogonalHom g.val).property v

/-- The split space has binary dimension six. -/
theorem finrank_orthogonalEight : Module.finrank (ZMod 2) (ClassicalOrthogonal.VectorD 3 (ZMod 2)) = 6 := by
  simp [ClassicalOrthogonal.VectorD, ClassicalOrthogonal.Index]

end Representation.BinaryLinearRecognition
