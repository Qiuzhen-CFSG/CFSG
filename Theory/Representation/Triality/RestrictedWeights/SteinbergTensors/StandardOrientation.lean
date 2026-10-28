module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.Orientation
public import Theory.SpecificGroups.Triality.StandardModel
public import Theory.Representation.Triality.BinaryDegree.TensorDescent

/-!
# Comparing the two existing triality conventions

The genuine Geck `StandardModel` composes diagram then field. On its fixed
points the field automorphism is therefore the inverse diagram automorphism.
The diagram action on binary labels agrees definitionally with `twistWeight`
in the degree-descent consumer. These identities check orientation only; they
do not compare the adjoint Geck model with a simply connected algebraic model.

Source: GLS3, Remark 2.8.8.
-/

public section

namespace Triality.RestrictedWeights.SteinbergTensors
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

/-- The finite standard model really uses inverse graph pullback at overflow. -/
theorem standard_field_eq_inverse_diagram (P : Standard.Parameters)
    (g : Standard.fixedSubgroup P) :
    Standard.fieldAutomorphism P g.val = (Standard.diagramAutomorphism P).symm g.val :=
  field_eq_inverse_graph (Standard.diagramAutomorphism P)
    (Standard.fieldAutomorphism P).toMonoidHom
    (fun x => (Standard.diagram_field_commute P x).symm) g.property

/-- The forward sequence twist is exactly the existing consumer's convention. -/
theorem diagramAction_eq_twistWeight (a : BasicWeight) :
    diagramAction a = BinaryDegree.twistWeight a := rfl

/-- The constructed sequence satisfies the actual consumer's wrap equation. -/
theorem extendWeights_tensorData_wrap {n : ℕ} (hn : 0 < n)
    (a : Fin n → BasicWeight) (i : ℕ) :
    extendWeights hn a (i + n) = BinaryDegree.twistWeight (extendWeights hn a i) :=
  extendWeights_wrap hn a i

end Triality.RestrictedWeights.SteinbergTensors
