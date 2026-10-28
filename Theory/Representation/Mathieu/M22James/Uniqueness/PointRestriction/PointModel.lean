module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Coordinates
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Generators
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.GroupComparison
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension

/-!
# Concrete data for the Mathieu point-stabilizer comparison

The actual restricted module has a specified invariant subspace of binary
dimension six and field dimension three. Its coordinates retain the actual
central scalar. A checked linear equivalence on the entire binary space
carries this subspace onto the first block of an explicit classical extension
candidate. Explicit Schreier words belong to the literal point stabilizer.

The stabilizer is identified with SL₃(4), with its distinguished scalar and
Schreier generation retained. The checked coordinates give an actual
equivalence from the literal point representation to the explicit nonsplit
natural-by-dual reference representation. This is the concrete model used by
the recognition theorem; it does not assert James's uniqueness theorem.

Source: James (1973), Lemma 8.3, as used in Aschbacher–Smith H.12.1,
printed pp.393–394.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

/-! The final assembly has no abstract group or matrix premises left: the
published group comparison supplies the equivalence and its natural action,
while the classical-extension module supplies the checked full-space
intertwining. -/

/-- The literal twelve-dimensional point representation is the explicit
natural-by-dual nonsplit representation of `SL₃(4)`, pulled back along the
actual point-stabilizer equivalence. -/
noncomputable def pointRepresentationEquiv :
    pointRepresentation.Equiv
      (Reference.binaryRepresentation.comp pointStabilizerEquiv.toMonoidHom) :=
  representationEquiv pointStabilizerEquiv
    pointStabilizerEquiv_natural_action closure_schreierGenerators_eq_top

lemma pointRepresentationEquiv_toLinearEquiv :
    pointRepresentationEquiv.toLinearEquiv = coordinates := rfl

/-- The comparison fixes the central field marking: the distinguished scalar
acts as the specified diagonal matrix `ω I₃`. -/
lemma pointRepresentationEquiv_pointScalar :
    pointStabilizerEquiv pointScalar = Reference.scalar :=
  pointStabilizerEquiv_pointScalar

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
