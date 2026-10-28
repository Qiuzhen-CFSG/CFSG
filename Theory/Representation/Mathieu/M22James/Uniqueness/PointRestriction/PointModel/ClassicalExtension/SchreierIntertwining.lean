module
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Coordinates
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Generators
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.Multiplication
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.SchreierIntertwining.Edges
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.SchreierIntertwining.Operators

/-!
# Whole-module intertwining for the actual Mathieu Schreier words

The finite certificates in the descendants identify all forty-four literal
Schreier words with nineteen binary matrices and intertwine those matrices
with explicit classical operators. If a supplied special linear element has
the required action on the geometric natural submodule, its natural matrix
agrees with the certified candidate. The same coordinate change therefore
intertwines its action on the whole twelve-dimensional binary module.

This proves the finite comparison with precisely the natural-action hypothesis.
It requires neither a group equivalence nor generation of the point stabilizer.
The separate classical-extension assembly can combine this theorem with those
inputs using its existing propagation lemmas.

Source context: James (1973), Lemma 8.3, used in Aschbacher–Smith H.12.1,
printed pp.393–394; p.394 describes the natural-by-dual point restriction.
Data provenance and a reproducible diagnostic are retained in
`SchreierIntertwining/source/README.md`.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix

private lemma coordinates_schreier_reference (i : Fin 22) (j : Fin 2) (v : BinarySpace) :
    coordinates (pointRepresentation (schreierGenerator i j) v) =
      Reference.operator
        (SchreierCertificate.referenceElement (SchreierCertificate.schreierIndex i j))
        (coordinates v) := by
  apply flattenPair.injective
  rw [coordinates_apply, SchreierCertificate.operator_matrix, coordinates_apply]
  change comparisonMatrix *ᵥ
    ((((schreierGenerator i j).val : Matrix12ˣ) : Matrix12) *ᵥ v) = _
  rw [SchreierCertificate.schreier_matrix, Matrix.mulVec_mulVec,
    SchreierCertificate.conjugacy, Matrix.mulVec_mulVec]

/-- For every literal Schreier word, its action on the geometric natural
submodule determines its action on the whole binary module in the checked
classical coordinates. No generation or group comparison is required. -/
lemma coordinates_schreierGenerator (i : Fin 22) (j : Fin 2) (g : Reference.SL)
    (h : ∀ w : Reference.W,
      pointRepresentation (schreierGenerator i j) (PointModel.naturalInclusion w) =
        PointModel.naturalInclusion (g.val *ᵥ w))
    (v : BinarySpace) :
    coordinates (pointRepresentation (schreierGenerator i j) v) =
      Reference.operator g (coordinates v) := by
  have he : (SchreierCertificate.referenceElement
      (SchreierCertificate.schreierIndex i j)).val = g.val := by
    apply Matrix.ext_iff_mulVec.mpr
    intro w
    have hw := congrArg coordinates (h w)
    rw [coordinates_schreier_reference, coordinates_inclusion,
      Reference.operator_inclusion, coordinates_inclusion] at hw
    exact congrArg Prod.fst hw
  have hg : SchreierCertificate.referenceElement
      (SchreierCertificate.schreierIndex i j) = g := Subtype.ext he
  simpa only [hg] using coordinates_schreier_reference i j v

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
