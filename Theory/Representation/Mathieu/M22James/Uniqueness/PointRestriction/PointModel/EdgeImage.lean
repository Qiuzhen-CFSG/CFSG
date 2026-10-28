module
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.EdgeImage.Generation
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Coordinates
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Generators
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.SchreierIntertwining.Edges
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.SchreierIntertwining.Operators

/-!
# Images of the literal point-stabilizer Schreier words

The accepted binary matrix and conjugacy certificates give the reference
operator of each literal edge word. Applying the geometric coordinate map to
an asserted natural action and taking the first block identifies its three
by three matrix. Thus every homomorphism realizing that natural action sends
each edge to its actual certified reference element.

The independent structural generation result in `EdgeImage.Generation` then
proves that the edge images generate SL₃(4), and hence that the homomorphism
is surjective. No generation of the point stabilizer or group equivalence is
assumed. Those remaining inputs belong to the group-comparison assembly.

Source context: James (1973), Lemma 8.3, used in Aschbacher–Smith H.12.1,
printed pp.393–394. In particular p.394 identifies the point stabilizer with
SL₃(4) and describes the natural-by-dual restriction. This module supplies the
edge-image ingredient, rather than claiming the whole source theorem.
The field encoding remains 0, 1, omega, 1 + omega, with geometric columns
54, 93, 407 and omega acting as 1 + J. Original ATLAS attribution is retained
in `PointModel/source/README.md` and the accepted certificate source notes.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix

private lemma edge_coordinates_reference (i : Fin 22) (j : Fin 2) (v : BinarySpace) :
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

/-- Compatibility with the geometric natural submodule determines the image
of every literal Schreier word. -/
lemma schreierGenerator_image_of_natural_action (f : pointStabilizer →* Reference.SL)
    (h : ∀ (g : pointStabilizer) (w : Reference.W),
      pointRepresentation g (naturalInclusion w) = naturalInclusion ((f g).val *ᵥ w))
    (i : Fin 22) (j : Fin 2) :
    f (schreierGenerator i j) =
      SchreierCertificate.referenceElement (SchreierCertificate.schreierIndex i j) := by
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro w
  have hw := congrArg coordinates (h (schreierGenerator i j) w)
  rw [edge_coordinates_reference, coordinates_inclusion,
    Reference.operator_inclusion, coordinates_inclusion] at hw
  exact (congrArg Prod.fst hw).symm

/-- The images of the literal Schreier words generate SL₃(4), using only
compatibility with the geometric natural action. -/
lemma closure_image_schreierGenerators_of_natural_action
    (f : pointStabilizer →* Reference.SL)
    (h : ∀ (g : pointStabilizer) (w : Reference.W),
      pointRepresentation g (naturalInclusion w) = naturalInclusion ((f g).val *ᵥ w)) :
    Subgroup.closure (f '' schreierGenerators) = ⊤ := by
  have hr : f '' schreierGenerators = Set.range (fun ij : Fin 22 × Fin 2 =>
      SchreierCertificate.referenceElement (SchreierCertificate.schreierIndex ij.1 ij.2)) := by
    ext g
    constructor
    · rintro ⟨x, ⟨ij, rfl⟩, rfl⟩
      exact ⟨ij, (schreierGenerator_image_of_natural_action f h ij.1 ij.2).symm⟩
    · rintro ⟨ij, rfl⟩
      exact ⟨schreierGenerator ij.1 ij.2, ⟨ij, rfl⟩,
        schreierGenerator_image_of_natural_action f h ij.1 ij.2⟩
  rw [hr, EdgeImage.closure_range_schreierReference]

/-- Every homomorphism realizing this natural action is onto SL₃(4). -/
lemma surjective_of_natural_action (f : pointStabilizer →* Reference.SL)
    (h : ∀ (g : pointStabilizer) (w : Reference.W),
      pointRepresentation g (naturalInclusion w) = naturalInclusion ((f g).val *ᵥ w)) :
    Function.Surjective f := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← closure_image_schreierGenerators_of_natural_action f h]
  apply (Subgroup.closure_le f.range).mpr
  rintro _ ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
