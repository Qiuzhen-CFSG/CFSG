module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Coordinates
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Generators
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.Nonsplitting
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.SchreierIntertwining
/-!
# The classical nonsplit Mathieu point-restriction model

The reference operators form an actual representation. Its first block is
natural and its quotient is Frobenius inverse-transpose natural; over the
binary field the quotient is the actual dual. The extension is nonsplit even
for binary-linear sections.

The checked Schreier identities propagate to the whole stabilizer through
the full-space coordinates. The resulting representation equivalence assumes
precisely a group equivalence with SL₃(4), its specified action on the geometric
natural submodule, and generation by the actual Schreier words. All finite
matrix and intertwining identities are discharged here. Constructing those
three group inputs remains with the independent group comparison and the
unconditional point-model assembly.

Source: James (1973), Lemma 8.3, as used in Aschbacher–Smith H.12.1,
printed pp.393–394.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix

/-- Once the finite Schreier identities have been checked, generation extends
 them to every stabilizer element. -/
lemma coordinates_equivariant_of_schreier
    (e : pointStabilizer ≃* Reference.SL)
    (hgen : Subgroup.closure schreierGenerators = ⊤)
    (hsch : ∀ (i : Fin 22) (j : Fin 2) (v : BinarySpace),
      coordinates (pointRepresentation (schreierGenerator i j) v) =
        Reference.operator (e (schreierGenerator i j)) (coordinates v))
    (g : pointStabilizer) (v : BinarySpace) :
    coordinates (pointRepresentation g v) = Reference.operator (e g) (coordinates v) := by
  let ρ : Representation (ZMod 2) pointStabilizer Reference.V :=
    coordinates.conjRingEquiv.toMonoidHom.comp pointRepresentation
  let σ : Representation (ZMod 2) pointStabilizer Reference.V :=
    Reference.binaryRepresentation.comp e.toMonoidHom
  have heq : ρ = σ := MonoidHom.eq_of_eqOn_dense hgen (by
    rintro _ ⟨⟨i,j⟩, rfl⟩
    apply LinearMap.ext
    intro w
    change coordinates (pointRepresentation (schreierGenerator i j) (coordinates.symm w)) =
      Reference.operator (e (schreierGenerator i j)) w
    rw [hsch, coordinates.apply_symm_apply])
  have h := LinearMap.congr_fun (DFunLike.congr_fun heq g) (coordinates v)
  change coordinates (pointRepresentation g (coordinates.symm (coordinates v))) =
    Reference.operator (e g) (coordinates v) at h
  simpa only [coordinates.symm_apply_apply] using h

/-- An actual representation equivalence from any supplied finite checks. -/
def representationEquiv_of_schreier
    (e : pointStabilizer ≃* Reference.SL)
    (hgen : Subgroup.closure schreierGenerators = ⊤)
    (hsch : ∀ (i : Fin 22) (j : Fin 2) (v : BinarySpace),
      coordinates (pointRepresentation (schreierGenerator i j) v) =
        Reference.operator (e (schreierGenerator i j)) (coordinates v)) :
    pointRepresentation.Equiv (Reference.binaryRepresentation.comp e.toMonoidHom) :=
  Representation.Equiv.mk coordinates (by
    intro g
    apply LinearMap.ext
    exact coordinates_equivariant_of_schreier e hgen hsch g)

/-- The specified full-space coordinates intertwine every stabilizer element.
Only the group comparison, its action on the geometric natural submodule, and
Schreier generation are inputs; the finite whole-module checks are proved. -/
theorem coordinates_equivariant
    (e : pointStabilizer ≃* Reference.SL)
    (hnatural : ∀ (g : pointStabilizer) (w : Reference.W),
      pointRepresentation g (PointModel.naturalInclusion w) =
        PointModel.naturalInclusion ((e g).val *ᵥ w))
    (hgen : Subgroup.closure schreierGenerators = ⊤)
    (g : pointStabilizer) (v : BinarySpace) :
    coordinates (pointRepresentation g v) = Reference.operator (e g) (coordinates v) :=
  coordinates_equivariant_of_schreier e hgen
    (fun i j => coordinates_schreierGenerator i j (e (schreierGenerator i j))
      (hnatural (schreierGenerator i j))) g v

/-- The actual binary point representation is equivalent, via `coordinates`,
to the classical nonsplit natural-by-dual model pulled back along `e`. -/
def representationEquiv
    (e : pointStabilizer ≃* Reference.SL)
    (hnatural : ∀ (g : pointStabilizer) (w : Reference.W),
      pointRepresentation g (PointModel.naturalInclusion w) =
        PointModel.naturalInclusion ((e g).val *ᵥ w))
    (hgen : Subgroup.closure schreierGenerators = ⊤) :
    pointRepresentation.Equiv (Reference.binaryRepresentation.comp e.toMonoidHom) :=
  Representation.Equiv.mk coordinates (by
    intro g
    apply LinearMap.ext
    exact coordinates_equivariant e hnatural hgen g)

lemma representationEquiv_toLinearEquiv
    (e : pointStabilizer ≃* Reference.SL)
    (hnatural : ∀ (g : pointStabilizer) (w : Reference.W),
      pointRepresentation g (PointModel.naturalInclusion w) =
        PointModel.naturalInclusion ((e g).val *ᵥ w))
    (hgen : Subgroup.closure schreierGenerators = ⊤) :
    (representationEquiv e hnatural hgen).toLinearEquiv = coordinates := rfl

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
