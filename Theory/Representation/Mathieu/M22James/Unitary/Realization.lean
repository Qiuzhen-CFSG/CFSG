module
public import Theory.Representation.Mathieu.M22James.Unitary.Forms

/-!
# Faithful realization in the literal SU₆(2) model

Apply the fixed `SL2FourNatural.fieldEquiv` to every coordinate and matrix
entry. This intertwines Frobenius and preserves the identity Hermitian form.
Perfectness gives determinant one in the target field. The resulting faithful
homomorphism lands in `U6Two.form.specialSubgroup`, and an actual binary linear
equivalence intertwines its column action with `binaryRepresentation`.
The scalar and form identities retain the exact central-field structure and
its relationship to the standard unitary coordinates.

Source: Aschbacher–Smith H.12.1(2), printed pp.393–394. This is the concrete
native-cover realization; arbitrary-cover transport is owned by the chapter
recognition assembly. ATLAS provenance is retained in `Data` and its imports.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Unitary
open Matrix Representation.SL2FourNatural
open Uniqueness.PointRestriction (fieldModule)
open Theory.SpecificGroups
open scoped Matrix

local instance : Module F BinarySpace :=
  fieldModule binaryRepresentation binaryRepresentation_faithful

def coefficientEquiv : Vector ≃ₗ[ZMod 2] (Fin 6 → U6Two.Field) where
  toFun v i := fieldEquiv (v i)
  invFun v i := fieldEquiv.symm (v i)
  left_inv v := by funext i; exact fieldEquiv.symm_apply_apply _
  right_inv v := by funext i; exact fieldEquiv.apply_symm_apply _
  map_add' v w := by funext i; exact map_add _ _ _
  map_smul' c v := by
    funext i
    change fieldEquiv (c • v i) = c • fieldEquiv (v i)
    fin_cases c
    · change fieldEquiv ((0 : ZMod 2) • v i) = (0 : ZMod 2) • _
      simp
    · change fieldEquiv ((1 : ZMod 2) • v i) = (1 : ZMod 2) • _
      simp

/-- Actual binary coordinates in the standard unitary model. -/
def standardCoordinates : BinarySpace ≃ₗ[ZMod 2] (Fin 6 → U6Two.Field) :=
  binaryCoordinates.trans coefficientEquiv

theorem standardCoordinates_apply (v : BinarySpace) (i : Fin 6) :
    standardCoordinates v i = fieldEquiv (coordinates v i) := rfl

/-- Compatibility with the specified central field, through the fixed field isomorphism. -/
theorem standardCoordinates_smul (a : F) (v : BinarySpace) :
    standardCoordinates (a • v) = fieldEquiv a • standardCoordinates v := by
  funext i
  simp only [standardCoordinates_apply, map_smul, Pi.smul_apply, smul_eq_mul, map_mul]

def standardMatrixAction : M22TripleCover →* GL (Fin 6) U6Two.Field :=
  (Matrix.GeneralLinearGroup.map fieldEquiv.toRingHom).comp matrixAction

theorem standardMatrixAction_intertwines (g : M22TripleCover) (v : BinarySpace) :
    (standardMatrixAction g : Matrix (Fin 6) (Fin 6) U6Two.Field) *ᵥ
      standardCoordinates v = standardCoordinates (binaryRepresentation g v) := by
  funext i
  have h := congrArg (fun x : Vector => fieldEquiv (x i)) (matrixAction_intertwines g v)
  change (∑ j, fieldEquiv ((matrixAction g : Matrix _ _ F) i j) *
    fieldEquiv (coordinates v j)) = fieldEquiv (coordinates (binaryRepresentation g v) i)
  simpa only [mulVec, dotProduct, map_sum, map_mul] using h

theorem standardMatrixAction_faithful : Function.Injective standardMatrixAction := by
  intro g h he
  apply binaryRepresentation_faithful
  apply LinearMap.ext
  intro v
  apply standardCoordinates.injective
  rw [← standardMatrixAction_intertwines, ← standardMatrixAction_intertwines, he]

private theorem map_adjoint (A : Matrix (Fin 6) (Fin 6) F) :
    (A.transpose.map fieldFrobenius).map fieldEquiv =
      U6Two.form.conjTranspose (A.map fieldEquiv) := by
  funext i j
  change fieldEquiv (fieldFrobenius (A j i)) = U6Two.conjugation (fieldEquiv (A j i))
  rw [fieldFrobenius_apply, U6Two.conjugation_apply, map_pow]

private theorem mapped_unitary (A : GL (Fin 6) F)
    (hA : (A : Matrix (Fin 6) (Fin 6) F).transpose.map fieldFrobenius *
      (A : Matrix (Fin 6) (Fin 6) F) = 1) :
    Matrix.GeneralLinearGroup.map fieldEquiv.toRingHom A ∈ U6Two.form.unitarySubgroup := by
  have hh := congrArg (RingHom.mapMatrix fieldEquiv.toRingHom) hA
  rw [map_mul, map_one] at hh
  change ((A : Matrix (Fin 6) (Fin 6) F).transpose.map fieldFrobenius).map fieldEquiv *
    (A : Matrix (Fin 6) (Fin 6) F).map fieldEquiv = 1 at hh
  rw [map_adjoint] at hh
  change U6Two.form.conjTranspose ((A : Matrix (Fin 6) (Fin 6) F).map fieldEquiv) *
    1 * (A : Matrix (Fin 6) (Fin 6) F).map fieldEquiv = 1
  simpa only [mul_one] using hh

theorem standardMatrixAction_unitary (g : M22TripleCover) :
    standardMatrixAction g ∈ U6Two.form.unitarySubgroup :=
  mapped_unitary (matrixAction g) (matrixAction_unitary g)

theorem standardMatrixAction_det (g : M22TripleCover) :
    Matrix.GeneralLinearGroup.det (standardMatrixAction g) = 1 := by
  exact Abelianization.commutator_subset_ker
    (Matrix.GeneralLinearGroup.det.comp standardMatrixAction) Group.IsPerfect.mem_commutator

/-- The faithful realization in the literal special unitary subgroup. -/
def unitaryAction : M22TripleCover →* U6Two.form.specialSubgroup :=
  standardMatrixAction.codRestrict _ (fun g =>
    ⟨standardMatrixAction_unitary g, standardMatrixAction_det g⟩)

theorem unitaryAction_faithful : Function.Injective unitaryAction := by
  intro g h he
  exact standardMatrixAction_faithful (congrArg Subtype.val he)

/-- The literal column actions intertwine on every original binary vector. -/
theorem unitaryAction_intertwines (g : M22TripleCover) (v : BinarySpace) :
    ((unitaryAction g).val : Matrix (Fin 6) (Fin 6) U6Two.Field) *ᵥ
      standardCoordinates v = standardCoordinates (binaryRepresentation g v) :=
  standardMatrixAction_intertwines g v

/-- The transported form is exactly the identity Hermitian form of the target model. -/
theorem standardCoordinates_form (v w : BinarySpace) :
    fieldEquiv (hermitianForm v w) =
      standardCoordinates v ⬝ᵥ
        (fun i => U6Two.conjugation (standardCoordinates w i)) := by
  simp only [hermitianForm_apply, dotProduct, map_sum, map_mul,
    standardCoordinates_apply, fieldFrobenius_apply, U6Two.conjugation_apply, map_pow]

end Sporadic.Mathieu.M22TripleCover.Unitary
