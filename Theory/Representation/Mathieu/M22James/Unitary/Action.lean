module
public import Theory.Representation.Mathieu.M22James.Unitary.Coordinates
public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinary

/-!
# The actual triple Mathieu action preserves the field form

Conjugating the given central-field representation by the checked coordinates
produces matrices on F₄⁶. Their values on the two native generators are the
certified unitary matrices. The native generating-closure theorem therefore
places the entire genuine cover in the unitary subgroup. Its perfectness
kills the determinant character. Faithfulness is inherited from the original
binary column action, with an explicit intertwining identity.

Source: Aschbacher–Smith H.12.1(2), printed pp.393–394. The generator data and
ATLAS attribution are retained in `Data` and the native imports.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Unitary
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Matrix Representation.SL2FourNatural
open Uniqueness.PointRestriction (fieldModule fieldRepresentation)
open BenderSuzuki.MatrixGroups
open scoped Matrix

local instance : Module F BinarySpace :=
  fieldModule binaryRepresentation binaryRepresentation_faithful

def fieldAction : Representation F M22TripleCover Vector :=
  (coordinates.conjAlgEquiv F).toMonoidHom.comp
    (fieldRepresentation binaryRepresentation binaryRepresentation_faithful)

def matrixAction : M22TripleCover →* GL (Fin 6) F :=
  Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp fieldAction.asGroupHom

theorem matrixAction_intertwines (g : M22TripleCover) (v : BinarySpace) :
    (matrixAction g : Matrix (Fin 6) (Fin 6) F) *ᵥ coordinates v =
      coordinates (binaryRepresentation g v) := by
  change LinearMap.toMatrix' (fieldAction g) *ᵥ coordinates v = _
  rw [LinearMap.toMatrix'_mulVec]
  change coordinates (binaryRepresentation g (coordinates.symm (coordinates v))) = _
  rw [coordinates.symm_apply_apply]

theorem matrixAction_faithful : Function.Injective matrixAction := by
  intro g h he
  apply binaryRepresentation_faithful
  apply LinearMap.ext
  intro v
  apply coordinates.injective
  rw [← matrixAction_intertwines, ← matrixAction_intertwines, he]

theorem matrixAction_generatorA :
    (matrixAction coreGeneratorA : Matrix (Fin 6) (Fin 6) F) = generatorA := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨w, rfl⟩ := coordinates.surjective v
  rw [matrixAction_intertwines, coordinates_generatorA]

theorem matrixAction_generatorB :
    (matrixAction coreGeneratorB : Matrix (Fin 6) (Fin 6) F) = generatorB := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨w, rfl⟩ := coordinates.surjective v
  rw [matrixAction_intertwines, coordinates_generatorB]

def fieldForm : HermitianForm 6 F where
  conj := fieldFrobenius
  conj_involutive := fieldFrobenius_involutive
  form := 1
  form_hermitian := by intro i j; by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

theorem mem_fieldForm_unitary (A : GL (Fin 6) F) :
    A ∈ fieldForm.unitarySubgroup ↔
      (A : Matrix (Fin 6) (Fin 6) F).transpose.map fieldFrobenius *
        (A : Matrix (Fin 6) (Fin 6) F) = 1 := by
  change fieldForm.conjTranspose _ * 1 * _ = 1 ↔ _
  rw [mul_one]
  rfl

theorem matrixAction_unitary (g : M22TripleCover) :
    (matrixAction g : Matrix (Fin 6) (Fin 6) F).transpose.map fieldFrobenius *
      (matrixAction g : Matrix (Fin 6) (Fin 6) F) = 1 := by
  have ht : (⊤ : Subgroup M22TripleCover) ≤ fieldForm.unitarySubgroup.comap matrixAction := by
    rw [← coreGenerators_closure_eq_top]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    change matrixAction x ∈ fieldForm.unitarySubgroup
    rw [mem_fieldForm_unitary]
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · rw [matrixAction_generatorA]
      exact generatorA_unitary
    · have hx' : x = coreGeneratorB := Set.mem_singleton_iff.mp hx
      subst x
      rw [matrixAction_generatorB]
      exact generatorB_unitary
  exact (mem_fieldForm_unitary _).mp (ht (Subgroup.mem_top g))

theorem matrixAction_det (g : M22TripleCover) :
    Matrix.GeneralLinearGroup.det (matrixAction g) = 1 := by
  exact Abelianization.commutator_subset_ker
    (Matrix.GeneralLinearGroup.det.comp matrixAction) (Group.IsPerfect.mem_commutator)

end Sporadic.Mathieu.M22TripleCover.Unitary
