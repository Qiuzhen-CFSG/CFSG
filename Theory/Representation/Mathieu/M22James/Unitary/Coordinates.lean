module
public import Theory.Representation.Mathieu.M22James.Unitary.Certificates
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.CentralField

/-!
# Compatible field coordinates on the genuine triple Mathieu module

The checked decoder proves injectivity of the binary coordinate map. Equal
finite cardinalities give an equivalence. The central-scalar certificate
then upgrades this very equivalence to linearity over the specified
`PointRestriction.fieldModule`, without changing the underlying vectors or
the scalar marking. The two generator identities retain the literal native
action and are consumed by `Action` to prove invariance for the full group.

Source: Aschbacher–Smith H.12.1(2), printed pp.393–394; see `Data` for the
native ATLAS attribution and coordinate convention.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Unitary
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Matrix Representation.SL2FourNatural
open Uniqueness.PointRestriction (fieldModule field_smul_formula)
open scoped Matrix

def binaryLift : BinarySpace →ₗ[ZMod 2] (Fin 12 → F) where
  toFun v i := algebraMap (ZMod 2) F (v i)
  map_add' v w := by funext i; exact map_add _ _ _
  map_smul' c v := by
    funext i
    change algebraMap (ZMod 2) F (c * v i) = c • algebraMap (ZMod 2) F (v i)
    simp [Algebra.smul_def]

def coordinateMap : BinarySpace →ₗ[ZMod 2] Vector :=
  (coordMatrix.mulVecLin.restrictScalars (ZMod 2)).comp binaryLift

theorem coordinateMap_apply (v : BinarySpace) :
    coordinateMap v = coordMatrix *ᵥ binaryLift v := rfl

theorem decode_coordinate (v : BinarySpace) (i : Fin 12) :
    ((decodeMatrix *ᵥ coordinateMap v) i).re = v i := by
  rw [coordinateMap_apply, mulVec_mulVec]
  have hr : (((decodeMatrix * coordMatrix) *ᵥ binaryLift v) i).re =
      (((decodeMatrix * coordMatrix).map QuadraticAlgebra.re) *ᵥ v) i := by
    change (QuadraticAlgebra.reₗ 1 1) (∑ j : Fin 12, (decodeMatrix * coordMatrix) i j *
      algebraMap (ZMod 2) F (v j)) = _
    simp [map_sum, mulVec, dotProduct]
  rw [hr, decode_coord, one_mulVec]

theorem coordinateMap_injective : Function.Injective coordinateMap := by
  intro v w h
  ext i
  rw [← decode_coordinate v i, ← decode_coordinate w i, h]

theorem coordinateMap_bijective : Function.Bijective coordinateMap := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨coordinateMap_injective, ?_⟩
  simp [BinarySpace, Vector, card_field]

noncomputable def binaryCoordinates : BinarySpace ≃ₗ[ZMod 2] Vector :=
  LinearEquiv.ofBijective coordinateMap coordinateMap_bijective

theorem coordinateMap_matrix (M : Matrix12) (v : BinarySpace) :
    coordinateMap (M *ᵥ v) =
      (coordMatrix * M.map (algebraMap (ZMod 2) F)) *ᵥ binaryLift v := by
  rw [coordinateMap_apply, ← mulVec_mulVec]
  congr 1
  funext i
  exact (RingHom.map_mulVec (algebraMap (ZMod 2) F) M v i)

theorem coordinateMap_scalar (v : BinarySpace) :
    coordinateMap (binaryRepresentation scalar v) =
      (QuadraticAlgebra.omega : F) • coordinateMap v := by
  rw [binaryRepresentation_apply]
  change coordinateMap ((scalarUnit : Matrix12) *ᵥ v) = _
  rw [coe_scalarUnit, coordinateMap_matrix, coord_scalar, smul_mulVec]
  rfl

local instance : Module F BinarySpace :=
  fieldModule binaryRepresentation binaryRepresentation_faithful

theorem coordinateMap_smul (a : F) (v : BinarySpace) :
    coordinateMap (a • v) = a • coordinateMap v := by
  rw [field_smul_formula, map_add, map_smul, map_smul, coordinateMap_scalar]
  funext i
  change a.re • coordinateMap v i + a.im •
    ((QuadraticAlgebra.omega : F) * coordinateMap v i) = a * coordinateMap v i
  rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← add_mul]
  congr 1
  ext <;> simp

noncomputable def coordinates : BinarySpace ≃ₗ[F] Vector :=
  { binaryCoordinates with map_smul' := coordinateMap_smul }

theorem coordinates_generatorA (v : BinarySpace) :
    coordinates (binaryRepresentation coreGeneratorA v) = generatorA *ᵥ coordinates v := by
  change coordinateMap ((coreA : Matrix12) *ᵥ v) = generatorA *ᵥ coordinateMap v
  rw [coe_coreA, coordinateMap_matrix, coord_generatorA, ← mulVec_mulVec]
  rfl

theorem coordinates_generatorB (v : BinarySpace) :
    coordinates (binaryRepresentation coreGeneratorB v) = generatorB *ᵥ coordinates v := by
  change coordinateMap ((coreB : Matrix12) *ᵥ v) = generatorB *ᵥ coordinateMap v
  rw [coe_coreB, coordinateMap_matrix, coord_generatorB, ← mulVec_mulVec]
  rfl

end Sporadic.Mathieu.M22TripleCover.Unitary
