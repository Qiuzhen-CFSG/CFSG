module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native
public import Theory.PGroupCore

/-!
# A native totally singular three-space over F₄

An explicit six-by-three coordinate matrix embeds F₄³ in the actual James
module. A left inverse proves its rank, and its zero Hermitian Gram matrix
proves total singularity. The marked binary vector 1327 and its whole central
F₄-point lie in this space. Its binary dimension is six, and it lies in the
orthogonal complement of the marked vector for the native quadratic form.

The literal stabilizer, its restricted representation, and the point
centralizer's intrinsic two-core are defined here for the remaining native
calculations. On this restricted representation, inversion of the central
cubic operator implies equality of the fixed and moved spaces and dimension
three. The operator relations are the precise hypotheses; no relation on an
extraspecial-group lift is imposed.

This supplies coordinates for Aschbacher–Smith 14.4.12, printed pp.1011–1012,
with the form from H.12.1(2). Identifying this stabilizer with the source D,
proving that its marked orbit spans the space, and locating the inverting
operator in the actual two-core remain separate group/module calculations.
See `source/README.md` for reproducible diagnostic data and conventions.
-/

@[expose] public section

noncomputable section
open Matrix Representation.SL2FourNatural
open Sporadic.Mathieu M22TripleCover M22TripleCover.Unitary
open M22TripleCover.Uniqueness.PointRestriction (fieldModule fieldTower)
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation.BinaryOffender
open scoped Matrix

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native

local instance : Module F BinarySpace :=
  fieldModule binaryRepresentation binaryRepresentation_faithful
local instance : IsScalarTower (ZMod 2) F BinarySpace :=
  fieldTower binaryRepresentation binaryRepresentation_faithful

def parabolicMatrix : Matrix (Fin 6) (Fin 3) F :=
  (!![2,2,0; 3,2,0; 2,0,1; 0,0,2; 3,1,2; 0,1,2] : Matrix _ _ ℕ).map fieldEntry

def parabolicDecoder : Matrix (Fin 3) (Fin 6) F :=
  (!![1,1,0,0,0,0; 2,1,0,0,0,0; 2,2,1,0,0,0] : Matrix _ _ ℕ).map fieldEntry

theorem parabolic_decode : parabolicDecoder * parabolicMatrix = 1 := by decide +kernel

theorem parabolic_gram_zero :
    parabolicMatrix.transpose * parabolicMatrix.map fieldFrobenius = 0 := by decide +kernel

def parabolicEmbedding : (Fin 3 → F) →ₗ[F] BinarySpace :=
  coordinates.symm.toLinearMap.comp parabolicMatrix.mulVecLin

theorem coordinates_parabolicEmbedding (u : Fin 3 → F) :
    coordinates (parabolicEmbedding u) = parabolicMatrix *ᵥ u :=
  coordinates.apply_symm_apply _

theorem parabolicEmbedding_injective : Function.Injective parabolicEmbedding := by
  intro u v h
  have hh := congrArg (fun w => parabolicDecoder *ᵥ coordinates w) h
  simpa only [coordinates_parabolicEmbedding, mulVec_mulVec,
    parabolic_decode, one_mulVec] using hh

def parabolicFieldSpace : Submodule F BinarySpace := parabolicEmbedding.range

def parabolicSpace : Submodule (ZMod 2) BinarySpace :=
  parabolicFieldSpace.restrictScalars (ZMod 2)

def markedVector : BinarySpace := fun i => if (1327 : ℕ).testBit i.val then 1 else 0

theorem markedVector_ne_zero : markedVector ≠ 0 := by decide +kernel

theorem markedVector_coordinates :
    coordinateMap markedVector = parabolicMatrix *ᵥ ![fieldEntry 3, 1, fieldEntry 2] := by
  decide +kernel

theorem markedVector_mem_parabolic : markedVector ∈ parabolicFieldSpace := by
  refine ⟨![fieldEntry 3, 1, fieldEntry 2], ?_⟩
  apply coordinates.injective
  exact (coordinates_parabolicEmbedding _).trans markedVector_coordinates.symm

theorem markedPoint_le_parabolic : binaryPoint markedVector ≤ parabolicSpace := by
  change (fieldPoint markedVector).restrictScalars (ZMod 2) ≤
    parabolicFieldSpace.restrictScalars (ZMod 2)
  have h : fieldPoint markedVector ≤ parabolicFieldSpace := by
    apply Submodule.span_le.mpr
    intro v hv
    rw [Set.mem_singleton_iff.mp hv]
    exact markedVector_mem_parabolic
  exact h

theorem parabolicFieldSpace_finrank : Module.finrank F parabolicFieldSpace = 3 := by
  rw [parabolicFieldSpace, LinearMap.finrank_range_of_inj parabolicEmbedding_injective]
  simp

theorem parabolicSpace_finrank : Module.finrank (ZMod 2) parabolicSpace = 6 := by
  have h := Module.finrank_mul_finrank (ZMod 2) F parabolicFieldSpace
  rw [QuadraticAlgebra.finrank_eq_two, parabolicFieldSpace_finrank] at h
  exact h.symm

theorem parabolic_hermitian_zero (u v : Fin 3 → F) :
    hermitianForm (parabolicEmbedding u) (parabolicEmbedding v) = 0 := by
  rw [hermitianForm_apply, coordinates_parabolicEmbedding, coordinates_parabolicEmbedding]
  have hbar : (fun i => fieldFrobenius ((parabolicMatrix *ᵥ v) i)) =
      parabolicMatrix.map fieldFrobenius *ᵥ (fun i => fieldFrobenius (v i)) := by
    funext i
    exact RingHom.map_mulVec fieldFrobenius.toRingHom parabolicMatrix v i
  rw [hbar, dotProduct_comm, ← dotProduct_transpose_mulVec,
    mulVec_mulVec, parabolic_gram_zero, zero_mulVec, dotProduct_zero]

theorem parabolicSpace_totally_singular :
    ∀ v ∈ parabolicSpace, quadraticForm v = 0 := by
  rintro v ⟨u, rfl⟩
  rw [quadraticForm_apply, parabolic_hermitian_zero]
  rfl

def markedPerp : Submodule (ZMod 2) BinarySpace :=
  (quadraticForm.polarBilin markedVector).ker

theorem parabolicSpace_le_markedPerp : parabolicSpace ≤ markedPerp := by
  intro v hv
  have hm : markedVector ∈ parabolicSpace := markedVector_mem_parabolic
  change quadraticForm (markedVector + v) - quadraticForm markedVector - quadraticForm v = 0
  rw [parabolicSpace_totally_singular _ (parabolicSpace.add_mem hm hv),
    parabolicSpace_totally_singular _ hm, parabolicSpace_totally_singular _ hv]
  simp

def parabolic : Subgroup Group := subspaceStabilizer representation parabolicSpace

def parabolicRepresentation : Representation (ZMod 2) parabolic parabolicSpace :=
  stabilizerRepresentation representation parabolicSpace

theorem centralScalar_mem_parabolic : centralScalar ∈ parabolic := by
  have hstab : Subgroup.zpowers centralScalar ≤ parabolic := by
    apply le_subspaceStabilizer
    intro a ha v hv
    have hf : IsOfFinOrder centralScalar :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, centralScalar_cube⟩
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp
      (hf.mem_zpowers_iff_mem_range_orderOf.mp ha)
    rw [centralScalar_pow_smul]
    exact parabolicFieldSpace.smul_mem _ hv
  exact hstab (Subgroup.mem_zpowers centralScalar)

def parabolicScalar : parabolic := ⟨centralScalar, centralScalar_mem_parabolic⟩

theorem parabolicScalar_cube : parabolicScalar ^ 3 = 1 :=
  Subtype.ext centralScalar_cube

theorem parabolicScalar_fixed_iff (v : parabolicSpace) :
    parabolicRepresentation parabolicScalar v = v ↔ v = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    exact (centralScalar_fixed_iff v).mp (congrArg Subtype.val h)
  · rintro rfl
    exact map_zero _

theorem parabolic_inverter_fixed_moved (x : parabolic)
    (hx : parabolicRepresentation x * parabolicRepresentation x = 1)
    (hxc : parabolicRepresentation x * parabolicRepresentation parabolicScalar =
      parabolicRepresentation parabolicScalar ^ 2 * parabolicRepresentation x) :
    LinearMap.range (parabolicRepresentation x - 1) =
        LinearMap.ker (parabolicRepresentation x - 1) ∧
      Module.finrank (ZMod 2) (LinearMap.range (parabolicRepresentation x - 1)) = 3 := by
  have hc : parabolicRepresentation parabolicScalar ^ 3 = 1 := by
    rw [← map_pow, parabolicScalar_cube, map_one]
  have hf : ∀ v, parabolicRepresentation parabolicScalar v = v → v = 0 :=
    fun v => (parabolicScalar_fixed_iff v).mp
  refine ⟨Representation.RankTwo.range_eq_ker_of_inverts_cubic _ _
    (Representation.RankTwo.quadratic_of_cubic_fixed_free _ hc hf) hx hxc, ?_⟩
  have h := Representation.RankTwo.finrank_range_inverting_cubic _ _ hc hf hx hxc
  rw [parabolicSpace_finrank] at h
  omega

def pointCentralizer : Subgroup Group :=
  subspaceKernel representation (binaryLine markedVector) ⊤

def pointRadical : Subgroup Group :=
  (pCore 2 pointCentralizer).map pointCentralizer.subtype

theorem marked_moved_point_le_parabolic :
    subspaceCommutator representation (binaryLine markedVector)
      (Subgroup.zpowers centralScalar) ≤ parabolicSpace := by
  rw [scalar_moved_line_eq_point]
  exact markedPoint_le_parabolic

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native
