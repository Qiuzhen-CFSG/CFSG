module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.WordEvaluation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.CommuteProducts
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.InvariantForm
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorSpace
public import Mathlib.Algebra.CharP.Two

/-!
# Intrinsic spaces for the literal max1 seed

The seed is the actual word `(xy)^14` in `Model`. Its displacement acts on
columns. The space `radicalForms` consists of the forms in the existing
`exteriorFormSpace` whose radical contains the displacement kernel. Neither
this definition nor the square-zero proof assumes a centralizer order or a
description of the vector stabilizer.

The finite-data construction is explained in
`Scratch/J4FleetGuidance/SeedCentralizer/README.md` in the source checkout.
Its motivation is GLS3 Table 5.3i (2B); the matrix identities, rather than
that table, are the proof inputs here.
-/

@[expose] public section
open scoped Matrix

namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra

open Cardinality Cardinality.KernelCount GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

abbrev Column := Fin 112 → ZMod 2

/-- The literal seed, with the already certified ambient generators. -/
def seed : Model := localKernelSeed matrixA_mul_self matrixB_pow_four

/-- The full centralizer in `Model`; definitionally the ambient seed centralizer.
This independent definition avoids importing the order-comparison assembly. -/
def centralizer : Subgroup Model := Subgroup.centralizer ({seed} : Set Model)

/-- Displacement matrix in the original column basis. -/
def displacementMatrix : BinaryMatrix := toMatrix seed - 1

def displacement : Column →ₗ[ZMod 2] Column := displacementMatrix.mulVecLin

def kernelSpace : Submodule (ZMod 2) Column := LinearMap.ker displacement

/-- The source exterior space, without replacing its spanning family. -/
abbrev ambientForms : Submodule (ZMod 2) BinaryMatrix := exteriorFormSpace

/-- Forms in the source exterior space with radical containing `kernelSpace`.
The forms are symmetric, so the right-radical convention is equivalent to
the left-radical convention. -/
def radicalForms : Submodule (ZMod 2) BinaryMatrix where
  carrier := {R | R ∈ ambientForms ∧ ∀ v ∈ kernelSpace, R *ᵥ v = 0}
  zero_mem' := ⟨ambientForms.zero_mem, by simp⟩
  add_mem' := by
    rintro R S ⟨hR, hRv⟩ ⟨hS, hSv⟩
    refine ⟨ambientForms.add_mem hR hS, ?_⟩
    intro v hv
    simp only [Matrix.add_mulVec, hRv v hv, hSv v hv, add_zero]
  smul_mem' := by
    rintro a R ⟨hR, hRv⟩
    refine ⟨ambientForms.smul_mem a hR, ?_⟩
    intro v hv
    simp only [Matrix.smul_mulVec, hRv v hv, smul_zero]

theorem seed_matrix : toMatrix seed = decodeRows e0Rows :=
  Relations.representation_seed matrixA_mul_self matrixB_pow_four

theorem seed_matrix_sq : toMatrix seed * toMatrix seed = 1 := by
  rw [seed_matrix, ← decode_packedMul, Relations.product_square0, decode_packedOne]

theorem seed_sq : seed * seed = 1 := by
  apply toMatrix_injective
  rw [map_mul, seed_matrix_sq, map_one]

private theorem square_displacement (T : BinaryMatrix) (hT : T * T = 1) :
    (T - 1) * (T - 1) = 0 := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, hT]
  ext i j
  simp only [Matrix.sub_apply, Matrix.zero_apply, CharTwo.sub_eq_add]
  rw [add_assoc, ← add_assoc (T i j), CharTwo.add_self_eq_zero,
    zero_add, CharTwo.add_self_eq_zero]

theorem displacementMatrix_sq : displacementMatrix * displacementMatrix = 0 :=
  square_displacement (toMatrix seed) seed_matrix_sq

theorem displacement_sq (v : Column) : displacement (displacement v) = 0 := by
  change displacementMatrix *ᵥ (displacementMatrix *ᵥ v) = 0
  rw [Matrix.mulVec_mulVec, displacementMatrix_sq, Matrix.zero_mulVec]

theorem range_displacement_le_kernel : LinearMap.range displacement ≤ kernelSpace := by
  rintro v ⟨w, rfl⟩
  exact displacement_sq w

theorem mem_kernelSpace (v : Column) : v ∈ kernelSpace ↔ displacementMatrix *ᵥ v = 0 :=
  Iff.rfl

theorem mem_radicalForms (R : BinaryMatrix) :
    R ∈ radicalForms ↔ R ∈ ambientForms ∧ ∀ v ∈ kernelSpace, R *ᵥ v = 0 := Iff.rfl

theorem ambientForms_transpose {R : BinaryMatrix} (hR : R ∈ ambientForms) : Rᵀ = R := by
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨i, rfl⟩ := hR
    exact decodeExteriorForm_transpose _
  | zero => exact Matrix.transpose_zero
  | add R S _ _ hR hS => rw [Matrix.transpose_add, hR, hS]
  | smul a R _ hR => rw [Matrix.transpose_smul, hR]

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
