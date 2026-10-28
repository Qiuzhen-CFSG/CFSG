module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.Reduction
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Nonzero intertwiners for the concrete J₄ matrices

The two equations defining an intertwiner are linear in its matrix entries.
Its kernel is invariant under the two original generators. Consequently, if
their binary module is irreducible, every nonzero solution is invertible.
For an automorphism fixing `a`, the resulting unit centralizes `matrixUnitA`
and conjugates `matrixUnitB` to the required image.

This is a conditional linear-algebra reduction. Neither irreducibility of the
literal matrices nor existence of nonzero twisted intertwiners is asserted
here. These are separate obligations; the orders of the generators do not
establish either one. The representation is ATLAS `J4G1-f2r112B0`, whose
literal data and source attribution are in `Janko4.Model.Data`. The motivating
outer-automorphism statement is GLS3, Table 5.3i.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator

/-- Column vectors for the literal binary representation. -/
abbrev BinaryVector := Fin 112 → ZMod 2

/-- Irreducibility stated directly at the two generating matrices. Since the
generators act invertibly, stability under them is the usual module condition. -/
def GeneratorIrreducible : Prop :=
  ∀ W : Submodule (ZMod 2) BinaryVector,
    (∀ v ∈ W, matrixA.mulVec v ∈ W) →
    (∀ v ∈ W, matrixB.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

/-- The space of matrix maps from the original representation to its twist by
`α`, specified on the two certified generators. No invertibility is assumed. -/
def generatorIntertwiners (α : MulAut Model) : Submodule (ZMod 2) BinaryMatrix where
  carrier := {U | U * matrixA = toMatrix (α a) * U ∧
    U * matrixB = toMatrix (α b) * U}
  zero_mem' := by simp
  add_mem' := by
    intro U V hU hV
    constructor
    · simp only [Matrix.add_mul, Matrix.mul_add, hU.1, hV.1]
    · simp only [Matrix.add_mul, Matrix.mul_add, hU.2, hV.2]
  smul_mem' := by
    intro c U hU
    constructor
    · simp only [Matrix.smul_mul, Matrix.mul_smul, hU.1]
    · simp only [Matrix.smul_mul, Matrix.mul_smul, hU.2]

@[simp] theorem mem_generatorIntertwiners (α : MulAut Model) (U : BinaryMatrix) :
    U ∈ generatorIntertwiners α ↔
      U * matrixA = toMatrix (α a) * U ∧
        U * matrixB = toMatrix (α b) * U := Iff.rfl

private theorem intertwiner_ker_stable {U M N : BinaryMatrix}
    (h : U * M = N * U) (v : BinaryVector) (hv : v ∈ LinearMap.ker U.mulVecLin) :
    M.mulVec v ∈ LinearMap.ker U.mulVecLin := by
  change U.mulVec v = 0 at hv
  change U.mulVec (M.mulVec v) = 0
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-- Schur's kernel argument needs only irreducibility of the source module.
The square matrix is then a unit by finite-dimensional linear algebra. -/
theorem isUnit_of_nonzero_generatorIntertwiner (hirr : GeneratorIrreducible)
    (α : MulAut Model) {U : BinaryMatrix}
    (hU : U ∈ generatorIntertwiners α) (hne : U ≠ 0) : IsUnit U := by
  obtain hbot | htop := hirr (LinearMap.ker U.mulVecLin)
    (intertwiner_ker_stable hU.1) (intertwiner_ker_stable hU.2)
  · apply Matrix.mulVec_injective_iff_isUnit.mp
    rw [← Matrix.coe_mulVecLin]
    exact LinearMap.ker_eq_bot.mp hbot
  · exfalso
    apply hne
    apply Matrix.toLin'.injective
    exact (LinearMap.ker_eq_top.mp htop).trans Matrix.mulVecLin_zero.symm

/-- Turn an invertible solution of the two linear equations into the exact
ambient unit required by the fixed-generator reduction. -/
theorem ambient_unit_of_isUnit_generatorIntertwiner
    (α : MulAut Model) (ha : α a = a) {U : BinaryMatrix}
    (hU : U ∈ generatorIntertwiners α) (hunit : IsUnit U) :
    ∃ u : BinaryMatrixˣ, u * matrixUnitA = matrixUnitA * u ∧
      toAmbient (α b) = u * matrixUnitB * u⁻¹ := by
  obtain ⟨u, rfl⟩ := hunit
  have hua : u * matrixUnitA = matrixUnitA * u := by
    apply Units.val_injective
    simpa only [Units.val_mul, coe_matrixUnitA, ha, toMatrix_a] using hU.1
  have hub : u * matrixUnitB = toAmbient (α b) * u := by
    apply Units.val_injective
    exact hU.2
  refine ⟨u, hua, ?_⟩
  rw [hub, mul_inv_cancel_right]

/-- Nonzero twisted intertwiners suffice once the actual binary module is
proved irreducible. This theorem discharges the invertibility requirement. -/
theorem ambient_unit_of_nonzero_generatorIntertwiner
    (hirr : GeneratorIrreducible) (α : MulAut Model) (ha : α a = a)
    {U : BinaryMatrix} (hU : U ∈ generatorIntertwiners α) (hne : U ≠ 0) :
    ∃ u : BinaryMatrixˣ, u * matrixUnitA = matrixUnitA * u ∧
      toAmbient (α b) = u * matrixUnitB * u⁻¹ :=
  ambient_unit_of_isUnit_generatorIntertwiner α ha hU
    (isUnit_of_nonzero_generatorIntertwiner hirr α hU hne)

end Janko4.OuterReduction.FixedGenerator
