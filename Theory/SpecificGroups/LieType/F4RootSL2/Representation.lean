module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.LinearLeviGeneration.LongRootMatrices.Coordinates
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup

/-!
# The long-root SL₂ action on the full F₄ adjoint lattice

The four Cartan coordinates and the two roots ±α₀ form a six-dimensional
block. The symmetric-square action on α₀, its coroot and −α₀ extends across
the remaining Cartan coordinates using the coefficients |a₀ⱼ| = (2,1,0,0).
Fourteen natural modules and eighteen fixed lines complete the 52-dimensional
action. A natural block proves faithfulness. This restores the coefficient
2 suppressed in the characteristic-two construction in
`ReeF4/.../LongRootMatrices/Representation.lean`, reusing its certified basis
permutation without changing that module or assuming a subsystem identification.

Source: GLS3 §§1.12 and 2.6, the integral common-lattice subsystem
construction (`refs/KGroup/GLS3/chapter2.tex`). This is the long-root map used
in Aschbacher–Smith A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

@[expose] public section
open Matrix
open ReeF4.Cartan.FieldSeparation.TraceValues
open scoped MatrixGroups
namespace ExceptionalSplit.F4RootSL2
abbrev SpecialIndex := ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.LongRootMatrices.SpecialIndex
abbrev BlockIndex := ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.LongRootMatrices.BlockIndex
noncomputable abbrev latticeEquiv := ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.LongRootMatrices.latticeEquiv

def cartanCoefficient (j : Fin 4) : ℤ := ![2, 1, 0, 0] j

def specialBlock {F : Type*} [CommRing F]
    (A : Matrix (Fin 2) (Fin 2) F) : Matrix SpecialIndex SpecialIndex F
  | .inl k, .inl j => (if k = j then 1 else 0) +
      if k = 0 then (cartanCoefficient j : F) * A 0 1 * A 1 0 else 0
  | .inl k, .inr s => if k = 0 then A 0 s * A 1 s else 0
  | .inr r, .inl j => (cartanCoefficient j : F) * A r 0 * A r 1
  | .inr r, .inr s => A r s ^ 2

variable {F : Type*} [CommRing F]

set_option maxHeartbeats 2000000 in
lemma specialBlock_one : specialBlock (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext (k | k) (j | j) <;> simp [specialBlock, Matrix.one_apply]
  all_goals aesop

set_option maxHeartbeats 1000000 in
lemma specialBlock_mul (A B : SL(2, F)) :
    specialBlock ((A * B).1) = specialBlock A.1 * specialBlock B.1 := by
  have hA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.det_coe
  have hB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using B.det_coe
  ext (k | k) (j | j)
  all_goals
    fin_cases k <;> fin_cases j <;>
      simp [specialBlock, cartanCoefficient, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_succ] <;>
      first | ring1 | grind only

/-- The six-dimensional block, fourteen natural modules, and eighteen fixed lines. -/
def blockMatrix (A : SL(2, F)) : Matrix BlockIndex BlockIndex F :=
  Matrix.fromBlocks (specialBlock A.1) 0 0
    (Matrix.fromBlocks (Matrix.blockDiagonal fun _ : Fin 14 => A.1) 0 0 1)

lemma blockMatrix_one : blockMatrix (1 : SL(2, F)) = 1 := by
  have h : Matrix.blockDiagonal (fun _ : Fin 14 => (1 : Matrix (Fin 2) (Fin 2) F)) = 1 :=
    Matrix.blockDiagonal_one
  simp only [blockMatrix, SpecialLinearGroup.coe_one, specialBlock_one, h,
    Matrix.fromBlocks_one]

lemma blockMatrix_mul (A B : SL(2, F)) :
    blockMatrix (A * B) = blockMatrix A * blockMatrix B := by
  unfold blockMatrix
  rw [specialBlock_mul]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, mul_one, SpecialLinearGroup.coe_mul,
    ← Matrix.blockDiagonal_mul]

/-- Faithfulness is visible on the first natural root-string block. -/
lemma blockMatrix_injective : Function.Injective (blockMatrix (F := F)) := by
  intro A B h
  apply Subtype.ext
  ext r s
  have hentry := congrArg
    (fun M : Matrix BlockIndex BlockIndex F => M (.inr (.inl (r, 0)))
      (.inr (.inl (s, 0)))) h
  simpa [blockMatrix, Matrix.blockDiagonal] using hentry

/-- A matrix monoid representation before restricting its range to the Geck group. -/
def blockHom : SL(2, F) →* Matrix BlockIndex BlockIndex F where
  toFun := blockMatrix
  map_one' := blockMatrix_one
  map_mul' := blockMatrix_mul

noncomputable section
local instance : DecidableEq Basis := fun a b => instDecidableEqSum a b

/-- The explicit faithful rank-one action on the actual Cartan-plus-root lattice. -/
def ambientHom : SL(2, F) →* (Matrix Basis Basis F)ˣ :=
  ((Matrix.reindexAlgEquiv F F latticeEquiv).toMonoidHom.comp blockHom).toHomUnits

lemma ambientHom_injective : Function.Injective (ambientHom (F := F)) := by
  intro A B h
  apply blockMatrix_injective
  apply (Matrix.reindexAlgEquiv F F latticeEquiv).injective
  exact congrArg Units.val h

/-- Entrywise form of the action, without inverses of the coordinate equivalence. -/
lemma ambientHom_entry (A : SL(2, F)) (r s : BlockIndex) :
    (ambientHom A).val (latticeEquiv r) (latticeEquiv s) =
      blockMatrix A r s := by
  simp [ambientHom, Matrix.reindexAlgEquiv, Matrix.reindexRingEquiv,
    Matrix.reindex_apply, blockHom]

end
end ExceptionalSplit.F4RootSL2
