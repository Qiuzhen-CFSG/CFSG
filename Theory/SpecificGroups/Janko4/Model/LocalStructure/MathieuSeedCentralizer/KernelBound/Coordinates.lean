module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.Coordinates.Calibration
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Data.Matrix.Block

/-!
# Adapted coordinates and the concrete 56-dimensional algebra span

Conjugation by the certified basis sends the literal seed to `[[I,I],[0,I]]`.
Commuting with that matrix forces the form `[[G,H],[0,G]]`; consequently the
upper-left block is multiplicative on the centralizer. The displayed algebra
span is defined independently of centralizer membership and of any bound.
No completeness assertion about its units is made here.

Source: the literal ATLAS word and finite witness data described in
`Coordinates.Data`. The sibling intrinsic-algebra construction can calibrate
against `algebraBasis` without importing any kernel classification.
-/

@[expose] public section

open Matrix
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.Coordinates
open GeneratorCertificates Cardinality.KernelCount
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

abbrev HalfMatrix := Matrix (Fin 56) (Fin 56) (ZMod 2)
abbrev BlockMatrix := Matrix (Fin 56 ⊕ Fin 56) (Fin 56 ⊕ Fin 56) (ZMod 2)

def adaptedBasis : BinaryMatrix := decodeRows adaptedRows
def adaptedBasisInverse : BinaryMatrix := decodeRows adaptedInverseRows

def conjugateMatrix (g : BinaryMatrix) : BinaryMatrix :=
  adaptedBasisInverse * g * adaptedBasis

theorem conjugateMatrix_mul (g h : BinaryMatrix) :
    conjugateMatrix (g * h) = conjugateMatrix g * conjugateMatrix h := by
  dsimp [conjugateMatrix, adaptedBasis, adaptedBasisInverse]
  rw [show decodeRows adaptedInverseRows * g * decodeRows adaptedRows *
      (decodeRows adaptedInverseRows * h * decodeRows adaptedRows) =
      decodeRows adaptedInverseRows * g *
      (decodeRows adaptedRows * decodeRows adaptedInverseRows) * h * decodeRows adaptedRows
      by simp only [mul_assoc]]
  rw [adapted_mul_inverse, mul_one]
  simp only [mul_assoc]

theorem conjugateMatrix_one : conjugateMatrix 1 = 1 := by
  simpa only [conjugateMatrix, adaptedBasis, adaptedBasisInverse, mul_one] using adapted_inverse_mul

theorem recover_conjugateMatrix (g : BinaryMatrix) :
    adaptedBasis * conjugateMatrix g * adaptedBasisInverse = g := by
  calc
    _ = (adaptedBasis * adaptedBasisInverse) * g *
        (adaptedBasis * adaptedBasisInverse) := by simp only [conjugateMatrix, mul_assoc]
    _ = g := by simp only [adaptedBasis, adaptedBasisInverse, adapted_mul_inverse, one_mul, mul_one]

theorem conjugateMatrix_injective : Function.Injective conjugateMatrix := by
  intro g h he
  simpa only [recover_conjugateMatrix] using
    congrArg (fun q => adaptedBasis * q * adaptedBasisInverse) he

def blockReindex : BinaryMatrix ≃+* BlockMatrix :=
  Matrix.reindexRingEquiv (ZMod 2) (finSumFinEquiv : Fin 56 ⊕ Fin 56 ≃ Fin 112).symm

def blockCoordinates (g : BinaryMatrix) : BlockMatrix := blockReindex (conjugateMatrix g)

theorem blockCoordinates_mul (g h : BinaryMatrix) :
    blockCoordinates (g * h) = blockCoordinates g * blockCoordinates h := by
  simp only [blockCoordinates, conjugateMatrix_mul, map_mul]

theorem blockCoordinates_one : blockCoordinates 1 = 1 := by
  simp only [blockCoordinates, conjugateMatrix_one, map_one]

theorem blockCoordinates_injective : Function.Injective blockCoordinates :=
  blockReindex.injective.comp conjugateMatrix_injective

def restrictionBlock (g : BinaryMatrix) : HalfMatrix := (blockCoordinates g).toBlocks₁₁

def shearBlock (g : BinaryMatrix) : HalfMatrix := (blockCoordinates g).toBlocks₁₂

def decodeHalf (word : ℕ) : HalfMatrix := fun i j => bit word (56 * i.val + j.val)

def algebraBasis (i : Fin 56) : HalfMatrix := decodeHalf (algebraBasisWords.get i)

def concreteAlgebra : Submodule (ZMod 2) HalfMatrix :=
  Submodule.span (ZMod 2) (Set.range algebraBasis)

def wallPairing : HalfMatrix := fun i j => bit (wallPairingRows.get i) j.val

theorem wallPairing_transpose : wallPairingᵀ = wallPairing := by
  decide +kernel

theorem adaptedForm_blocks :
    blockReindex (decodeRows adaptedFormRows) =
      Matrix.fromBlocks (0 : HalfMatrix) wallPairing wallPairingᵀ
        ((blockReindex (decodeRows adaptedFormRows)).toBlocks₂₂) := by
  decide +kernel

theorem adaptedSeed_blocks :
    blockReindex (decodeRows adaptedSeedRows) =
      Matrix.fromBlocks (1 : HalfMatrix) 1 0 1 := by
  decide +kernel

theorem blockCoordinates_seed :
    blockCoordinates (decodeRows e0Rows) = Matrix.fromBlocks (1 : HalfMatrix) 1 0 1 := by
  have h : conjugateMatrix (decodeRows e0Rows) = decodeRows adaptedSeedRows := by
    dsimp [conjugateMatrix, adaptedBasis, adaptedBasisInverse]
    rw [mul_assoc, seed_mul_adapted, ← mul_assoc, adapted_inverse_mul, one_mul]
  rw [blockCoordinates, h, adaptedSeed_blocks]

theorem centralizing_block_shape (g : BinaryMatrix)
    (hc : g * decodeRows e0Rows = decodeRows e0Rows * g) :
    blockCoordinates g = Matrix.fromBlocks (restrictionBlock g) (shearBlock g) 0
      (restrictionBlock g) := by
  have he := congrArg blockCoordinates hc
  rw [blockCoordinates_mul, blockCoordinates_mul, blockCoordinates_seed] at he
  let q := blockCoordinates g
  have hq : q = Matrix.fromBlocks q.toBlocks₁₁ q.toBlocks₁₂ q.toBlocks₂₁ q.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks q).symm
  change q * _ = _ * q at he
  rw [hq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at he
  simp only [mul_one, mul_zero, add_zero, zero_mul, zero_add, one_mul,
    Matrix.fromBlocks_inj] at he
  have h21 : q.toBlocks₂₁ = 0 := by
    have h := he.1
    exact add_left_cancel (show q.toBlocks₁₁ + q.toBlocks₂₁ = q.toBlocks₁₁ + 0 by simpa using h.symm)
  have h22 : q.toBlocks₂₂ = q.toBlocks₁₁ := by
    have h := he.2.1
    rw [add_comm q.toBlocks₁₂ q.toBlocks₂₂] at h
    exact (add_right_cancel h).symm
  change q = Matrix.fromBlocks q.toBlocks₁₁ q.toBlocks₁₂ 0 q.toBlocks₁₁
  conv_lhs => rw [hq]
  rw [h21, h22]

theorem restrictionBlock_one : restrictionBlock 1 = 1 := by
  rw [restrictionBlock, blockCoordinates_one, ← Matrix.fromBlocks_one]
  rfl

theorem restrictionBlock_mul (g h : BinaryMatrix)
    (hg : g * decodeRows e0Rows = decodeRows e0Rows * g)
    (hh : h * decodeRows e0Rows = decodeRows e0Rows * h) :
    restrictionBlock (g * h) = restrictionBlock g * restrictionBlock h := by
  change (blockCoordinates (g * h)).toBlocks₁₁ = _
  rw [blockCoordinates_mul, centralizing_block_shape g hg, centralizing_block_shape h hh,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, mul_zero, add_zero]

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.Coordinates
