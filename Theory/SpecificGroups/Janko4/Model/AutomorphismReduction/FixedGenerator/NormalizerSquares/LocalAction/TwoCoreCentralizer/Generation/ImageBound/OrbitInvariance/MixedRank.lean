module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitInvariance.ContractionRank
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Field.ZMod

/-!
# Mixed-coordinate calculation of intrinsic contraction rank

The columns of mixedEmbedding give fixed lifts and hence actual classes in
NaturalHomology. The complete radical certificate identifies their contraction
rows, evaluated on restrictionLifts, with the span of the forty published
mixedGenerator contractions. The universal factorization gives the reverse
map. These two maps yield opposite dimension inequalities, so the intrinsic
rank equals the ordinary rank of the explicit forty-by-fifty row matrix.

Both directions use the actual radical: merely checking displayed forms would
not prove this identity. No rank values or orbit census are asserted here.
The input certificates and ATLAS column conventions are documented in
KernelEquations/FiniteRestriction/QuadraticRelations/LinearMembership/source/README.md.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.ContractionRank
open KernelBound.OrbitCoverCoordinates KernelBound.OrbitCoverCoordinates.LinearMembership
set_option maxRecDepth 2048
attribute [local irreducible] exteriorFormSpace exteriorRadical fixedVectors displacementVectors
  displacementInFixed mixedEmbedding mixedSpace mixedGenerator restrictionLifts restrictionExtraction

/-- Lift mixed coordinates to the fixed subspace. -/
def mixedFixed : (Fin 12 → ZMod 2) →ₗ[ZMod 2] fixedVectors :=
  mixedEmbedding.mulVecLin.codRestrict fixedVectors (by
    intro x
    simp only [fixedVectors, LinearMap.mem_ker]
    change displacement (mixedEmbedding *ᵥ x) = 0
    rw [displacement_apply, Matrix.mulVec_mulVec, mixedEmbedding_fixed, sub_self])

/-- The actual quotient classes of the twelve mixed columns. -/
def mixedClass : (Fin 12 → ZMod 2) →ₗ[ZMod 2] NaturalHomology :=
  displacementInFixed.mkQ.comp mixedFixed

/-- The forty contraction rows in the fifty displacement-lift coordinates. -/
def mixedRowMatrix (x : Fin 12 → ZMod 2) : Matrix (Fin 40) (Fin 50) (ZMod 2) :=
  fun i => x ᵥ* mixedGenerator i

def mixedRowSpace (x : Fin 12 → ZMod 2) : Submodule (ZMod 2) (Fin 50 → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (mixedRowMatrix x))

private def mixedRowMap (x : Fin 12 → ZMod 2) : MixedMatrix →ₗ[ZMod 2] (Fin 50 → ZMod 2) :=
  Matrix.vecMulBilin (ZMod 2) (ZMod 2) x

private theorem mixedRowSpace_eq_map (x : Fin 12 → ZMod 2) :
    mixedRowSpace x = mixedSpace.map (mixedRowMap x) := by
  simp only [mixedSpace, Submodule.map_span, ← Set.range_comp]
  rfl

theorem evaluation_mixed_factor (x : Fin 12 → ZMod 2) (R : Radical) :
    evaluation (mixedClass x) R =
      (x ᵥ* mixedEvaluation R) ᵥ* (restrictionExtraction * (matrixA - 1)) := by
  change (mixedEmbedding *ᵥ x) ᵥ* (R : BinaryMatrix) = _
  rw [Matrix.vecMul_mulVec, radical_mixed_factorization R R.property]
  rw [Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem evaluation_mixed_lifts (x : Fin 12 → ZMod 2) (R : Radical) :
    evaluation (mixedClass x) R ᵥ* restrictionLifts = x ᵥ* mixedEvaluation R := by
  change (mixedEmbedding *ᵥ x) ᵥ* (R : BinaryMatrix) ᵥ* restrictionLifts = _
  rw [Matrix.vecMul_mulVec, Matrix.vecMul_vecMul]
  rfl

private theorem mixed_space_map_lifts (x : Fin 12 → ZMod 2) :
    (space (mixedClass x)).map restrictionLifts.vecMulLinear = mixedRowSpace x := by
  rw [mixedRowSpace_eq_map, ← mixedImageSpace_eq_mixedSpace]
  apply le_antisymm
  · rintro y ⟨u, ⟨R, rfl⟩, rfl⟩
    refine ⟨mixedEvaluation R, ⟨R, R.property, rfl⟩, ?_⟩
    exact (evaluation_mixed_lifts x R).symm
  · rintro y ⟨M, ⟨R, hR, rfl⟩, rfl⟩
    refine ⟨evaluation (mixedClass x) ⟨R, hR⟩, ⟨⟨R, hR⟩, rfl⟩, ?_⟩
    exact evaluation_mixed_lifts x ⟨R, hR⟩

private theorem mixed_space_map_factor (x : Fin 12 → ZMod 2) :
    (mixedRowSpace x).map (restrictionExtraction * (matrixA - 1)).vecMulLinear =
      space (mixedClass x) := by
  rw [mixedRowSpace_eq_map, ← mixedImageSpace_eq_mixedSpace]
  apply le_antisymm
  · rintro y ⟨u, ⟨M, ⟨R, hR, rfl⟩, rfl⟩, rfl⟩
    exact ⟨⟨R, hR⟩, evaluation_mixed_factor x ⟨R, hR⟩⟩
  · rintro y ⟨R, rfl⟩
    refine ⟨x ᵥ* mixedEvaluation R, ⟨mixedEvaluation R, ⟨R, R.property, rfl⟩, rfl⟩, ?_⟩
    exact (evaluation_mixed_factor x R).symm

theorem rank_mixedClass (x : Fin 12 → ZMod 2) :
    rank (mixedClass x) = Module.finrank (ZMod 2) (mixedRowSpace x) := by
  apply Nat.le_antisymm
  · have h := Submodule.finrank_map_le (restrictionExtraction * (matrixA - 1)).vecMulLinear
      (mixedRowSpace x)
    rw [mixed_space_map_factor] at h
    exact h
  · have h := Submodule.finrank_map_le restrictionLifts.vecMulLinear (space (mixedClass x))
    rw [mixed_space_map_lifts] at h
    exact h

theorem rank_mixedClass_matrix (x : Fin 12 → ZMod 2) :
    rank (mixedClass x) = (mixedRowMatrix x).rank := by
  exact (rank_mixedClass x).trans (Matrix.rank_eq_finrank_span_row (mixedRowMatrix x)).symm

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.ContractionRank
