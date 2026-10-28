module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Algebra
public import Mathlib.Tactic.LinearCombination
/-! The symmetric bilinear certificate extends the quadratic identity from the
published affine directions to their span over F₂. The diagonal is additive
because equal cross terms cancel, and every scalar is zero or one.
Source and witness conventions: Reconstruction/source/README.md. -/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate

theorem bilinear_symmetric_on_span
    (h : ∀ i j, bilinear (affineDirection i) (affineDirection j) =
      bilinear (affineDirection j) (affineDirection i))
    {X Y : RestrictionMatrix} (hX : X ∈ affineDirections) (hY : Y ∈ affineDirections) :
    bilinear X Y = bilinear Y X := by
  change X ∈ Submodule.span (ZMod 2) (Set.range affineDirection) at hX
  change Y ∈ Submodule.span (ZMod 2) (Set.range affineDirection) at hY
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨i, rfl⟩ := hX
    induction hY using Submodule.span_induction with
    | mem Y hY => obtain ⟨j, rfl⟩ := hY; exact h i j
    | zero => rw [bilinear_zero_left, bilinear_zero_right]
    | add Y Z _ _ hY hZ => rw [bilinear_add_left, bilinear_add_right, hY, hZ]
    | smul c Y _ hY => rw [bilinear_smul_left, bilinear_smul_right, hY]
  | zero => rw [bilinear_zero_left, bilinear_zero_right]
  | add X Z _ _ hX hZ => rw [bilinear_add_left, bilinear_add_right, hX, hZ]
  | smul c X _ hX => rw [bilinear_smul_left, bilinear_smul_right, hX]

def polynomial (X : RestrictionMatrix) : ZMod 2 :=
  bilinear X X + bilinear 1 X + bilinear X 1

theorem polynomial_zero : polynomial 0 = 0 := by
  simp [polynomial, bilinear_zero_left, bilinear_zero_right]

theorem polynomial_add {X Y : RestrictionMatrix} (h : bilinear X Y = bilinear Y X) :
    polynomial (X + Y) = polynomial X + polynomial Y := by
  simp only [polynomial, bilinear_add_left, bilinear_add_right]
  have hc : bilinear Y X + bilinear Y X = 0 := by
    generalize bilinear Y X = c
    revert c
    decide
  rw [h]
  linear_combination hc

theorem polynomial_on_span
    (hsym : ∀ i j, bilinear (affineDirection i) (affineDirection j) =
      bilinear (affineDirection j) (affineDirection i))
    (hdir : ∀ i, polynomial (affineDirection i) = defectScalar (affineDirection i))
    {X : RestrictionMatrix} (hX : X ∈ affineDirections) : polynomial X = defectScalar X := by
  change X ∈ Submodule.span (ZMod 2) (Set.range affineDirection) at hX
  induction hX using Submodule.span_induction with
  | mem X hX => obtain ⟨i, rfl⟩ := hX; exact hdir i
  | zero => simp [polynomial_zero, defectScalar]
  | add X Y hX hY ihX ihY =>
    rw [polynomial_add (bilinear_symmetric_on_span hsym hX hY), ihX, ihY]
    simp [defectScalar]
  | smul c X _ ih =>
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simp [polynomial_zero, defectScalar]
    · simpa using ih

theorem polynomial_preservation_expression (S : RestrictionMatrix) :
    polynomial (S - 1) =
      lj (Sᵀ * restrictionPairing * S + restrictionPairing) +
      le (Sᵀ * restrictionTestForm 0 * S + restrictionTestForm 0) := by
  have hs : S = 1 + (S - 1) := by abel
  conv_rhs => rw [hs]
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul,
    Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, map_add, polynomial, bilinear]
  have hJ : lj restrictionPairing + lj restrictionPairing = 0 := by
    generalize lj restrictionPairing = c
    revert c
    decide
  have hE : le (restrictionTestForm 0) + le (restrictionTestForm 0) = 0 := by
    generalize le (restrictionTestForm 0) = c
    revert c
    decide
  linear_combination -hJ - hE

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
