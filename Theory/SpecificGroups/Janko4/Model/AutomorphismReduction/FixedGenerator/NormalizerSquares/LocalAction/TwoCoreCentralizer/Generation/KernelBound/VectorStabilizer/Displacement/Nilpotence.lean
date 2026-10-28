module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.Arithmetic

/-!
# A common image annihilated by all 102 directions

Each displayed direction factors through the same ten-column matrix U.
Its displayed factor annihilates U, so all pairwise products vanish.
Bilinearity extends this to the whole span, proving square-zero displacement.
The small factorization witnesses come from ../source/explore.py.
-/

public section
set_option Elab.async false
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates LinearMembership.FiniteAlgebra

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem factor_checks : ∀ k : Fin 102, ∀ i : Fin 50,
    scan (nilImageRows.get i) (nilFactorRows.get k).toList =
      (slices 50 50 (nilWords.get k)).get i := by
  simp only [slices, get_ofFn]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem annihilation_checks : ∀ k : Fin 102, ∀ i : Fin 10,
    scan ((nilFactorRows.get k).get i) nilImageRows.toList = 0 := by decide +kernel

attribute [local irreducible] nilWords nilFactorRows nilImageRows

theorem nil_basis_factor (k : Fin 102) : nilBasis k = nilImage * nilFactor k := by
  change packedMatrix (nilWords.get k) = _
  rw [packedMatrix, ← decode_slices]
  change _ = rectDecode 10 nilImageRows * rectDecode 50 (nilFactorRows.get k)
  rw [← decode_mulRows]
  congr 1
  apply Vector.ext
  intro i hi
  change (slices 50 50 (nilWords.get k)).get ⟨i, hi⟩ =
    (mulRows nilImageRows (nilFactorRows.get k)).get ⟨i, hi⟩
  simpa only [mulRows, get_ofFn] using (factor_checks k ⟨i, hi⟩).symm

theorem nil_factor_annihilates (k : Fin 102) : nilFactor k * nilImage = 0 := by
  change rectDecode 50 (nilFactorRows.get k) * rectDecode 10 nilImageRows = 0
  rw [← decode_mulRows]
  have h : mulRows (nilFactorRows.get k) nilImageRows = Vector.replicate 10 0 := by
    apply Vector.ext
    intro i hi
    simpa only [mulRows, Vector.getElem_ofFn, Vector.getElem_replicate] using
      annihilation_checks k ⟨i, hi⟩
  rw [h]
  ext i j
  simp [rectDecode, bit, Vector.get]

theorem nil_basis_mul (i j : Fin 102) : nilBasis i * nilBasis j = 0 := by
  rw [nil_basis_factor i, nil_basis_factor j, Matrix.mul_assoc,
    ← Matrix.mul_assoc (nilFactor i), nil_factor_annihilates,
    Matrix.zero_mul, Matrix.mul_zero]

/-- All products in the displayed nilpotent span vanish. -/
theorem nilSpace_mul {X Y : RestrictionMatrix} (hX : X ∈ nilSpace) (hY : Y ∈ nilSpace) :
    X * Y = 0 := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨i, rfl⟩ := hX
    induction hY using Submodule.span_induction with
    | mem Y hY => obtain ⟨j, rfl⟩ := hY; exact nil_basis_mul i j
    | zero => exact Matrix.mul_zero _
    | add Y Z _ _ hY hZ => rw [Matrix.mul_add, hY, hZ, add_zero]
    | smul r Y _ hY => rw [Matrix.mul_smul, hY, smul_zero]
  | zero => exact Matrix.zero_mul _
  | add X Z _ _ hX hZ => rw [Matrix.add_mul, hX, hZ, add_zero]
  | smul r X _ hX => rw [Matrix.smul_mul, hX, smul_zero]

theorem nilSpace_square {X : RestrictionMatrix} (hX : X ∈ nilSpace) : X * X = 0 :=
  nilSpace_mul hX hX

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement
