module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Data

/-!
# Complete coefficient reconstruction and mixed-image transfer

The recovery identities express every coordinate, modulo a combination of the
595 upper-block equations, in terms of the 626 displayed free coordinates.
Consequently every solution is a linear combination of the displayed kernel
vectors. Checked mixed-image expressions then put its image in mixedSpan.
Calibration refers to the actual exteriorBasisForm and shared formCoordinates.

Source: source/README.md and the untrusted witnesses in Data.lean.
-/

@[expose] public section
set_option maxRecDepth 10000
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open LinearMembership FiniteAlgebra

abbrev Coefficients := Fin 1221 → ZMod 2

def kernelVector (k : Fin 626) : Coefficients :=
  fun i => bit (kernelCoefficients.get k) i.val

/-- One identity in the complete coefficient reconstruction. -/
def RecoveryCheck (i : Fin 1221) : Prop :=
  scan (recoveryRows.get i) evaluationRows.toList =
    2 ^ i.val ^^^ xorList (List.ofFn (fun k : Fin 626 =>
      if (kernelCoefficients.get k).testBit i.val then 2 ^ (freeIndices.get k).val else 0))

/-- Both sides are in the original, published ordering of their generators. -/
def MixedCheck (k : Fin 626) : Prop :=
  scan (kernelCoefficients.get k) originalMixedWords.toList =
    scan (mixedCombinations.get k) mixedWords.toList

/-- The selected equations and mixed words describe the actual transported form. -/
def Calibration (i : Fin 1221) : Prop :=
  (∀ t : Fin 595, bit (evaluationRows.get t) i.val =
    upperBlockLinear (formCoordinates (exteriorBasisForm i))
      (upperPositions.get t).1 (upperPositions.get t).2) ∧
  decodeHalf (originalMixedWords.get i) =
    mixedBlockLinear (formCoordinates (exteriorBasisForm i))

attribute [local irreducible] evaluationRows kernelCoefficients recoveryRows freeIndices
  originalMixedWords mixedWords mixedCombinations upperPositions

/-- Exhaustive reconstruction: the input coefficient vector is arbitrary. -/
theorem reconstruct (h : ∀ i, RecoveryCheck i) (c : Coefficients)
    (hc : ∀ t : Fin 595, ev c (evaluationRows.get t) = 0) :
    c = ∑ k : Fin 626, c (freeIndices.get k) • kernelVector k := by
  apply FiniteAlgebra.reconstruct c freeIndices kernelCoefficients
    (fun i => scan (recoveryRows.get i) evaluationRows.toList)
  · intro i
    rw [ev_scan]
    simp only [hc, mul_zero, Finset.sum_const_zero]
  · exact h

def mixedCoefficientMap : Coefficients →ₗ[ZMod 2] HalfMatrix where
  toFun c := ∑ i, c i • decodeHalf (originalMixedWords.get i)
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

theorem decodeHalf_scan {n : ℕ} (c : ℕ) (xs : Vector ℕ n) :
    decodeHalf (scan c xs.toList) = ∑ i, bit c i.val • decodeHalf (xs.get i) := by
  ext a b
  simp only [decodeHalf, bit_scan, ev, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem mixed_kernelVector (k : Fin 626) :
    mixedCoefficientMap (kernelVector k) =
      decodeHalf (scan (kernelCoefficients.get k) originalMixedWords.toList) := by
  rw [decodeHalf_scan]
  rfl

theorem mixed_kernelVector_mem (h : ∀ k, MixedCheck k) (k : Fin 626) :
    mixedCoefficientMap (kernelVector k) ∈ mixedSpan := by
  rw [mixed_kernelVector, h k, decodeHalf_scan]
  exact mixedSpan.sum_mem (fun i _ =>
    mixedSpan.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))

theorem mixedCoefficientMap_mem_of_checks
    (hr : ∀ i, RecoveryCheck i) (hm : ∀ k, MixedCheck k) (c : Coefficients)
    (hc : ∀ t : Fin 595, ev c (evaluationRows.get t) = 0) :
    mixedCoefficientMap c ∈ mixedSpan := by
  rw [reconstruct hr c hc, map_sum]
  exact mixedSpan.sum_mem (fun k _ => by
    rw [map_smul]
    exact mixedSpan.smul_mem _ (mixed_kernelVector_mem hm k))

/-- Full source-space containment, conditional only on explicit finite checks. -/
theorem mixedKernelSpace_le_of_checks
    (hc : ∀ i, Calibration i) (hr : ∀ i, RecoveryCheck i)
    (hm : ∀ k, MixedCheck k) : mixedKernelSpace ≤ mixedSpan := by
  rintro X ⟨F, ⟨hF, hu⟩, rfl⟩
  obtain ⟨E, hE, rfl⟩ := hF
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hE
  change upperBlockLinear (formCoordinatesLinear (∑ i, c i • exteriorBasisForm i)) = 0 at hu
  have he (t : Fin 595) : ev c (evaluationRows.get t) = 0 := by
    have ht := congrArg (fun M : HalfMatrix => M (upperPositions.get t).1
      (upperPositions.get t).2) hu
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.zero_apply, smul_eq_mul] at ht
    change (∑ i, c i * upperBlockLinear (formCoordinates (exteriorBasisForm i))
      (upperPositions.get t).1 (upperPositions.get t).2) = 0 at ht
    simpa only [ev, (hc _).1, mul_comm] using ht
  have hx := mixedCoefficientMap_mem_of_checks hr hm c he
  convert hx using 1
  simp only [map_sum, map_smul]
  change (∑ i, c i • mixedBlockLinear (formCoordinates (exteriorBasisForm i))) =
    ∑ i, c i • decodeHalf (originalMixedWords.get i)
  simp only [(hc _).2]

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness
