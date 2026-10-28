module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.Definitions
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.Packed

/-!
# The inverse first restriction and exclusion of the extra shear

A four-entry functional annihilates every proposed mixed generator and R₁,
but evaluates to one on R₁ times the extra shear. It therefore removes the
second coefficient from the complete two-dimensional pairing kernel, once
that separate kernel calculation and mixed-space bound are supplied.

All finite identities here are checked by kernel reduction. Source and bit
conventions: `source/README.md` and `Data.lean`.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership

set_option maxRecDepth 10000 in
private theorem inverse_product_rows (i : Fin 56) :
    rectRowProduct (r0InverseRows.get i) r0Rows = 2 ^ i.val := by
  revert i
  decide +kernel

/-- The numerical inverse is a left inverse of the actual first test matrix. -/
theorem inverseRestriction_mul : inverseRestriction * testRestriction 0 = 1 := by
  change rectDecode 56 r0InverseRows * rectDecode 56 r0Rows = 1
  rw [← rectDecode_one 56]
  apply rectProduct_eq
  simpa only [get_ofFn] using inverse_product_rows

theorem inverse_mul_mem_candidateSpan (M : HalfMatrix) (hM : M ∈ mixedSpan) :
    inverseRestriction * M ∈ candidateSpan := by
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨i, rfl⟩ := hM
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simpa only [mul_zero] using candidateSpan.zero_mem
  | add M N _ _ hM hN =>
    simpa only [mul_add] using candidateSpan.add_mem hM hN
  | smul a M _ hM =>
    simpa only [Matrix.mul_smul] using candidateSpan.smul_mem a hM

/-- No coefficient of a possible shear is lost in the first restriction test. -/
theorem mem_candidateSpan_of_first_test (H : HalfMatrix)
    (hH : testRestriction 0 * H ∈ mixedSpan) : H ∈ candidateSpan := by
  have h := inverse_mul_mem_candidateSpan _ hH
  rwa [← mul_assoc, inverseRestriction_mul, one_mul] at h

private theorem separatingFunctional_basis (i : Fin 616) :
    separatingFunctional (mixedBasis i) = 0 := by
  revert i
  decide +kernel

/-- This vanishing holds on the entire proposed mixed span. -/
theorem separatingFunctional_span (M : HalfMatrix) (hM : M ∈ mixedSpan) :
    separatingFunctional M = 0 := by
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨i, rfl⟩ := hM
    exact separatingFunctional_basis i
  | zero => exact map_zero _
  | add M N _ _ hM hN => rw [map_add, hM, hN, add_zero]
  | smul a M _ hM => rw [map_smul, hM, smul_zero]

private theorem separatingFunctional_restriction :
    separatingFunctional (testRestriction 1) = 0 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem extra_product_rows (i : Fin 56) :
    rectRowProduct (r1Rows.get i) extraShearRows = extraProductRows.get i := by
  revert i
  decide +kernel

private theorem extra_product :
    testRestriction 1 * extraShear = rowsHalf extraProductRows := by
  change rectDecode 56 r1Rows * rectDecode 56 extraShearRows = rectDecode 56 extraProductRows
  exact rectProduct_eq _ _ _ extra_product_rows

private theorem separatingFunctional_extra :
    separatingFunctional (testRestriction 1 * extraShear) = 1 := by
  rw [extra_product]
  decide +kernel

/-- The second mixed test eliminates the nonidentity direction. -/
theorem eq_scalar_one_of_second_test (H : HalfMatrix) (a b : ZMod 2)
    (hH : H = a • (1 : HalfMatrix) + b • extraShear)
    (hsecond : testRestriction 1 * H ∈ mixedSpan) : H = a • (1 : HalfMatrix) := by
  have hz := separatingFunctional_span _ hsecond
  rw [hH, mul_add, Matrix.mul_smul, Matrix.mul_smul, mul_one,
    map_add, map_smul, map_smul, separatingFunctional_restriction,
    separatingFunctional_extra, smul_zero, zero_add, smul_eq_mul, mul_one] at hz
  simpa only [hz, zero_smul, add_zero] using hH

/-- Over F₂ the surviving scalar line has exactly two matrices. -/
theorem eq_zero_or_one_of_second_test (H : HalfMatrix)
    (hpair : ∃ a b : ZMod 2, H = a • (1 : HalfMatrix) + b • extraShear)
    (hsecond : testRestriction 1 * H ∈ mixedSpan) : H = 0 ∨ H = 1 := by
  obtain ⟨a, b, hab⟩ := hpair
  have h := eq_scalar_one_of_second_test H a b hab hsecond
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl
  · exact Or.inl (by simpa only [zero_smul] using h)
  · exact Or.inr (by simpa only [one_smul] using h)

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity
