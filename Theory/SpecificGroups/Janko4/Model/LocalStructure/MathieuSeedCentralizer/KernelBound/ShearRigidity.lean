module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.AmbientConditions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.TestForms
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.FinalTest
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.PairingKernel

/-!
# Assembly of the pointwise seed-centralizer shear calculation

The actual model supplies symmetry of JH and both mixed restriction tests.
The first restriction has a certified inverse; the second removes the extra
direction in the two-dimensional pairing kernel by a four-entry functional.
This module currently leaves explicit two independent linear-algebra premises:
the upper bound on the complete mixed-kernel space and the complete pairing
kernel in the candidate span. It does not yet assert unconditional rigidity.

Source: `KernelBound/source/README.md` and `ShearRigidity/source/README.md`.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound
open Coordinates ShearRigidity

/-- The two finite linear-algebra obligations suffice for actual model rigidity. -/
theorem eq_one_or_seed_of_restriction_eq_one_of_linear_certificates
    (hmixed : mixedKernelSpace ≤ mixedSpan)
    (hpair : ∀ H : HalfMatrix, H ∈ candidateSpan →
      (wallPairing * H)ᵀ = wallPairing * H →
      ∃ a b : ZMod 2, H = a • (1 : HalfMatrix) + b • extraShear)
    (c : SeedCentralizer) (hc : restriction c = 1) :
    (c : Model) = 1 ∨
      (c : Model) = (Cardinality.localKernelSeed matrixA_mul_self matrixB_pow_four : Model) := by
  let H := shearBlock (toMatrix (c : Model))
  have htest (t : Fin 2) : testRestriction t * H ∈ mixedSpan := by
    apply hmixed
    have h := centralizer_shear_mixed_constraint c hc (testForm t) (testForm_mem t)
    change upperBlockLinear (testForm t) * H ∈ mixedKernelSpace at h
    rwa [testForm_upper] at h
  have hp := hpair H (mem_candidateSpan_of_first_test H (htest 0))
    (centralizer_shear_pairing_constraint c hc)
  exact centralizer_eq_one_or_seed_of_shear c hc
    (eq_zero_or_one_of_second_test H hp (htest 1))

/-- A full-centralizer element fixing the seed subspace pointwise is one or the
published local-kernel seed. -/
theorem eq_one_or_seed_of_restriction_eq_one
    (c : SeedCentralizer) (hc : restriction c = 1) :
    (c : Model) = 1 ∨
      (c : Model) = (Cardinality.localKernelSeed matrixA_mul_self matrixB_pow_four : Model) := by
  exact eq_one_or_seed_of_restriction_eq_one_of_linear_certificates
    mixedKernelSpace_le_mixedSpan pairing_kernel c hc

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound
