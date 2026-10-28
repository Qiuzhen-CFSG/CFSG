module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Contracts
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Products
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Annihilator

/-!
# Assembly of the exact right-kernel certificate

The packed-table certificate identifies the literal singular matrix. The
independent reduction certificate identifies its solutions with the explicit
rows `e_i + v_i e_0`, where v is the unchanged published seed and v_0 = 1.
This gives both annihilation of v and the entire kernel line. The proved left
annihilator supplies the last clause. No cyclicity, density, irreducibility,
or carrier descent is an input.

The complete checked products and solution-preserving reduction discharge both
numerical premises of the unconditional `kernelCertificate`. Source and checked
arithmetic boundaries are documented in `Kernel/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density
open KernelData

/-- Both independent checks identify the literal singular matrix's entire kernel. -/
theorem separatingMatrix_kernel_iff_of_checks (hRows : RowTableCertificate)
    (hReduction : ReductionCertificate) (w : Vector) :
    separatingMatrix.mulVec w = 0 ↔ w = w 0 • kernelVector := by
  rw [separatingMatrix_eq_decode hRows, ← initial_solutions_iff,
    ← hReduction w]
  exact kernelNormalForm_solutions w

/-- The independent checks imply annihilation of the unchanged published seed. -/
theorem kernelVector_annihilated_of_checks (hRows : RowTableCertificate)
    (hReduction : ReductionCertificate) : separatingMatrix.mulVec kernelVector = 0 := by
  apply (separatingMatrix_kernel_iff_of_checks hRows hReduction kernelVector).mpr
  have h0 : kernelVector 0 = 1 := by decide +kernel
  rw [h0, one_smul]

/-- Kernel-certificate assembly from the two independent numerical checks. -/
theorem kernelCertificate_of_checks (hRows : RowTableCertificate)
    (hReduction : ReductionCertificate) : KernelCertificate := by
  refine ⟨kernelVector_annihilated_of_checks hRows hReduction, ?_, kernelCovector_annihilates⟩
  intro w hw
  exact ⟨w 0, (separatingMatrix_kernel_iff_of_checks hRows hReduction w).mp hw⟩

/-- The entire right kernel of the literal singular matrix is the published seed line. -/
theorem separatingMatrix_kernel_iff (w : Vector) :
    separatingMatrix.mulVec w = 0 ↔ w = w 0 • kernelVector :=
  separatingMatrix_kernel_iff_of_checks rowTableCertificate reductionCertificate w

/-- The literal singular matrix annihilates the unchanged published right seed. -/
theorem kernelVector_annihilated : separatingMatrix.mulVec kernelVector = 0 :=
  kernelVector_annihilated_of_checks rowTableCertificate reductionCertificate

/-- The exact right kernel and left annihilator for the literal degree-1408 matrix. -/
theorem kernelCertificate : KernelCertificate :=
  kernelCertificate_of_checks rowTableCertificate reductionCertificate

end Representation.HigmanSims.LargeModels.Restricted1408.Density
