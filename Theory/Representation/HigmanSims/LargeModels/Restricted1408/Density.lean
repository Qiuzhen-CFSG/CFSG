module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.MatrixCriterion
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.OrbitSpan
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Annihilator
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity

/-!
# Assembly of the degree-1408 matrix density certificate

The singular element `1 + b + a*b + b*a` belongs to the algebra of the
literal ATLAS restriction matrices. The checked exact right-kernel line,
left annihilator and two cyclic orbit spans satisfy the cyclic-kernel
criterion. Thus `matrixAlgebraIsFull` proves that the literal pair generates
the whole matrix algebra, with every finite certificate discharged.

Source and coordinate conventions: `Restricted1408/source/README.md`.
This calculation is independent of descent to the permutation-defined HS
carrier. The existing `Restricted1408.lean` consumes the resulting density
statement together with the independently owned marked descent.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408
open Density

/-- The three finite certificates imply full density for the literal pair. -/
theorem matrixAlgebraIsFull_of_certificates
    (hk : KernelCertificate) (hc : ColumnCyclic) (hr : RowCyclic) :
    MatrixAlgebraIsFull :=
  CyclicKernel.matrix_top generatedAlgebra separatingMatrix kernelVector kernelCovector
    separatingMatrix_mem hk.1 hk.2.1 hc hr hk.2.2

/-- Only the right-kernel and cyclicity checks remain after the proved left
annihilator. No normalization of the two seeds' pairing is required. -/
theorem matrixAlgebraIsFull_of_right_kernel_and_cyclic
    (hsv : separatingMatrix.mulVec kernelVector = 0)
    (hker : ∀ w : Vector, separatingMatrix.mulVec w = 0 →
      ∃ c : ZMod 2, w = c • kernelVector)
    (hc : ColumnCyclic) (hr : RowCyclic) : MatrixAlgebraIsFull :=
  matrixAlgebraIsFull_of_certificates
    ⟨hsv, hker, kernelCovector_annihilates⟩ hc hr

/-- The literal restricted degree-1408 matrices generate the full binary matrix
algebra. The exact kernel and both cyclic orbit certificates are unconditional. -/
theorem matrixAlgebraIsFull : MatrixAlgebraIsFull :=
  matrixAlgebraIsFull_of_certificates kernelCertificate columnCyclic rowCyclic

end Representation.HigmanSims.LargeModels.Restricted1408
