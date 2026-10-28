module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Matrices

/-!
# Witnesses for the cyclic-kernel density certificate

The seeds below are candidate right and left null vectors of
`1 + b + a*b + b*a`, in the literal coordinates of `Matrices.lean`.
Bit j represents coordinate j. The contracts separate the kernel calculation
from the two cyclicity calculations; defining them asserts none of them.
The final density assembly must prove all three contracts.

Source: the ATLAS restriction described in `../source/README.md`.
The exact binary discovery script and its output are retained in the task's
`Scratch/HS1408Density/discovery/`, copied without altering the parent work.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density

/-- Decode a packed row or column without changing coordinate order. -/
def vectorOfBits (x : ℕ) : Vector := fun i => Thompson.BinaryMatrix.bit x i.val

/-- A candidate generator of the right kernel. -/
def kernelVector : Vector := vectorOfBits 3037566777681267535834465479477380210446177044093850219542017719937461953016038750181753272333662566324377528990954025738249985938610247160176175638580520348176498059831193934536735574962891405363127719209003405508515098615267758094552103906262663260137666912768254730890609589573719963388200362861770965963113113402544595261017349602099599066548935105647282472801271845992658676808526609012602330107685271989261917926201689

/-- A candidate generator of the left kernel, used as a row vector. -/
def kernelCovector : Vector := vectorOfBits 6139659506272620636799992634585864912974850861989027553578679464913486302281527940175156070320392067611652369546924542021397720996761118473793348864471114369508769626501072600596880300320335650299740397691746171392531800198810740112039712369436304016295946974394247809937077352640764210711792336474238360822535962832740291840144514467706461618504933402428400203289257630659796294098578531096526360994385659558891729078815382

/-- The singular algebra element used in the density argument. -/
def separatingMatrix : Mat := 1 + matrixB + matrixA * matrixB + matrixB * matrixA

/-- The actual matrix algebra, independently of any group action. -/
def generatedAlgebra : Subalgebra (ZMod 2) Mat := Algebra.adjoin (ZMod 2) {matrixA, matrixB}

/-- Exact right kernel and a left annihilator for the literal singular element. -/
def KernelCertificate : Prop :=
  separatingMatrix.mulVec kernelVector = 0 ∧
  (∀ w : Vector, separatingMatrix.mulVec w = 0 →
    ∃ c : ZMod 2, w = c • kernelVector) ∧
  Matrix.vecMul kernelCovector separatingMatrix = 0

/-- Every column is an algebra translate of the right-kernel seed. -/
def ColumnCyclic : Prop :=
  ∀ w : Vector, ∃ M ∈ generatedAlgebra, M.mulVec kernelVector = w

/-- Every row is an algebra translate of the left-kernel seed. -/
def RowCyclic : Prop :=
  ∀ w : Vector, ∃ M ∈ generatedAlgebra, Matrix.vecMul kernelCovector M = w

theorem kernelVector_ne_zero : kernelVector ≠ 0 := by
  intro h
  have he := congrFun h 0
  have hc : kernelVector 0 = 1 := by decide +kernel
  rw [hc] at he
  exact one_ne_zero he

theorem kernelCovector_ne_zero : kernelCovector ≠ 0 := by
  intro h
  have he := congrFun h 1
  have hc : kernelCovector 1 = 1 := by decide +kernel
  rw [hc] at he
  exact one_ne_zero he

theorem matrixA_mem : matrixA ∈ generatedAlgebra :=
  Algebra.subset_adjoin (by simp)

theorem matrixB_mem : matrixB ∈ generatedAlgebra :=
  Algebra.subset_adjoin (by simp)

theorem separatingMatrix_mem : separatingMatrix ∈ generatedAlgebra :=
  generatedAlgebra.add_mem
    (generatedAlgebra.add_mem (generatedAlgebra.add_mem generatedAlgebra.one_mem matrixB_mem)
      (generatedAlgebra.mul_mem matrixA_mem matrixB_mem))
    (generatedAlgebra.mul_mem matrixB_mem matrixA_mem)

end Representation.HigmanSims.LargeModels.Restricted1408.Density
