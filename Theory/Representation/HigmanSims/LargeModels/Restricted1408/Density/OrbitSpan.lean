module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Witnesses

/-!
# From invariant spans to algebra translates

The algebra translates of a vector form a vector subspace stable under
left multiplication by any algebra element. The corresponding row space
is stable under right multiplication. Thus a finite orbit-spanning
certificate can prove cyclicity by testing invariant subspaces, without
constructing a separate algebra expression for every target vector.
These lemmas feed the two literal degree-1408 cyclicity contracts.
-/

public section

namespace Representation.CyclicKernel
open Matrix
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

theorem column_cyclic_of_invariant (P : Subalgebra F (Matrix ι ι F))
    (a b : Matrix ι ι F) (v : ι → F) (ha : a ∈ P) (hb : b ∈ P)
    (h : ∀ W : Submodule F (ι → F),
      (∀ x ∈ W, a.mulVec x ∈ W) → (∀ x ∈ W, b.mulVec x ∈ W) →
      v ∈ W → W = ⊤) :
    ∀ w, ∃ M ∈ P, M.mulVec v = w := by
  let W : Submodule F (ι → F) :=
    { carrier := {w | ∃ M ∈ P, M.mulVec v = w}
      zero_mem' := ⟨0, P.zero_mem, Matrix.zero_mulVec _⟩
      add_mem' := by
        rintro x y ⟨M, hM, rfl⟩ ⟨N, hN, rfl⟩
        exact ⟨M + N, P.add_mem hM hN, Matrix.add_mulVec _ _ _⟩
      smul_mem' := by
        rintro c x ⟨M, hM, rfl⟩
        exact ⟨c • M, P.smul_mem hM c, Matrix.smul_mulVec _ _ _⟩ }
  have stable (N : Matrix ι ι F) (hN : N ∈ P) : ∀ x ∈ W, N.mulVec x ∈ W := by
    rintro x ⟨M, hM, rfl⟩
    exact ⟨N * M, P.mul_mem hN hM, (Matrix.mulVec_mulVec v N M).symm⟩
  have hv : v ∈ W := ⟨1, P.one_mem, Matrix.one_mulVec _⟩
  have hW := h W (stable a ha) (stable b hb) hv
  intro w
  have hw : w ∈ W := hW ▸ Submodule.mem_top
  exact hw

theorem row_cyclic_of_invariant (P : Subalgebra F (Matrix ι ι F))
    (a b : Matrix ι ι F) (lam : ι → F) (ha : a ∈ P) (hb : b ∈ P)
    (h : ∀ W : Submodule F (ι → F),
      (∀ x ∈ W, Matrix.vecMul x a ∈ W) → (∀ x ∈ W, Matrix.vecMul x b ∈ W) →
      lam ∈ W → W = ⊤) :
    ∀ w, ∃ M ∈ P, Matrix.vecMul lam M = w := by
  let W : Submodule F (ι → F) :=
    { carrier := {w | ∃ M ∈ P, Matrix.vecMul lam M = w}
      zero_mem' := ⟨0, P.zero_mem, Matrix.vecMul_zero _⟩
      add_mem' := by
        rintro x y ⟨M, hM, rfl⟩ ⟨N, hN, rfl⟩
        exact ⟨M + N, P.add_mem hM hN, Matrix.vecMul_add _ _ _⟩
      smul_mem' := by
        rintro c x ⟨M, hM, rfl⟩
        exact ⟨c • M, P.smul_mem hM c, Matrix.vecMul_smul _ _ _⟩ }
  have stable (N : Matrix ι ι F) (hN : N ∈ P) : ∀ x ∈ W, Matrix.vecMul x N ∈ W := by
    rintro x ⟨M, hM, rfl⟩
    exact ⟨M * N, P.mul_mem hM hN, (Matrix.vecMul_vecMul lam M N).symm⟩
  have hv : lam ∈ W := ⟨1, P.one_mem, Matrix.vecMul_one _⟩
  have hW := h W (stable a ha) (stable b hb) hv
  intro w
  have hw : w ∈ W := hW ▸ Submodule.mem_top
  exact hw
end Representation.CyclicKernel

namespace Representation.HigmanSims.LargeModels.Restricted1408.Density

/-- Apply the invariant-span test with the actual column actions. -/
theorem columnCyclic_of_invariant
    (h : ∀ W : Submodule (ZMod 2) Vector,
      (∀ x ∈ W, matrixA.mulVec x ∈ W) →
      (∀ x ∈ W, matrixB.mulVec x ∈ W) → kernelVector ∈ W → W = ⊤) :
    ColumnCyclic :=
  CyclicKernel.column_cyclic_of_invariant generatedAlgebra matrixA matrixB kernelVector
    matrixA_mem matrixB_mem h

/-- Apply the invariant-span test with the actual right row actions. -/
theorem rowCyclic_of_invariant
    (h : ∀ W : Submodule (ZMod 2) Vector,
      (∀ x ∈ W, Matrix.vecMul x matrixA ∈ W) →
      (∀ x ∈ W, Matrix.vecMul x matrixB ∈ W) → kernelCovector ∈ W → W = ⊤) :
    RowCyclic :=
  CyclicKernel.row_cyclic_of_invariant generatedAlgebra matrixA matrixB kernelCovector
    matrixA_mem matrixB_mem h

end Representation.HigmanSims.LargeModels.Restricted1408.Density
