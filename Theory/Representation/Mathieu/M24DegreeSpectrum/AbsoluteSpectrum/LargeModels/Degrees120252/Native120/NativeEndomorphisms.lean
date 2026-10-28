module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120.Adjoint

/-!
# Interpretation as endomorphisms of the literal Golay quotient

The certified code-coordinate equivalence identifies the matrix conjugation
with conjugation on endomorphisms of `MathieuCode.Code`. It preserves trace,
so it restricts to an equivariant linear equivalence of the trace kernels.
This records the actual native carrier underlying the degree-120 construction.

Source: James, J. Algebra 27 (1973), 57–111; GM02, Proposition 5.1.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120
open MathieuCode Sporadic.Mathieu

/-- In characteristic two the diagonal differences are the requested sums. -/
lemma traceZeroMatrix_binary (j : Fin 120) :
    traceZeroMatrix j = Matrix.single (position j).1 (position j).2 1 +
      if (position j).1 = (position j).2 then Matrix.single 10 10 1 else 0 := by
  ext i k
  exact CharTwo.sub_eq_add _ _

/-- Endomorphisms of the literal code, in the certified Golay row basis. -/
def nativeEndEquiv : Module.End (ZMod 2) Code ≃ₐ[ZMod 2] CodeMat :=
  (codeEquiv.conjAlgEquiv (ZMod 2)).trans LinearMap.toMatrixAlgEquiv'

lemma nativeEndEquiv_codeRepresentation (g : M24) :
    nativeEndEquiv (codeRepresentation g) = nativeCodeMatrix g := rfl

lemma nativeEndEquiv_conjugation (g : M24) (f : Module.End (ZMod 2) Code) :
    nativeEndEquiv ((codeRepresentation.linHom codeRepresentation) g f) =
      conjugation g (nativeEndEquiv f) := by
  change nativeEndEquiv (codeRepresentation g * f * codeRepresentation g⁻¹) =
    nativeCodeMatrix g * nativeEndEquiv f * nativeCodeMatrix g⁻¹
  simp only [map_mul, nativeEndEquiv_codeRepresentation]

lemma nativeEndEquiv_trace (f : Module.End (ZMod 2) Code) :
    Matrix.trace (nativeEndEquiv f) = LinearMap.trace (ZMod 2) Code f := by
  change Matrix.trace (LinearMap.toMatrix' (codeEquiv.conj f)) = _
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  exact LinearMap.trace_conj' f codeEquiv

/-- Conjugation on trace-zero endomorphisms of the original native code. -/
def nativeTraceZero : Subrepresentation (codeRepresentation.linHom codeRepresentation) where
  toSubmodule := (LinearMap.trace (ZMod 2) Code).ker
  apply_mem_toSubmodule g f hf := by
    change LinearMap.trace (ZMod 2) Code (codeRepresentation g * f * codeRepresentation g⁻¹) = 0
    rw [LinearMap.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, one_mul]
    exact hf

abbrev NativeTraceZeroSpace := (LinearMap.trace (ZMod 2) Code).ker
abbrev nativeTraceZeroRepresentation := nativeTraceZero.toRepresentation

def nativeTraceZeroEquiv : NativeTraceZeroSpace ≃ₗ[ZMod 2] TraceZeroSpace where
  toFun f := ⟨nativeEndEquiv f.val, by
    change Matrix.trace (nativeEndEquiv f.val) = 0
    rw [nativeEndEquiv_trace]
    exact f.property⟩
  invFun X := ⟨nativeEndEquiv.symm X.val, by
    change LinearMap.trace (ZMod 2) Code (nativeEndEquiv.symm X.val) = 0
    rw [← nativeEndEquiv_trace, nativeEndEquiv.apply_symm_apply]
    exact X.property⟩
  left_inv f := by apply Subtype.ext; exact nativeEndEquiv.symm_apply_apply f.val
  right_inv X := by apply Subtype.ext; exact nativeEndEquiv.apply_symm_apply X.val
  map_add' f h := by apply Subtype.ext; exact map_add nativeEndEquiv f.val h.val
  map_smul' c f := by apply Subtype.ext; exact map_smul nativeEndEquiv c f.val

/-- The trace-kernel comparison intertwines every element of native M24. -/
theorem nativeTraceZeroEquiv_equivariant (g : M24) (f : NativeTraceZeroSpace) :
    nativeTraceZeroEquiv (nativeTraceZeroRepresentation g f) =
      traceZeroRepresentation g (nativeTraceZeroEquiv f) := by
  apply Subtype.ext
  exact nativeEndEquiv_conjugation g f.val

/-- Native endomorphism coordinates used by the degree-120 action. -/
def nativeAdjointEquiv : NativeTraceZeroSpace ≃ₗ[ZMod 2] (Fin 120 → ZMod 2) :=
  nativeTraceZeroEquiv.trans adjointEquiv

theorem nativeAdjointEquiv_equivariant (g : M24) (f : NativeTraceZeroSpace) :
    nativeAdjointEquiv (nativeTraceZeroRepresentation g f) =
      adjointRepresentation g (nativeAdjointEquiv f) := by
  change adjointEquiv (nativeTraceZeroEquiv (nativeTraceZeroRepresentation g f)) =
    adjointEquiv (traceZeroRepresentation g
      (adjointEquiv.symm (adjointEquiv (nativeTraceZeroEquiv f))))
  rw [nativeTraceZeroEquiv_equivariant, adjointEquiv.symm_apply_apply]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120
