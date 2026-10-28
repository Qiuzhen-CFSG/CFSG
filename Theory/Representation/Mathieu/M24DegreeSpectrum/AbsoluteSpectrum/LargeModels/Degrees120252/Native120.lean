module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120.Actors
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120.Comparison
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120.NativeEndomorphisms
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120.Transport

/-!
# Native realization of the degree-120 binary M24 matrices

Golay rows 0 through 10 modulo the constant line give coordinates on the
native code. Conjugation on its trace-zero endomorphisms gives a lawful action
in dimension 120. The checked matrix-unit basis and invertible comparison
identify the two literal native generators with `matrix120`.

No irreducibility premise enters the realization. The final binary-model
application retains matrix density explicitly for the parent assembly.

Sources: James, J. Algebra 27 (1973), 57–111; GM02, Proposition 5.1;
`Degrees120252/source/README.md` for the saved comparison and conventions.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252
open Sporadic.Mathieu

/-- The literal matrix pair acts lawfully through native M24. -/
def native120Realization : NativeRealization 120 matrix120 :=
  Native120.transportRealization Native120.adjointRealization
    Native120.comparison_mul_inverse Native120.inverse_mul_comparison
    Native120.comparison_intertwines

theorem nonempty_native120 : Nonempty (NativeRealization 120 matrix120) :=
  ⟨native120Realization⟩

/-- The actual source carrier, in the final degree-120 matrix coordinates. -/
def native120Equiv : Native120.NativeTraceZeroSpace ≃ₗ[ZMod 2] (Fin 120 → ZMod 2) :=
  Native120.nativeAdjointEquiv.trans
    (Native120.comparisonEquiv Native120.comparison_mul_inverse Native120.inverse_mul_comparison)

/-- The constructed representation is conjugation on the native code trace kernel. -/
theorem native120Equiv_equivariant (g : M24) (f : Native120.NativeTraceZeroSpace) :
    native120Equiv (Native120.nativeTraceZeroRepresentation g f) =
      native120Realization.representation g (native120Equiv f) := by
  let e := Native120.comparisonEquiv Native120.comparison_mul_inverse Native120.inverse_mul_comparison
  change e (Native120.nativeAdjointEquiv (Native120.nativeTraceZeroRepresentation g f)) =
    e (Native120.adjointRepresentation g (e.symm (e (Native120.nativeAdjointEquiv f))))
  rw [Native120.nativeAdjointEquiv_equivariant, e.symm_apply_apply]

/-- Density remains the independent premise owned by the larger-model assembly. -/
def binaryModel120_of_density
    (hA : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)),
      (∀ j, matrix120 j ∈ Q) → Q = ⊤) : BinaryModel 120 :=
  native120Realization.binaryModel hA

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252
