module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.BinaryModels
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.CoordinateDensity

/-!
# Native realization of a binary matrix pair

Native M₂₄ acts on columns by the transposes of the given ATLAS row matrices.
A separately proved full-matrix-algebra certificate gives absolute irreducibility.
Keeping the carrier realization independent of density permits separate proofs
without importing the two-degree assembly.

Source application: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
namespace Degrees12421792
open Sporadic.Mathieu MatrixDensity

/-- A realization on the actual Witt-design carrier. ATLAS matrices act on rows;
the matrices of the native linear maps act on columns and hence are transposed.
Neither irreducibility nor a presentation assumption is included. -/
structure NativeRealization {d : ℕ} (A B : Matrix (Fin d) (Fin d) (ZMod 2)) where
  representation : Representation (ZMod 2) M24 (Fin d → ZMod 2)
  first : LinearMap.toMatrix' (representation ⟨m24GeneratorA, m24GeneratorA_mem⟩) = A.transpose
  second : LinearMap.toMatrix' (representation ⟨m24GeneratorB, m24GeneratorB_mem⟩) = B.transpose

/-- Combine native carrier identification and a separate finite density proof. -/
def NativeRealization.toBinaryModel {d : ℕ} [NeZero d]
    {A B : Matrix (Fin d) (Fin d) (ZMod 2)}
    (r : NativeRealization A B) (h : DensePair A B) : BinaryModel d where
  representation := r.representation
  absolute := absolutelyIrreducible_of_coordinate_matrices r.representation
    (LinearEquiv.refl (ZMod 2) (Fin d → ZMod 2))
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ ⟨m24GeneratorB, m24GeneratorB_mem⟩
    A.transpose B.transpose r.first r.second h.transpose

end Degrees12421792
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
