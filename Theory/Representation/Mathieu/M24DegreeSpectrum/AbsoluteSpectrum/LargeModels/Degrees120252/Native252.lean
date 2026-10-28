module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Transport
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.LinearAlgebra

/-!
# Degree-252 native realization: assembly of sextet certificates

The native standard pair generates the actual Witt-design M24. The invariant
image construction below turns the finite geometric and covector identities
into the specified representation, and then into a binary model when matrix
density is supplied independently. The identities remain construction
obligations; this module does not yet assert unconditional realization.

The finite obligations are owned by the geometry and matrix certificate
prerequisites. This assembly retains their final discharge, while the parent
`Degrees120252` assembly owns density and absolute-model construction.
Sources: James, J. Algebra 27 (1973), 57–111; GM02, Proposition 5.1.
-/

public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252
open scoped Pointwise

/-- A checked native sextet comparison and the packed linear certificates
supply the actual representation needed by the parent assembly. -/
def native252OfCertificates
    (hp : Function.Injective Native252.pointParts)
    (hm : ∀ j i, actor j • Native252.pointParts i = Native252.pointParts (Native252.forward j i))
    (hE : Function.Injective Native252.embedding)
    (hEA : ∀ j i k, (Native252.embeddingMatrix * matrix252 j) (Native252.forward j i) k =
      Native252.embeddingMatrix i k) : NativeRealization 252 matrix252 :=
  Native252.transportRealization hp hm hE hEA

open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks

/-- The literal selected inverse and packed row checks discharge the two
linear-algebra premises of the native realization construction. -/
def native252OfPackedCertificates
    (hp : Function.Injective Native252.pointParts)
    (hm : ∀ j i, actor j • Native252.pointParts i = Native252.pointParts (Native252.forward j i))
    (hs : ∀ i k, Native252.embeddingMatrix (Native252.selectedIndex i) k =
      Native252.selectedMatrix i k)
    (hi : Native252.inverseMatrix * Native252.selectedMatrix = 1)
    (hlen : ∀ j, (rows252 j).length = 252)
    (hrows : ∀ j i, combineList (rows252 j)
      (entry Native252.covectorRows (Native252.forward j i).val) =
        entry Native252.covectorRows i.val) : NativeRealization 252 matrix252 :=
  native252OfCertificates hp hm (Native252.embedding_injective_of_inverse hs hi)
    (Native252.intertwining_of_rows hlen hrows)

/-- Matrix density remains the independent parent's premise. -/
def binaryModel252OfCertificates
    (hp : Function.Injective Native252.pointParts)
    (hm : ∀ j i, actor j • Native252.pointParts i = Native252.pointParts (Native252.forward j i))
    (hE : Function.Injective Native252.embedding)
    (hEA : ∀ j i k, (Native252.embeddingMatrix * matrix252 j) (Native252.forward j i) k =
      Native252.embeddingMatrix i k)
    (hA : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin 252) (Fin 252) (ZMod 2)),
      (∀ j, matrix252 j ∈ Q) → Q = ⊤) : BinaryModel 252 :=
  (native252OfCertificates hp hm hE hEA).binaryModel hA

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252
