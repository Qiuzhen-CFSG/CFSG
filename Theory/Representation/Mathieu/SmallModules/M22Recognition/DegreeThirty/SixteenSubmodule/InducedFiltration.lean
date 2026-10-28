module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.Models
public import Theory.Representation.FactorDegreeFiltration
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.CosetModel
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.CertificateInterface
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.NativeFlag
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.SimpleFactors
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Transport

/-!
# A simple-factor filtration of the native adjoint induction

The native induced adjoint has a checked 22-coset realization of binary
dimension 352. Transporting a filtration of that realization preserves the
literal invariant subspaces, simplicity of their quotients, and quotient
dimensions. This is the final transport needed by `Induction`.

The checked native flag has eight simple factors of degrees
140, 1, 34, 1, 34, 1, 1, 140. The native matrix comparison and the binary
simplicity certificates discharge both inputs of the assembly. Thus the
literal induced representation has a finite simple-factor filtration in
which every quotient degree is at most 10 or greater than 30. All extension
blocks are retained; no semisimplicity assertion is used.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457.
-/

public section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule

/-- Transfer a checked coset filtration to the original, noninjective induction.
The actual central-kernel comparison is part of `inducedCosetEquiv`. -/
theorem induced_factorDegreeFiltration_of_coset {D : Set ℕ}
    (h : FactorDegreeFiltration (k := ZMod 2) (G := M22) (V := CosetAdjoint)
      D cosetAdjoint) :
    FactorDegreeFiltration (k := ZMod 2) (G := M22) (V := InducedAdjoint)
      D inducedAdjoint := by
  apply h.transport (MonoidHom.id M22) (fun x => ⟨x, rfl⟩)
    inducedAdjoint inducedCosetEquiv.symm.toLinearEquiv
  intro g v
  exact IntertwiningMap.isIntertwining _ _ inducedCosetEquiv.symm.toIntertwiningMap g v

/-- Assemble a native flag and its eight binary simplicity certificates for
the original central-cover induction. -/
theorem induced_factorDegreeFiltration_of_certificates
    (C : InducedFiltration.FlagCoordinates)
    (hs : ∀ t : InducedFiltration.Factor, InducedFiltration.FactorSimple t) :
    FactorDegreeFiltration {d : ℕ | d ≤ 10 ∨ 30 < d} inducedAdjoint := by
  apply (InducedFiltration.binary_factorDegreeFiltration_of_certificates C hs).transport
    (MonoidHom.id M22) (fun x => ⟨x, rfl⟩) inducedAdjoint
    GeneratorMatrices.inducedBinaryEquiv.symm.toLinearEquiv
  intro g v
  exact IntertwiningMap.isIntertwining _ _
    GeneratorMatrices.inducedBinaryEquiv.symm.toIntertwiningMap g v

/-- The checked native invariant flag has simple quotients with the required
degree bounds, in the explicit 22-by-16 binary coordinates. -/
theorem InducedFiltration.binary_factorDegreeFiltration :
    FactorDegreeFiltration {d : ℕ | d ≤ 10 ∨ 30 < d}
      GeneratorMatrices.binaryAdjoint :=
  InducedFiltration.binary_factorDegreeFiltration_of_certificates
    InducedFiltration.nativeFlag InducedFiltration.factorSimple

/-- The concrete induced adjoint has a finite simple-factor filtration with
every quotient degree at most ten or greater than thirty. -/
theorem induced_factorDegreeFiltration :
    FactorDegreeFiltration {d : ℕ | d ≤ 10 ∨ 30 < d} inducedAdjoint :=
  induced_factorDegreeFiltration_of_certificates
    InducedFiltration.nativeFlag InducedFiltration.factorSimple

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule
