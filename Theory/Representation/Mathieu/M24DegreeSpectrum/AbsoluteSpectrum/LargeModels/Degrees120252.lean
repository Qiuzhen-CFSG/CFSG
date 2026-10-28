module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.BinaryModels
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Certificate
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Realization
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity

/-!
# The native degree-120 and degree-252 binary M24 construction

Conjugation on the native eleven-dimensional code's trace-zero endomorphisms
supplies the degree-120 action. An invariant subspace of the native sextet
permutation representation supplies the degree-252 action. Checked coordinate
comparisons identify both pairs of generator matrices. The independent full
matrix-algebra certificates then imply absolute irreducibility by scalar
extension and Jacobson density.

The assembly discharges all native-realization and density premises, giving
actual absolutely irreducible binary representations of the Witt-design M24.
No degree spectrum, completeness assertion or ATLAS irreducibility label is
used as a premise. The original conditional assembly remains available.

Sources: James, J. Algebra 27 (1973), 57–111; the candidate matrices
M24G1-f2r120B0 and M24G1-f2r252B0 in the ATLAS of Finite Group
Representations. The source application is Guralnick–Malle I, Proposition 5.1,
M24 paragraph (journal pp.366–367, manuscript p.17).
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
open Degrees120252

/-- Actual native actions and checked matrix density give the two required
models. Final assembly must discharge all four independent premises. -/
theorem models120252_of_realizations
    (r120 : NativeRealization 120 matrix120)
    (r252 : NativeRealization 252 matrix252)
    (h120 : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin 120) (Fin 120) (ZMod 2)),
      (∀ j, matrix120 j ∈ Q) → Q = ⊤)
    (h252 : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin 252) (Fin 252) (ZMod 2)),
      (∀ j, matrix252 j ∈ Q) → Q = ⊤) :
    Nonempty (BinaryModel 120) ∧ Nonempty (BinaryModel 252) :=
  ⟨⟨r120.binaryModel h120⟩, ⟨r252.binaryModel h252⟩⟩

/-- The native trace-zero adjoint and sextet constructions give absolutely
irreducible binary M24 modules of degrees 120 and 252. -/
theorem models120252 : Nonempty (BinaryModel 120) ∧ Nonempty (BinaryModel 252) :=
  models120252_of_realizations native120Realization native252 matrix120_full matrix252_full

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
