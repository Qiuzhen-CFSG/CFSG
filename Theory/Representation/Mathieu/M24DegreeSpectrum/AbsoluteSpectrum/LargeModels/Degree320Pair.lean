module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.DensityApplication
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.TraceComparison
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.TraceCertificate

/-!
# Assembly of the binary degree-320 pair

The explicit ATLAS matrices must first be realized on the native Witt-design
M24. Full matrix-algebra generation then proves absolute irreducibility, and
the trace at one explicitly marked word proves inequivalence. This is the
degree-320 input for the James/GM02 larger-module exhaustion argument.

The assembly is conditional: native realization, finite density and trace
certificates remain to be supplied. In particular this file does not assert
the unconditional `pair320` theorem or use ATLAS labels as mathematical proofs.
-/

public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
open Degree320Pair

/-- Assemble the concrete construction obligations into the exact binary pair
consumed by `largeModelsExist_of_candidates`. Final discharge stays here. -/
theorem pair320_of_certificates (ha : ActionsExist) (hd : GeneratorDensity)
    (ht : TraceSeparation) : Nonempty (BinaryPair 320) := by
  obtain ⟨ρ, hρ⟩ := ha false
  obtain ⟨σ, hσ⟩ := ha true
  exact ⟨{
    first := ⟨ρ, absolute_of_realizes false ρ hρ (hd false)⟩
    second := ⟨σ, absolute_of_realizes true σ hσ (hd true)⟩
    inequivalent := inequivalent_of_realizes ht ρ σ hρ hσ }⟩

/-- A direct consumer of the finite row checker on the actual native models. -/
theorem pair320_of_rowChecks (ha : ActionsExist) (hd : GeneratorDensity)
    (hc : TraceRowChecks) : Nonempty (BinaryPair 320) :=
  pair320_of_certificates ha hd (traceSeparation_of_rowChecks hc)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
