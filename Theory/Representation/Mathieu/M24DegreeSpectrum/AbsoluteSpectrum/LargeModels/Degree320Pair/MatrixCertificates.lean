module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceReduction
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.ProjectionApplication
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.OrbitSpanning
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows

/-!
# Certified density and trace separation for the binary degree-320 pair

For each literal ATLAS matrix pair, a certified complementary inverse puts a
rank-one projection in the generated algebra. Its certified left and right
orbit bases then span every matrix, proving full matrix-algebra generation.
The twenty certified suffix products evaluate `(A*B)^5*B`; its two traces,
zero and one, distinguish the variants.

All finite-certificate premises are discharged here. The native applications
give absolute irreducibility and inequivalence for representations satisfying
the original marking equations. Construction of those actions remains with
the independent native-action owner and the final `pair320` assembly.

These are the auxiliary degree-320 models for the James/GM02 degree-window
argument. Source attribution and numerical conventions are recorded in
`Degree320Pair/source/README.md` and `MatrixCertificates/source/README.md`.
-/

public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair

/-- Both literal generator pairs generate the full binary matrix algebra. -/
theorem generatorDensity : GeneratorDensity :=
  generatorDensity_of_rankOne MatrixCertificates.rankOneMembership
    MatrixCertificates.orbitSpanning

/-- The literal word `(A*B)^5*B` has different traces for the two variants. -/
theorem traceSeparation : TraceSeparation :=
  traceSeparation_of_rowChecks MatrixCertificates.traceRowChecks

/-- The completed density certificate discharges the numerical premise of
`absolute_of_realizes` for either marked native action. -/
theorem absolute_of_certificates (variant : Bool)
    (ρ : Representation (ZMod 2) Sporadic.Mathieu.M24 Space)
    (hρ : Realizes variant ρ) : ρ.IsAbsolutelyIrreducible :=
  absolute_of_realizes variant ρ hρ (generatorDensity variant)

/-- The completed trace certificate discharges the numerical premise of
`inequivalent_of_realizes`, preserving the original native marking. -/
theorem inequivalent_of_certificates
    (ρ σ : Representation (ZMod 2) Sporadic.Mathieu.M24 Space)
    (hρ : Realizes false ρ) (hσ : Realizes true σ) : IsEmpty (ρ.Equiv σ) :=
  inequivalent_of_realizes traceSeparation ρ σ hρ hσ

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
