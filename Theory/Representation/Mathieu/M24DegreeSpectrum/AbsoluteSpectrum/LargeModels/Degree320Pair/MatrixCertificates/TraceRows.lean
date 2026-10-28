module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product02A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product03A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product04A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product05A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product06A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product07A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product08A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product09A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product10A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product11A
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product02B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product03B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product04B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product05B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product06B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product07B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product08B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product09B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product10B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceRows.Product11B
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.TraceReduction

/-!
# The twenty literal products for the degree-320 trace test

The sparse certificates discharge every product in `TraceRowChecks` for both
published matrix pairs. The native application compares the characters at
`(actorA * actorB)^5 * actorB`, using exactly the original marking equations.
It requires neither density nor orbit spanning. Representation construction
remains with the action owner; only the existing `Realizes` hypotheses are used.

The row-sum proof and reproducibility measurements are in `TraceRows/source/README.md`.
Original ATLAS attribution and action conventions are in `../source/README.md`.
-/

public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates

/-- All twenty original row-product identities, with no certificate premises. -/
theorem traceRowChecks : TraceRowChecks :=
  ⟨⟨TraceRows.r2a,
      TraceRows.r3a,
      TraceRows.r4a,
      TraceRows.r5a,
      TraceRows.r6a,
      TraceRows.r7a,
      TraceRows.r8a,
      TraceRows.r9a,
      TraceRows.r10a,
      TraceRows.r11a⟩,
    ⟨TraceRows.r2b,
      TraceRows.r3b,
      TraceRows.r4b,
      TraceRows.r5b,
      TraceRows.r6b,
      TraceRows.r7b,
      TraceRows.r8b,
      TraceRows.r9b,
      TraceRows.r10b,
      TraceRows.r11b⟩⟩

/-- Native representations with the two literal markings are inequivalent. -/
theorem inequivalent_of_traceRows
    (ρ σ : Representation (ZMod 2) Sporadic.Mathieu.M24 Space)
    (hρ : Realizes false ρ) (hσ : Realizes true σ) : IsEmpty (ρ.Equiv σ) :=
  inequivalent_of_realizes (traceSeparation_of_rowChecks traceRowChecks) ρ σ hρ hσ

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates
