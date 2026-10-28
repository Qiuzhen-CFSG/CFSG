module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RowArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.TraceCertificate

/-!
# Applying the faster row checker to the literal trace comparison

The twenty skip-checker identities imply the twenty original product checks,
so they evaluate the same word `(A*B)^5*B`. The native consumer uses the exact
marked group elements of `TraceComparison`. All twenty finite checks remain
explicit premises until their certificates have been built; no untrusted
numerical output is used as a proof.

The original ATLAS data and action convention are in `../source/README.md`.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates

/-- The original twenty products, using the proved skip implementation. -/
def TraceSkipChecks : Prop :=
  (checkSkip Data.BaRows Data.BaRows Data.R2aRows = true ∧
    checkSkip Data.AaRows Data.R2aRows Data.R3aRows = true ∧
    checkSkip Data.BaRows Data.R3aRows Data.R4aRows = true ∧
    checkSkip Data.AaRows Data.R4aRows Data.R5aRows = true ∧
    checkSkip Data.BaRows Data.R5aRows Data.R6aRows = true ∧
    checkSkip Data.AaRows Data.R6aRows Data.R7aRows = true ∧
    checkSkip Data.BaRows Data.R7aRows Data.R8aRows = true ∧
    checkSkip Data.AaRows Data.R8aRows Data.R9aRows = true ∧
    checkSkip Data.BaRows Data.R9aRows Data.R10aRows = true ∧
    checkSkip Data.AaRows Data.R10aRows Data.R11aRows = true) ∧
  (checkSkip Data.BbRows Data.BbRows Data.R2bRows = true ∧
    checkSkip Data.AbRows Data.R2bRows Data.R3bRows = true ∧
    checkSkip Data.BbRows Data.R3bRows Data.R4bRows = true ∧
    checkSkip Data.AbRows Data.R4bRows Data.R5bRows = true ∧
    checkSkip Data.BbRows Data.R5bRows Data.R6bRows = true ∧
    checkSkip Data.AbRows Data.R6bRows Data.R7bRows = true ∧
    checkSkip Data.BbRows Data.R7bRows Data.R8bRows = true ∧
    checkSkip Data.AbRows Data.R8bRows Data.R9bRows = true ∧
    checkSkip Data.BbRows Data.R9bRows Data.R10bRows = true ∧
    checkSkip Data.AbRows Data.R10bRows Data.R11bRows = true)

theorem rowChecks_of_skipChecks (h : TraceSkipChecks) : TraceRowChecks := by
  obtain ⟨⟨h2a, h3a, h4a, h5a, h6a, h7a, h8a, h9a, h10a, h11a⟩, ⟨h2b, h3b, h4b, h5b, h6b, h7b, h8b, h9b, h10b, h11b⟩⟩ := h
  exact ⟨⟨checkRows_of_skip _ _ _ h2a,
      checkRows_of_skip _ _ _ h3a,
      checkRows_of_skip _ _ _ h4a,
      checkRows_of_skip _ _ _ h5a,
      checkRows_of_skip _ _ _ h6a,
      checkRows_of_skip _ _ _ h7a,
      checkRows_of_skip _ _ _ h8a,
      checkRows_of_skip _ _ _ h9a,
      checkRows_of_skip _ _ _ h10a,
      checkRows_of_skip _ _ _ h11a⟩,
    ⟨checkRows_of_skip _ _ _ h2b,
      checkRows_of_skip _ _ _ h3b,
      checkRows_of_skip _ _ _ h4b,
      checkRows_of_skip _ _ _ h5b,
      checkRows_of_skip _ _ _ h6b,
      checkRows_of_skip _ _ _ h7b,
      checkRows_of_skip _ _ _ h8b,
      checkRows_of_skip _ _ _ h9b,
      checkRows_of_skip _ _ _ h10b,
      checkRows_of_skip _ _ _ h11b⟩⟩

theorem traceSeparation_of_skipChecks (h : TraceSkipChecks) : TraceSeparation :=
  traceSeparation_of_rowChecks (rowChecks_of_skipChecks h)

/-- Actual native consumer of the twenty finite skip checks. -/
theorem inequivalent_of_skipChecks (h : TraceSkipChecks)
    (ρ σ : Representation (ZMod 2) Sporadic.Mathieu.M24 Space)
    (hρ : Realizes false ρ) (hσ : Realizes true σ) : IsEmpty (ρ.Equiv σ) :=
  inequivalent_of_realizes (traceSeparation_of_skipChecks h) ρ σ hρ hσ

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates
