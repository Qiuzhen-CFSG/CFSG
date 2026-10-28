module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Reduction
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.Collection

/-!
# Order-seven coverage from the fixed coordinate certificates

A multiplicative realization of the 343-element coordinate group, together
with noncommuting images of its two generators, gives an actual subgroup of
order 343. Conjugate-power certificates for its nonidentity normal forms then
give `LocalPrimeCoverage 7 3`. The matrix multiplication and fusion premises
remain explicit until their concrete certificates are supplied.

The normal forms are fixed in `Seven/Setup.lean`; the target representatives
are the ATLAS words in `ProjectiveSimplicity/Words.lean`.
-/

namespace ONan.Simplicity

/-- Assemble the seven-local certificate from independently checkable matrix
realization and conjugate-power identities. -/
public theorem localPrimeCoverage_seven_of_coordinates
    (hmul : ∀ s t, Seven.evaluate (s * t) = Seven.evaluate s * Seven.evaluate t)
    (hne : Seven.generatorX * Seven.generatorY ≠ Seven.generatorY * Seven.generatorX)
    (hcoverage : ∀ t : Seven.Coordinates, t ≠ 1 →
      ∃ i k g, primeRepresentative i = g * Seven.evaluate t ^ k * g⁻¹) :
    LocalPrimeCoverage 7 3 := by
  refine ⟨(Seven.coordinateHom hmul).range, Seven.coordinateHom_range_card hmul hne, ?_⟩
  intro y hy
  obtain ⟨t, ht⟩ := y.property
  have hval : Seven.evaluate t = (y : Model) := ht
  have htne : t ≠ 1 := by
    intro h
    have hyone : y = 1 := Subtype.ext (by simpa [h, Seven.evaluate_one] using hval.symm)
    simp [hyone] at hy
  obtain ⟨i, k, g, hg⟩ := hcoverage t htne
  exact ⟨i, k, g, by simpa only [hval] using hg⟩

end ONan.Simplicity
