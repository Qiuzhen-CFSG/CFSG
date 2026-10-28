module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.CatalogueCoverage.FiniteChecks.Checks

/-!
# Elementary extension and conjugacy certificates

These four certificates discharge the concrete finite premises of
`standardCatalogue_cover_of_extensions`. The final comparison with actual
actors remains with that theorem’s assembly owner. The last theorem applies
the abstract extension argument to arbitrary finite elementary code sets.

Source: Guralnick–Malle, Classification of 2F-modules II, Lemma 4.5 and Proposition 4.8 step 3A; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds

/-- Row zero is precisely the identity row. -/
theorem elementaryRows_zero : elementaryRows 0 = {0} := by decide +kernel

/-- Every candidate row contains the identity. -/
theorem zero_mem_elementaryRows : ∀ i, 0 ∈ elementaryRows i := by decide +kernel

/-- Adjoining any commuting square-zero code gives another listed row,
including the extension by the identity code. -/
theorem elementaryRows_extend : ∀ i c, CoverageCode.mul c c = 0 →
    (∀ a ∈ elementaryRows i, CoverageCode.mul c a = CoverageCode.mul a c) →
    ∃ j, elementaryRows j = elementaryRows i ∪ (elementaryRows i).image (CoverageCode.mul c) := by
  intro i c hc hcomm
  exact ⟨FiniteChecks.nextRow i c, (FiniteChecks.all_checked i).1 c
    ((FiniteChecks.mem_involutions_iff c).mpr hc) hcomm⟩

/-- Every nonidentity row is conjugate to the ordered products of an unchanged
catalogue generator list. Conjugation is `g * a * inv g`. -/
theorem elementaryRows_conjugate : ∀ i, elementaryRows i ≠ {0} →
    ∃ (j : Fin 60) (g : Code), (elementaryRows i).image (CoverageCode.conj g) =
      CoverageCode.products 0 CoverageCode.mul (catalogueGenerators j) := by
  intro i hi
  exact ⟨(FiniteChecks.conjugateWitness i).1, (FiniteChecks.conjugateWitness i).2,
    (FiniteChecks.all_checked i).2 hi⟩

/-- Consumer of the extension certificates: every finite elementary,
multiplication-closed code set is one of the listed rows. -/
theorem elementaryRows_complete (T : Finset Code) (hz : 0 ∈ T)
    (hclosed : ∀ x ∈ T, ∀ y ∈ T, CoverageCode.mul x y ∈ T)
    (hsq : ∀ x ∈ T, CoverageCode.mul x x = 0)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, CoverageCode.mul x y = CoverageCode.mul y x) :
    ∃ i, elementaryRows i = T :=
  CoverageCode.exists_row_of_extensions 0 CoverageCode.mul elementaryRows 0
    elementaryRows_zero zero_mem_elementaryRows CoverageCode.mul_zero
    elementaryRows_extend T hz hclosed hsq hcomm

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
