module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Sections.Collection

/-!
# Exact coordinates and orders of the Ree root sections

Closed split-root collection followed by uniqueness of positive coordinates
forces the stated supports in the literal fixed matrix subgroup. Counting the
remaining free field scalars gives the six orders used in GLS3 Lemma 3.3.9.
This supplies every field of `SectionFacts`, without an elementary-rank or
root-calculation hypothesis.

Source: GLS3 2.4.5(d), 2.4.6 and Lemma 3.3.9, printed pp.134–135,
`refs/KGroup/GLS3/chapter2.tex` and `chapter3.tex`.
-/
public section
namespace ReeF4.ElementaryTwoBound.RootCalculations

/-- All section-coordinate and order inputs for the source counting argument. -/
theorem sectionFacts (m : ℕ) (_hm : 1 ≤ m) : SectionFacts m where
  support_D := Sections.factorization_of_splitCollection m (Sections.splitCollection m) .d
  support_D₁ := Sections.factorization_of_splitCollection m (Sections.splitCollection m) .d1
  support_D₂ := Sections.factorization_of_splitCollection m (Sections.splitCollection m) .d2
  card_D := Sections.card_section m .d
    (Sections.factorization_of_splitCollection m (Sections.splitCollection m) .d)
  card_D₁ := Sections.card_section m .d1
    (Sections.factorization_of_splitCollection m (Sections.splitCollection m) .d1)
  card_D₂ := Sections.card_section m .d2
    (Sections.factorization_of_splitCollection m (Sections.splitCollection m) .d2)
  card_T₁ := Sections.card_section m .t1
    (Sections.factorization_of_splitCollection m (Sections.splitCollection m) .t1)
  card_T₂ := Sections.card_section m .t2
    (Sections.factorization_of_splitCollection m (Sections.splitCollection m) .t2)
  card_K := Sections.card_section m .k
    (Sections.factorization_of_splitCollection m (Sections.splitCollection m) .k)

end ReeF4.ElementaryTwoBound.RootCalculations
