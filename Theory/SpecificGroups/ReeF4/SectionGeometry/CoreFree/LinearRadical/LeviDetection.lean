module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.Levi
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.FirstLayer
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.FixedSpan
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.RootCentralizer

/-!
# Detecting full linear Ree Levi elements on the radical abelianization

The matrix quotient constructed in `FirstLayer` kills the actual radical
commutator subgroup. Consequently, trivial action on the radical abelianization
centralizes every matrix in the field span of its degree-one parts.

The fixed radical words in `FixedSpan` span every degree-one root operator
when `m ≥ 1`. The actual matrix calculation in `RootCentralizer` puts their
common centralizer in the full fixed Levi inside the fixed torus. Combining
these calculations proves detection with no further premises. The end-node
subsystem is {0,3}, and `fullLevi` retains the full complementary torus.
No identification of the matrix layer with the whole abelianization is used.

Source: GLS3, Theorem 2.6.5(e,g), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section

namespace ReeF4.SectionGeometry.LinearRadical

open Theory.AlgebraicGroup Parabolics LeviDetection

/-- Fixed-root spanning and the common-centralizer calculation together
give the required detection from the true radical abelianization. -/
theorem fullLevi_mem_fixedTorus_of_degreeOne_calculations (m : ℕ)
    (hspan : ∀ r : F4Chevalley.Root, rootDegree r = 1 →
      rootOperator m r ∈ radicalDegreeOneSpan m)
    (hdetect : ∀ l ∈ fullLevi m,
      (∀ r : F4Chevalley.Root, rootDegree r = 1 →
        Commute (modelMatrix m l) (rootOperator m r)) → l ∈ fixedTorus m)
    (l : Model m) (hl : l ∈ fullLevi m)
    (hact : ActsTriviallyOnRadicalAbelianization m l) : l ∈ fixedTorus m := by
  apply hdetect l hl
  intro r hr
  exact commute_of_mem_radicalDegreeOneSpan l hl hact _ (hspan r hr)

/-- An element of the full fixed linear Levi acting trivially on the actual
radical abelianization belongs to the fixed torus. -/
theorem fullLevi_mem_fixedTorus_of_trivial_radical_abelianization (m : ℕ) (hm : 1 ≤ m)
    (l : Model m) (hl : l ∈ fullLevi m)
    (hact : ActsTriviallyOnRadicalAbelianization m l) : l ∈ fixedTorus m :=
  fullLevi_mem_fixedTorus_of_degreeOne_calculations m
    (rootOperator_mem_radicalDegreeOneSpan m hm)
    (fullLevi_mem_fixedTorus_of_commute_rootOperators m hm) l hl hact

end ReeF4.SectionGeometry.LinearRadical
