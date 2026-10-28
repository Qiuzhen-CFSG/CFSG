module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Signatures
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Characteristic
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Reconstructions
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Row12

/-!
# The nine Held normalizer containments into E64 rows

Rows 1, 3 and 5 reduce to characteristic subgroups of their ambient centralizers.
Fixed-point signatures reduce rows 8, 10 and 16 to rows 3, 1 and 3, respectively.
Translation-overlap signatures reduce rows 18 and 19 to rows 5 and 3. Row 12
requires a separate argument choosing the prescribed E64 subgroup.

The final theorem discharges the conditional reduction using the three concrete
characteristic-centralizer certificates, five finite reconstruction identities,
and the separate row-12 containment. It proves the nine containments for arbitrary
elements of the actual normalizers, without simplicity, graph or order premises.
The remaining catalogue branches and source condition E belong to the parent
assembly.

Sources: GLS3 Table 5.3p; Aschbacher–Smith condition E, printed pp.3–4 and
481–482; the unchanged ATLAS catalogue words in `ElementaryWords`.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Subgroup E64Containment

/-- Assemble the E64 branch from three characteristic-centralizer calculations,
five finite signature reconstructions, and the separate row-12 argument. -/
public theorem e64_containments_of_reconstruction
    (hchar : ∀ j : Fin 22, j = 1 ∨ j = 3 ∨ j = 5 →
      ambient (container j) ≤ centralizer (ambient j : Set He) ∧
        ((ambient (container j)).subgroupOf (centralizer (ambient j : Set He))).Characteristic)
    (h8 : fixedPointSpan (ambient 8) 42 = ambient 3)
    (h10 : fixedPointSpan (ambient 10) 42 = ambient 1)
    (h16 : fixedPointSpan (ambient 16) 42 = ambient 3)
    (h18 : overlapSpan (ambient 18) 0 = ambient 5)
    (h19 : overlapSpan (ambient 19) 6 = ambient 3)
    (h12 : normalizer (ambient 12 : Set He) ≤ normalizer (ambient 20 : Set He)) :
    ∀ j : Fin 22, container j ≠ 0 →
      normalizer (ambient j : Set He) ≤ normalizer (ambient (container j) : Set He) := by
  have hbase (j : Fin 22) (hj : j = 1 ∨ j = 3 ∨ j = 5) :
      normalizer (ambient j : Set He) ≤ normalizer (ambient (container j) : Set He) :=
    normalizer_le_of_characteristic_centralizer _ _ (hchar j hj).1 (hchar j hj).2
  have hfirst := hbase 1 (Or.inl rfl)
  have hthird := hbase 3 (Or.inr (Or.inl rfl))
  have hfifth := hbase 5 (Or.inr (Or.inr rfl))
  intro j hj
  have hcases : j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 8 ∨ j = 10 ∨ j = 12 ∨
      j = 16 ∨ j = 18 ∨ j = 19 := by
    have hall : ∀ k : Fin 22, container k ≠ 0 →
        k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 8 ∨ k = 10 ∨ k = 12 ∨
          k = 16 ∨ k = 18 ∨ k = 19 := by decide +kernel
    exact hall j hj
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hfirst
  · exact hthird
  · exact hfifth
  · exact (h8 ▸ normalizer_le_fixedPointSpan (ambient 8) 42).trans hthird
  · exact (h10 ▸ normalizer_le_fixedPointSpan (ambient 10) 42).trans hfirst
  · exact h12
  · exact (h16 ▸ normalizer_le_fixedPointSpan (ambient 16) 42).trans hthird
  · exact (h18 ▸ normalizer_le_overlapSpan (ambient 18) 0).trans hfifth
  · exact (h19 ▸ normalizer_le_overlapSpan (ambient 19) 6).trans hthird

/-- All nine normalizer containments into the prescribed E64 rows, with every
concrete premise of the reconstruction argument discharged. -/
public theorem e64_normalizer_containments :
    ∀ j : Fin 22, container j ≠ 0 →
      normalizer (ambient j : Set He) ≤ normalizer (ambient (container j) : Set He) :=
  e64_containments_of_reconstruction e64_centralizer_certificates
    fixedPointSpan_ambient8_eq_ambient3 fixedPointSpan_ambient10_eq_ambient1
    fixedPointSpan_ambient16_eq_ambient3 overlapSpan_ambient18_eq_ambient5
    overlapSpan_ambient19_eq_ambient3 normalizer_row12_le_normalizer_row20

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
