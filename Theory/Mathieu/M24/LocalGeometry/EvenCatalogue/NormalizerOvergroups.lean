module
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.OvergroupData
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups.TrioTranslations

/-!
# Geometric overgroups for all 22 native M₂₄ normalizers

Fifteen rows preserve the octad numbered 456, by point-orbit size or by its
unique repeated fixed-set property. Five more rows preserve the same actual
trio, whose stabilizer normalizes the zero-sum translation subgroup
`EvenCandidates.elementary 0`. The final two rows are literally the two
six-generator elementary candidates. Every containment concerns the full
normalizer in the native Witt-design automorphism group.

This is the adequate containment calculation used with source maximality;
no equality of smaller normalizers or maximal-subgroup classification is needed.
Source: GLS3 Table 5.3e; Aschbacher--Smith 15.3.41--42, printed p.1138.
-/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue
open NormalizerOvergroupsProof

private theorem row_cases : ∀ i : Fin 22,
    (∃ r : Fin 14, octadRow r = i) ∨ i = 17 ∨
      (∃ r : Fin 4, trioRow r = i) ∨ i = 19 ∨ i = 20 ∨ i = 21 := by
  decide +kernel

/-- Every listed full ambient normalizer lies in an actual octad stabilizer
or one of the two elementary candidate normalizers. -/
theorem normalizerOvergroups : NormalizerOvergroups := by
  intro i
  rcases row_cases i with ⟨r, rfl⟩ | rfl | ⟨r, rfl⟩ | rfl | rfl | rfl
  · exact Or.inl ⟨commonOctad, octadRow_le_octad r⟩
  · exact Or.inl ⟨commonOctad, row17_le_octad⟩
  · exact Or.inr ⟨0, (trioRow_le_trio r).trans trio_le_elementary_normalizer⟩
  · exact Or.inr ⟨0, row19_le_trio.trans trio_le_elementary_normalizer⟩
  · refine Or.inr ⟨0, ?_⟩
    change Subgroup.normalizer (ambient 20 : Set M24) ≤ _
    rw [show ambient 20 = EvenCandidates.elementary 0 from last_ambient 0]
    exact le_rfl
  · refine Or.inr ⟨1, ?_⟩
    change Subgroup.normalizer (ambient 21 : Set M24) ≤ _
    rw [show ambient 21 = EvenCandidates.elementary 1 from last_ambient 1]
    exact le_rfl

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue
