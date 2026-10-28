module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.Witnesses
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment

/-!
# Seventeen proper inclusions in the Held normalizer catalogue

The eight containments into row 0 follow from an invariant signature of the
common involution. The nine containments into rows 20 and 21 follow from
characteristic centralizer subgroups, finite signature reconstructions and
the separate row-12 calculation. Each containing normalizer also has a
checked Held element that does not normalize the original row. Combining
these facts proves all seventeen strict inclusions without additional premises.

The resulting family supplies the strict-inclusion input of
`excluded_of_strict_inclusions` in the separate catalogue assembly. That
application uses the representative's two-group certificate to establish
two-locality; exhaustive coverage and distinguished normalizer identities
remain separate inputs of the source assembly.

Source: the ATLAS degree-2058 action, GLS3 Table 5.3p, and Aschbacher–Smith
condition E on printed pp.3–4 and 481–482. The unchanged container table is
published in `ElementaryWords`; all calculations here use those actual rows.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Subgroup

/-- The reverse inclusions fail unconditionally for all seventeen rows. -/
public theorem container_normalizer_not_le (j : Fin 22)
    (hj : ∀ k : Fin 5, j ≠ distinguished k) :
    ¬ normalizer (ambient (container j) : Set He) ≤ normalizer (ambient j : Set He) := by
  obtain ⟨g, hgin, hgout⟩ := ProperInclusions.exists_separating_element j hj
  exact fun h => hgout (h hgin)

/-- Concrete separation supplies strictness from forward containments. -/
public theorem strict_inclusions_of_containments
    (hcontain : ∀ j : Fin 22, (∀ k : Fin 5, j ≠ distinguished k) →
      normalizer (ambient j : Set He) ≤ normalizer (ambient (container j) : Set He)) :
    ∀ j : Fin 22, (∀ k : Fin 5, j ≠ distinguished k) →
      normalizer (ambient j : Set He) < normalizer (ambient (container j) : Set He) := by
  intro j hj
  exact lt_of_le_not_ge (hcontain j hj) (container_normalizer_not_le j hj)

/-- Every nondistinguished row normalizer lies in its prescribed containing
normalizer, using the central and E64 containment families. -/
public theorem normalizer_le_container_normalizer (j : Fin 22)
    (hj : ∀ k : Fin 5, j ≠ distinguished k) :
    normalizer (ambient j : Set He) ≤ normalizer (ambient (container j) : Set He) := by
  by_cases hc : container j = 0
  · rw [hc]
    exact normalizer_le_normalizer_zero_of_container_eq_zero j hj hc
  · exact e64_normalizer_containments j hc

/-- All seventeen proper inclusions between the actual ambient normalizers.
Both containment and strictness are proved, with no group-order, simplicity,
graph, enumeration or distinguished-normalizer premise. -/
public theorem normalizer_strict_inclusions :
    ∀ j : Fin 22, (∀ k : Fin 5, j ≠ distinguished k) →
      normalizer (ambient j : Set He) < normalizer (ambient (container j) : Set He) :=
  strict_inclusions_of_containments normalizer_le_container_normalizer

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
