module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord

/-!
# Literal candidates for three Held centralizer two-cores

Adjoin the displayed words to the prescribed E64 row. These definitions retain
the actual embedding into Held. Identification with the two-core of the full
ambient centralizer is a separate obligation; the definitions assert no order,
normality, or completeness of a finite list.

Source: the ATLAS Held words and the reproducible diagnostic in
`source/discover.py`; GLS3 Table 5.3p gives the surrounding
involution-centralizer context. GAP output is discovery evidence only.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
open Subgroup LocalPairs.SylowGeometry.Calculations

/-- Extra signed words for rows 1, 3, and 5, in the fixed four generators. -/
@[expose] public def coreSupplementWords : Fin 22 → List (List ℤ)
  | 1 => [[-3], [-3, -4, -1, 2, 1, 2, -4, -2, -1, -3, -2, -2, -1, -2]]
  | 3 => [[4, -3, -4, -1, 2, 1, 2, -4, -2, -1, -3, -2], [4, -4, 2, 1, 2, 4]]
  | 5 => [[4]]
  | _ => []

/-- A concrete subgroup; its two-core identification is not part of the definition. -/
@[expose] public def coreCandidate (j : Fin 22) : Subgroup He :=
  ambient (container j) ⊔ closure {x | ∃ w ∈ coreSupplementWords j, (word w : He) = x}

public theorem ambient_container_le_coreCandidate (j : Fin 22) :
    ambient (container j) ≤ coreCandidate j := le_sup_left

public theorem coreCandidate_le_representative (j : Fin 22) :
    coreCandidate j ≤ representative := by
  apply sup_le (ambient_le_representative _) ((closure_le _).mpr ?_)
  rintro _ ⟨w, _, rfl⟩
  exact (word w).property

/-- The common involution is an actual element of every ambient row. -/
public theorem centralWord_mem_ambient (j : Fin 22) : centralWord ∈ ambient j := by
  have h : ∀ k : Fin 22, commonWord ∈ generatorWords k := by decide +kernel
  change (word commonWord : He) ∈ (entry j).map representative.subtype
  exact Subgroup.mem_map.mpr ⟨word commonWord, word_mem_entry j commonWord (h j), rfl⟩

/-- Every centralizer under consideration lies in the common involution centralizer. -/
public theorem ambient_centralizer_le_common (j : Fin 22) :
    centralizer (ambient j : Set He) ≤ centralizer ({centralWord} : Set He) :=
  centralizer_le (Set.singleton_subset_iff.mpr (centralWord_mem_ambient j))

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
