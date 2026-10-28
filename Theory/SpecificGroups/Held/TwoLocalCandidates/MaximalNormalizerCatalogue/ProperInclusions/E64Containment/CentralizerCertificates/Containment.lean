module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.WordEvaluation
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreCandidates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.WordTests

/-!
# Containment in the three actual Held centralizers

Check commutation of the literal generating words on Held's certified four-point
base, using the previously certified fast tables. Subgroup closure then proves
containment of the whole core candidate, and hence of its prescribed E64 row,
in the full ambient centralizer. These are actual subgroup containments; no
normality, centralizer order, or exhaustive enumeration is assumed.

Sources: ATLAS HeG1-p2058B0 and the unchanged catalogue words; GLS3 Table 5.3p.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
open Subgroup ProperInclusions

private def candidateWords (j : Fin 22) : List (List ℤ) :=
  generatorWords (container j) ++ coreSupplementWords j

private theorem index_of_mem {ws : List (List ℤ)} {w : List ℤ} (hw : w ∈ ws) :
    ∃ i : Fin ws.length, ws[i.val]?.getD [] = w := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hw
  exact ⟨⟨i, hi⟩, by simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using he⟩

private theorem word_mem_centralizer (j : Fin 22) (w : List ℤ)
    (h : ∀ i : Fin (generatorWords j).length,
      rowElement j i * (word w : He) = (word w : He) * rowElement j i) :
    (word w : He) ∈ centralizer (ambient j : Set He) := by
  have hc : ambient j ≤ centralizer ({(word w : He)} : Set He) := by
    apply (ambient_le_iff j _).mpr
    intro v hv
    obtain ⟨i, hi⟩ := index_of_mem hv
    apply mem_centralizer_singleton_iff.mpr
    simpa only [rowElement, hi] using h i
  intro x hx
  exact mem_centralizer_singleton_iff.mp (hc hx)

set_option maxRecDepth 4096 in
private theorem checks_one : ∀ i : Fin (candidateWords 1).length,
    ∀ k : Fin (generatorWords 1).length, ∀ t : Fin 4,
    (fastWord ((generatorWords 1)[k.val]?.getD []) *
      fastWord ((candidateWords 1)[i.val]?.getD [])) ⟨t.val, by omega⟩ =
    (fastWord ((candidateWords 1)[i.val]?.getD []) *
      fastWord ((generatorWords 1)[k.val]?.getD [])) ⟨t.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem checks_three : ∀ i : Fin (candidateWords 3).length,
    ∀ k : Fin (generatorWords 3).length, ∀ t : Fin 4,
    (fastWord ((generatorWords 3)[k.val]?.getD []) *
      fastWord ((candidateWords 3)[i.val]?.getD [])) ⟨t.val, by omega⟩ =
    (fastWord ((candidateWords 3)[i.val]?.getD []) *
      fastWord ((generatorWords 3)[k.val]?.getD [])) ⟨t.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem checks_five : ∀ i : Fin (candidateWords 5).length,
    ∀ k : Fin (generatorWords 5).length, ∀ t : Fin 4,
    (fastWord ((generatorWords 5)[k.val]?.getD []) *
      fastWord ((candidateWords 5)[i.val]?.getD [])) ⟨t.val, by omega⟩ =
    (fastWord ((candidateWords 5)[i.val]?.getD []) *
      fastWord ((generatorWords 5)[k.val]?.getD [])) ⟨t.val, by omega⟩ := by
  decide +kernel

private theorem candidateWord_commutes (j : Fin 22) (hj : j = 1 ∨ j = 3 ∨ j = 5)
    (w : List ℤ) (hw : w ∈ candidateWords j)
    (k : Fin (generatorWords j).length) :
    rowElement j k * (word w : He) = (word w : He) * rowElement j k := by
  obtain ⟨i, hi⟩ := index_of_mem hw
  apply Held.eq_of_four_point_images
  intro t
  rw [map_mul, map_mul]
  simp only [rowElement, ← fastWord_eq]
  rw [← hi]
  rcases hj with rfl | rfl | rfl
  · exact checks_one i k t
  · exact checks_three i k t
  · exact checks_five i k t

/-- The whole candidate centralizes the indicated literal row. -/
public theorem coreCandidate_le_centralizer (j : Fin 22)
    (hj : j = 1 ∨ j = 3 ∨ j = 5) :
    coreCandidate j ≤ centralizer (ambient j : Set He) := by
  apply sup_le
  · apply (ambient_le_iff _ _).mpr
    intro w hw
    exact word_mem_centralizer j w (candidateWord_commutes j hj w
      (List.mem_append_left _ hw))
  · apply (closure_le _).mpr
    rintro _ ⟨w, hw, rfl⟩
    exact word_mem_centralizer j w (candidateWord_commutes j hj w
      (List.mem_append_right _ hw))

/-- The containment clause of the requested three-row family. -/
public theorem ambient_container_le_centralizer (j : Fin 22)
    (hj : j = 1 ∨ j = 3 ∨ j = 5) :
    ambient (container j) ≤ centralizer (ambient j : Set He) :=
  (ambient_container_le_coreCandidate j).trans (coreCandidate_le_centralizer j hj)

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
