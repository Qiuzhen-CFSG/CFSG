module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreCandidates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.WordEvaluation
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.SpanIdentities.FiniteCertificates

/-!
# Literal word interfaces for the Held centralizer-index calculation

The listed word generators generate exactly the existing ambient rows and core
candidates, by the subgroup map and closure laws. Certified finite enumerations
can therefore be applied to these original subgroups without replacing their
carriers or assuming a centralizer or two-core identification.

Source: the unchanged ATLAS word definitions; GLS3 Table 5.3p and quasithin
condition E. The final bridge consumes both finite span containments.
-/

@[expose] public section

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.SpanCertificates
open Subgroup

def wordGenerator (ws : List (List ℤ)) (a : Fin ws.length) : He :=
  word (ws[a.val]?.getD [])
lemma wordGenerator_range (ws : List (List ℤ)) :
    Set.range (wordGenerator ws) = {x | ∃ w ∈ ws, (word w : He) = x} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨ws[a.val], List.getElem_mem a.isLt,
      by simp only [wordGenerator, List.getElem?_eq_getElem a.isLt, Option.getD_some]⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hw
    refine ⟨⟨i, hi⟩, ?_⟩
    simp only [wordGenerator, List.getElem?_eq_getElem hi, Option.getD_some, he]
lemma ambient_eq_word_closure (j : Fin 22) :
    ambient j = closure (Set.range (wordGenerator (generatorWords j))) := by
  rw [wordGenerator_range, ambient, entry, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨word w, ⟨w, hw, rfl⟩, rfl⟩
def spanWords (j : Fin 22) : List (List ℤ) :=
  generatorWords (container j) ++ coreSupplementWords j
lemma coreCandidate_eq_word_closure (j : Fin 22) :
    coreCandidate j = closure (Set.range (wordGenerator (spanWords j))) := by
  rw [coreCandidate, ambient_eq_word_closure, wordGenerator_range,
    wordGenerator_range, ← closure_union]
  congr 1
  ext x
  simp only [spanWords, List.mem_append, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨w, hw, he⟩ | ⟨w, hw, he⟩)
    · exact ⟨w, Or.inl hw, he⟩
    · exact ⟨w, Or.inr hw, he⟩
  · rintro ⟨w, hw | hw, he⟩
    · exact Or.inl ⟨w, hw, he⟩
    · exact Or.inr ⟨w, hw, he⟩
def wordPerm (ws : List (List ℤ)) (a : Fin ws.length) : Equiv.Perm (Fin 2058) :=
  fastWord (ws[a.val]?.getD [])
lemma wordPerm_eq (ws : List (List ℤ)) (a : Fin ws.length) :
    wordPerm ws a = representation (wordGenerator ws a) := fastWord_eq _
def productPerm (ws : List (List ℤ)) (w : List (Fin ws.length)) : Equiv.Perm (Fin 2058) :=
  (w.map (wordPerm ws)).prod
lemma productPerm_eq (ws : List (List ℤ)) (w : List (Fin ws.length)) :
    productPerm ws w = representation (eval (wordGenerator ws) w) := by
  simp only [productPerm, eval, map_list_prod, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro a _
  exact wordPerm_eq ws a

lemma core_span_of_enumeration {n : ℕ} (j : Fin 22)
    (d : Enumeration (wordGenerator (spanWords j)) n)
    (upper : ∀ i, n ≤ 2 * d.count i →
      d.element i ∈ closure (Set.range (wordGenerator (generatorWords (container j)))))
    (lower : ∀ a, ∃ w : List (Fin n), (∀ i ∈ w, n ≤ 2 * d.count i) ∧
      eval d.element w = wordGenerator (generatorWords (container j)) a) :
    indexTwoSpan (coreCandidate j) = (ambient (container j)).subgroupOf (coreCandidate j) := by
  rw [coreCandidate_eq_word_closure, ambient_eq_word_closure]
  exact d.span_eq _ upper lower
end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.SpanCertificates
