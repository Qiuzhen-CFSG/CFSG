module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Generators
public import Theory.GroupTheory.PGroup.GeneratorSeries

/-!
# Generator certificates for the distinguished Held normalizers

The six slots below enumerate each distinguished elementary row, padding shorter
rows with the identity. The two candidate generators are conjugated using the
unchanged published conjugator. `conjugateFactors` records proposed images as
products of row generators; the companion check modules prove these identities
on the certified four-point base. This file alone asserts no normalizer equality.

Source: the literal ATLAS degree-2058 action and GLS3 Table 5.3p.
The discovery program is retained in `source/conjugation.g`; Lean checks its output.
-/

@[expose] public section

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities
open Subgroup LocalPairs.SylowGeometry.Calculations

/-- The published row words, padded to six slots by the empty word. -/
def rowWord (k : Fin 5) (j : Fin 6) : List ℤ :=
  ((generatorWords (distinguished k))[j.val]?).getD []

/-- Each slot evaluated in the actual ambient group. -/
def rowGenerator (k : Fin 5) (j : Fin 6) : He := word (rowWord k j)

/-- Products used as witnesses for generator conjugation. -/
def rowProduct (k : Fin 5) (w : List (Fin 6)) : He := (w.map (rowGenerator k)).prod

/-- The candidate's two literal generators, with the specified conjugation. -/
def mappedGenerator (k : Fin 5) (t : Fin 2) : He :=
  (MulAut.conj (conjugator k)) (Cores.localGenerator (candidate k) t : He)

/-- Indices of the row generators in each conjugate. -/
def conjugateFactors : Fin 5 → Fin 2 → Fin 6 → List (Fin 6)
  | 0, 0, 0 => [0]
  | 0, 1, 0 => [0]
  | 1, 0, 0 => [1, 2]
  | 1, 0, 1 => [0, 2, 3]
  | 1, 0, 2 => [0, 1, 2, 3]
  | 1, 0, 3 => [3]
  | 1, 1, 0 => [2]
  | 1, 1, 1 => [1, 2, 3]
  | 1, 1, 2 => [0, 2, 3]
  | 1, 1, 3 => [3]
  | 2, 0, 0 => [1, 2]
  | 2, 0, 1 => [0, 3]
  | 2, 0, 2 => [2, 3]
  | 2, 0, 3 => [3]
  | 2, 1, 0 => [0, 1, 3]
  | 2, 1, 1 => [2]
  | 2, 1, 2 => [1, 2, 3]
  | 2, 1, 3 => [3]
  | 3, 0, 0 => [0]
  | 3, 0, 1 => [0, 3, 4, 5]
  | 3, 0, 2 => [1, 3, 4]
  | 3, 0, 3 => [1, 4, 5]
  | 3, 0, 4 => [0, 1, 2, 3]
  | 3, 0, 5 => [1, 2, 3, 4, 5]
  | 3, 1, 0 => [0, 1, 2, 5]
  | 3, 1, 1 => [0, 1, 2, 3, 5]
  | 3, 1, 2 => [4]
  | 3, 1, 3 => [0, 1, 2, 4]
  | 3, 1, 4 => [0, 4, 5]
  | 3, 1, 5 => [1, 3]
  | 4, 0, 0 => [0]
  | 4, 0, 1 => [0, 1, 2, 4, 5]
  | 4, 0, 2 => [2]
  | 4, 0, 3 => [0, 3]
  | 4, 0, 4 => [2, 4]
  | 4, 0, 5 => [2, 5]
  | 4, 1, 0 => [0, 1, 2, 3]
  | 4, 1, 1 => [0, 1, 5]
  | 4, 1, 2 => [0, 1, 2]
  | 4, 1, 3 => [0, 1, 3, 4, 5]
  | 4, 1, 4 => [0, 1, 2, 4, 5]
  | 4, 1, 5 => [1, 4, 5]
  | _, _, _ => []

theorem rowGenerator_mem (k : Fin 5) (j : Fin 6) :
    rowGenerator k j ∈ ambient (distinguished k) := by
  have hm : ∀ k : Fin 5, ∀ j : Fin 6,
      rowWord k j = [] ∨ rowWord k j ∈ generatorWords (distinguished k) := by
    decide +kernel
  rcases hm k j with he | he
  · simp only [rowGenerator, he, word, List.map_nil, List.prod_nil, OneMemClass.coe_one]
    exact one_mem _
  · exact ⟨word (rowWord k j), word_mem_entry _ _ he, rfl⟩

theorem rowProduct_mem (k : Fin 5) (w : List (Fin 6)) :
    rowProduct k w ∈ ambient (distinguished k) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact rowGenerator_mem k j

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities
