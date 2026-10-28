module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.CheckPart0
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.CheckPart1
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.CheckPart2
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.CheckPart3
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.CheckPart4

/-!
# The concrete Held group preserves the published graph

The kernel certificates establish the action of both bit-routing circuits
and their effect on every row. Circuit soundness gives adjacency preservation
by the two actual ATLAS generators. Closure then gives preservation by the
whole concrete Held carrier, with no graph-containment premise.

Source: ATLAS HeG1-p2058B0 and the relation in `Normalizer/GraphData.lean`.
-/

namespace Held.Realization.MarkedConjugacy.Seventeen
open Held.NormalizerGraph Rudvalis.OuterNormalizer.InvarianceCertificate

private theorem block_checks (b : Fin 33) : checkBlock facts b.val = true := by
  by_cases h0 : b.val < 8
  · have h := checkPart0 ⟨b.val - 0, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 0 ≤ b.val)] using h
  by_cases h1 : b.val < 16
  · have h := checkPart1 ⟨b.val - 8, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 8 ≤ b.val)] using h
  by_cases h2 : b.val < 24
  · have h := checkPart2 ⟨b.val - 16, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 16 ≤ b.val)] using h
  by_cases h3 : b.val < 32
  · have h := checkPart3 ⟨b.val - 24, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 24 ≤ b.val)] using h
  have h := checkPart4 ⟨b.val - 32, by have := b.isLt; omega⟩
  simpa only [Nat.add_sub_of_le (by omega : 32 ≤ b.val)] using h

private theorem allFacts (x : Fin 2058) : facts x := allFinBlocks facts block_checks x

public theorem atlasA_mem_preservingGroup : atlasA ∈ preservingGroup := by
  intro x y
  change (rowMask (atlasA x)).testBit (atlasA y).val = true ↔
    (rowMask x).testBit y.val = true
  rw [← sound aCircuit y.val (atlasA y).val (rowMask (atlasA x)) (allFacts y).1,
    (allFacts x).2.2.1]

public theorem atlasB_mem_preservingGroup : atlasB ∈ preservingGroup := by
  intro x y
  change (rowMask (atlasB x)).testBit (atlasB y).val = true ↔
    (rowMask x).testBit y.val = true
  rw [← sound bCircuit y.val (atlasB y).val (rowMask (atlasB x)) (allFacts y).2.1,
    (allFacts x).2.2.2]

/-- Containment follows from the checked actions of both defining generators. -/
public theorem permutationGroup_le_preservingGroup : permutationGroup ≤ preservingGroup := by
  rw [permutationGroup, Subgroup.closure_le]
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · exact atlasA_mem_preservingGroup
  · exact Set.mem_singleton_iff.mp hg ▸ atlasB_mem_preservingGroup

end Held.Realization.MarkedConjugacy.Seventeen
