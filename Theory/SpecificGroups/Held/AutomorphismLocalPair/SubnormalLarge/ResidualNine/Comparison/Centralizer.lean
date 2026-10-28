module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.Definitions
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.LiteralLocal.Centralizer
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Row12.UpperBound
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The centralizer controlling the full Held seed normalizer

The four generators of catalogue row 12 commute with all twelve seed generators.
Their sixteen products realize every possible image of vertex zero under a seed
centralizer. Cancelling such a product fixes zero, and the established faithful
centralizer action forces identity. Thus the full seed normalizer normalizes
row 12, whose normalizer has order at most 9216.

Source: the ATLAS degree-2058 action, GLS3 Table 5.3p (automorphism-fused E64
classes), and Aschbacher--Smith, printed p.526.
-/

public section
namespace Held.AutomorphismLocalPair.ResidualNine.Comparison
open Subgroup LiteralLocal Held.NormalizerGraph
open TwoLocalCandidates.MaximalNormalizerCatalogue
open TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions
open TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Row12

private def centerGen (i : Fin 4) : He := rowElement 12 i.val
private def centerPerm (i : Fin 4) : Equiv.Perm Vertex :=
  tableWord ((generatorWords 12)[i.val]?.getD [])

private theorem centerPerm_eq (i : Fin 4) :
    centerPerm i = representation (centerGen i) := tableWord_eq _

set_option maxRecDepth 16384 in
private theorem center_commutes_check : ∀ i : Fin 4, ∀ j : Fin 12, ∀ v : Fin 4,
    (seedPerm j * centerPerm i) ⟨v.val, by omega⟩ =
      (centerPerm i * seedPerm j) ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem centerGen_mem_centralizer (i : Fin 4) :
    centerGen i ∈ centralizer (representativeLargeSeed : Set He) := by
  apply (mem_centralizer_iff_generators _).mpr
  intro j
  apply eq_of_four_point_images
  simpa only [map_mul, ← seedPerm_eq, ← centerPerm_eq] using center_commutes_check i j

private theorem row12_le_centralizer :
    ambient 12 ≤ centralizer (representativeLargeSeed : Set He) := by
  apply (ambient_le_iff _ _).mpr
  intro w hw
  change w ∈ [[-4, -1, -2, -4, -2, -1],
    [-3, -4, 2, 1, 2, -4, -2, -1, -3, -2],
    [-4, 2, 1, 2, -4, -2, -1, -2], [-3, 2, 1, 2, 3, -2, -1, -2]] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact centerGen_mem_centralizer 0
  · exact centerGen_mem_centralizer 1
  · exact centerGen_mem_centralizer 2
  · exact centerGen_mem_centralizer 3

private def test0 (x : Vertex) : Prop :=
  seedPerm 0 x = x ∧ seedPerm 5 x = seedPerm 4 x ∧
    ¬ Adj x (seedPerm 8 x) ∧ Adj x (seedPerm 6 x)
private instance (x : Vertex) : Decidable (test0 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

private def image0 : Fin 16 → Vertex
  | 0 => 0
  | 1 => 1514
  | 2 => 355
  | 3 => 1044
  | 4 => 581
  | 5 => 1796
  | 6 => 374
  | 7 => 66
  | 8 => 1395
  | 9 => 125
  | 10 => 919
  | 11 => 1112
  | 12 => 1455
  | 13 => 1631
  | 14 => 219
  | _ => 49

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem candidates0 : ∀ x : Vertex, test0 x → ∃ n : Fin 16, image0 n = x := by
  apply TwoLocalCandidates.Cores.allLetters
  decide +kernel

private theorem test0_zero : test0 0 := by decide +kernel

private theorem image_zero (σ : Equiv.Perm Vertex) (hc : CommutesGenerators σ)
    (hg : σ ∈ preservingGroup) : ∃ n : Fin 16, image0 n = σ 0 := by
  apply candidates0
  have h := test0_zero
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hc 0, h.1]
  · rw [← hc 5, ← hc 4, h.2.1]
  · rw [← hc 8]
    exact (hg _ _).not.mpr h.2.2.1
  · rw [← hc 6]
    exact (hg _ _).mpr h.2.2.2


private def maskIndices (n : Fin 16) : List (Fin 4) :=
  (List.finRange 4).filter (fun i => n.val.testBit i.val)
private def witness (n : Fin 16) : He := ((maskIndices n).map centerGen).prod
private def witnessPerm (n : Fin 16) : Equiv.Perm Vertex :=
  ((maskIndices n).map centerPerm).prod

private theorem witnessPerm_eq (n : Fin 16) : witnessPerm n = representation (witness n) := by
  simp only [witnessPerm, witness, map_list_prod, List.map_map, Function.comp_def]
  congr 1
  exact List.map_congr_left (fun i _ => centerPerm_eq i)

private theorem witness_mem (n : Fin 16) : witness n ∈ ambient 12 := by
  apply list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact rowElement_mem _ _

set_option maxRecDepth 16384 in
private theorem witness_image_check : ∀ n : Fin 16, witnessPerm n 0 = image0 n := by
  decide +kernel

/-- The centralizer is the literal catalogue subgroup, with no order premise. -/
theorem seed_centralizer_eq_row12 :
    centralizer (representativeLargeSeed : Set He) = ambient 12 := by
  apply le_antisymm _ row12_le_centralizer
  intro x hx
  obtain ⟨n, hn⟩ := image_zero (representation x) (centralizer_commutes hx)
    (Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup x.property)
  have him : representation (witness n) 0 = representation x 0 := by
    rw [← witnessPerm_eq, witness_image_check, hn]
  have hc : (witness n)⁻¹ * x ∈ centralizer (representativeLargeSeed : Set He) :=
    mul_mem (inv_mem (row12_le_centralizer (witness_mem n))) hx
  have hid : (witness n)⁻¹ * x = 1 := centralizer_fix_zero hc (by
    change (representation (witness n)).symm (representation x 0) = 0
    rw [← him]
    exact Equiv.symm_apply_apply _ _)
  rw [← inv_mul_eq_one.mp hid]
  exact witness_mem n

/-- The full normalizer, rather than an exhibited subgroup, has this bound. -/
theorem representativeLargeLocal_card_le : Nat.card representativeLargeLocal ≤ 9216 := by
  apply (card_le_of_le (show representativeLargeLocal ≤ normalizer (ambient 12 : Set He) from ?_)).trans
    normalizer_card_le
  rw [← seed_centralizer_eq_row12]
  exact normalizer_le_normalizer_centralizer representativeLargeSeed

end Held.AutomorphismLocalPair.ResidualNine.Comparison
