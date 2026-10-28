module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.Elements
import Mathlib.Tactic.FinCases

/-!
# Ambient generation by the explicit local subgroups

Two short signed words in the local generators evaluate to the original
ATLAS pair a,b. The checked pair generates the actual carrier, so the literal
local centralizer and vertex normalizer generate it too. No simplicity or
order-based recognition is used. Source: Aschbacher, *Sporadic Groups*, 47.10,
p.266; the reproducible GAP word candidates are in `source/generation.json`.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
open Subgroup Theory.GroupTheory GeneratorPair

private def letters : Fin 10 → Carrier :=
  ![rotation, edgeExtra, x, y, inverter, rotation⁻¹, edgeExtra⁻¹, x⁻¹, y⁻¹, inverter⁻¹]

private def tables : Fin 10 → Equiv.Perm (Fin 100) :=
  ![EdgeData.table0, EdgeData.table1, LocalData.table0, LocalData.table1, LocalData.table2,
    EdgeData.table0⁻¹, EdgeData.table1⁻¹, LocalData.table0⁻¹, LocalData.table1⁻¹, LocalData.table2⁻¹]

private theorem letters_inclusion (i : Fin 10) : inclusion (letters i) = tables i := by
  fin_cases i
  · exact inclusion_rotation
  · exact inclusion_edgeExtra
  · exact inclusion_x
  · exact inclusion_y
  · exact inclusion_inverter
  · exact (map_inv inclusion rotation).trans (congrArg Inv.inv inclusion_rotation)
  · exact (map_inv inclusion edgeExtra).trans (congrArg Inv.inv inclusion_edgeExtra)
  · exact (map_inv inclusion x).trans (congrArg Inv.inv inclusion_x)
  · exact (map_inv inclusion y).trans (congrArg Inv.inv inclusion_y)
  · exact (map_inv inclusion inverter).trans (congrArg Inv.inv inclusion_inverter)

private def wordA : List (Fin 10) := [2, 0, 1, 5, 1, 0, 4, 6]

private def wordB : List (Fin 10) := [2, 9, 6, 9, 6, 0, 1, 5, 8, 4, 1, 3, 4, 8, 5, 8, 9, 8, 7, 5]

private theorem word_inclusion (w : List (Fin 10)) :
    inclusion (evalWord letters w) = evalWord tables w := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [evalWord, map_mul, ih, letters_inclusion, evalWord]

private theorem wordA_eq : evalWord letters wordA = a := by
  apply inclusion_injective
  rw [word_inclusion]
  change evalWord tables wordA = generatorA
  rw [generatorA_eq_table]
  decide +kernel

private theorem wordB_eq : evalWord letters wordB = b := by
  apply inclusion_injective
  rw [word_inclusion]
  change evalWord tables wordB = generatorB
  rw [generatorB_eq_table]
  decide +kernel

/-- The two explicit candidates already generate the whole ATLAS carrier. -/
theorem candidates_generate : edgeCandidate ⊔ localCandidate = ⊤ := by
  have hletters (i : Fin 10) : letters i ∈ edgeCandidate ⊔ localCandidate := by
    have hr : rotation ∈ edgeCandidate ⊔ localCandidate :=
      mem_sup_left (mem_sup_left (mem_zpowers rotation))
    have he : edgeExtra ∈ edgeCandidate ⊔ localCandidate :=
      mem_sup_left (mem_sup_right (mem_zpowers edgeExtra))
    have hx : x ∈ edgeCandidate ⊔ localCandidate :=
      mem_sup_right (mem_sup_left (mem_sup_left (mem_zpowers x)))
    have hy : y ∈ edgeCandidate ⊔ localCandidate :=
      mem_sup_right (mem_sup_left (mem_sup_right (mem_zpowers y)))
    have hs : inverter ∈ edgeCandidate ⊔ localCandidate :=
      mem_sup_right (mem_sup_right (mem_zpowers inverter))
    fin_cases i
    · exact hr
    · exact he
    · exact hx
    · exact hy
    · exact hs
    · exact (edgeCandidate ⊔ localCandidate).inv_mem hr
    · exact (edgeCandidate ⊔ localCandidate).inv_mem he
    · exact (edgeCandidate ⊔ localCandidate).inv_mem hx
    · exact (edgeCandidate ⊔ localCandidate).inv_mem hy
    · exact (edgeCandidate ⊔ localCandidate).inv_mem hs
  have hw (w : List (Fin 10)) : evalWord letters w ∈ edgeCandidate ⊔ localCandidate := by
    induction w with
    | nil => exact (edgeCandidate ⊔ localCandidate).one_mem
    | cons i w ih => exact (edgeCandidate ⊔ localCandidate).mul_mem (hletters i) ih
  apply top_unique
  rw [← closure_pair_eq_top]
  apply (closure_le _).mpr
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · exact wordA_eq ▸ hw wordA
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact wordB_eq ▸ hw wordB

/-- The ambient generation premise of `ConcreteSystem.ofCalculations`. -/
theorem K_sup_M : K ⊔ M = ⊤ := by
  apply top_unique
  rw [← candidates_generate]
  exact sup_le ((edgeCandidate_le_E.trans inf_le_left).trans le_sup_right)
    (localCandidate_le_K.trans le_sup_left)

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
