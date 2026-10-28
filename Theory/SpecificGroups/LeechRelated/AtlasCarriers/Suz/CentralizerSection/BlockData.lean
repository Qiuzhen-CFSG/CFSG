module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.Tables
public import Mathlib.Data.Finset.Image

/-!
# The explicit 27 pairs and their permutation group

These 27 pairs of letters are stable under the two certified centralizer words.
The quotient carrier is the closure of their exact induced permutations.
No identification with an orthogonal group is assumed in this module.
Source: fixed ATLAS SuzG1-p1782B0 permutations, as calculated and checked in
CentralizerSection/Certificates.lean and Action.lean.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Suz.CentralizerSection

/-- A labelled pair of letters of the original permutation representation. -/
def point (i : Fin 27) : Finset (Fin 1782) :=
  match i.val with
  | 0 => {2, 727}
  | 1 => {18, 256}
  | 2 => {33, 1559}
  | 3 => {154, 1719}
  | 4 => {185, 1765}
  | 5 => {209, 867}
  | 6 => {282, 1142}
  | 7 => {394, 920}
  | 8 => {442, 565}
  | 9 => {458, 523}
  | 10 => {461, 1169}
  | 11 => {468, 1315}
  | 12 => {478, 650}
  | 13 => {514, 1428}
  | 14 => {527, 1013}
  | 15 => {549, 1135}
  | 16 => {733, 900}
  | 17 => {741, 1732}
  | 18 => {770, 791}
  | 19 => {821, 862}
  | 20 => {890, 1770}
  | 21 => {896, 1681}
  | 22 => {988, 1167}
  | 23 => {999, 1425}
  | 24 => {1050, 1419}
  | 25 => {1150, 1663}
  | _ => {1166, 1463}

/-- The literal induced permutation on the 27 labelled pairs. -/
def blockC : Equiv.Perm (Fin 27) :=
  (([[0, 21, 26, 3, 4], [1, 7, 24, 9, 23], [2, 8, 5, 11, 16], [6, 17, 25, 12, 14], [10, 13, 20, 22, 15]] : List (List (Fin 27))).map List.formPerm).prod

/-- The literal induced permutation on the 27 labelled pairs. -/
def blockD : Equiv.Perm (Fin 27) :=
  (([[0, 14], [1, 15], [3, 8, 24, 16, 4, 20], [5, 22, 6, 11, 19, 25], [7, 18], [9, 10, 26, 13, 23, 12]] : List (List (Fin 27))).map List.formPerm).prod

/-- The concrete image to be identified with the canonical orthogonal model. -/
def blockGroup : Subgroup (Equiv.Perm (Fin 27)) :=
  Subgroup.closure {blockC, blockD}

abbrev BlockGroup := blockGroup

/-- Distinct labels denote distinct pairs. -/
theorem point_injective : Function.Injective point := by decide +kernel

theorem point_card (i : Fin 27) : (point i).card = 2 := by
  have h : ∀ j : Fin 27, (point j).card = 2 := by decide +kernel
  exact h i

/-- First centralizer word's action on the labelled pairs. -/
theorem cMap_point (i : Fin 27) : (point i).image Tables.cMap = point (blockC i) := by
  have h : ∀ j : Fin 27, (point j).image Tables.cMap = point (blockC j) := by
    decide +kernel
  exact h i

/-- Second centralizer word's action on the labelled pairs. -/
theorem dMap_point (i : Fin 27) : (point i).image Tables.dMap = point (blockD i) := by
  have h : ∀ j : Fin 27, (point j).image Tables.dMap = point (blockD j) := by
    decide +kernel
  exact h i

end Sporadic.LeechRelated.Suz.CentralizerSection
