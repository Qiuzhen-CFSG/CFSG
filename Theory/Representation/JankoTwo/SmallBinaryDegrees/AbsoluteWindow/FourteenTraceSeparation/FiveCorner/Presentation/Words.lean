module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveLocal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.FinCases

/-!
# Literal words for the Hall--Janko norm corner

The words use the retained degree-100 ATLAS carrier. GAP right multiplication
is converted to Lean left composition by inverting each generator and preserving
word order. Letters 0, 1, 2, 3 mean a⁻¹, b⁻¹, a, b respectively.
The two subgroup words and the nine sums are the witnesses recorded by the
five-corner discovery scripts; their required identities are proved separately.

Source: ATLAS J2G1-p100B0, with original attribution and licensing discussion retained in
Theory/SpecificGroups/LeechRelated/AtlasCarriers/source/. The local application
is Guralnick--Malle Proposition 5.1 and corrected Hiss--Malle Table 2.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
open Sporadic.LeechRelated.J2

/-- GAP's signed generators after conversion to left composition. -/
def letter : Fin 4 → Carrier :=
  ![GeneratorPair.a⁻¹, GeneratorPair.b⁻¹, GeneratorPair.a, GeneratorPair.b]

/-- Evaluate a word in the actual carrier, preserving its order. -/
def word (w : List (Fin 4)) : Carrier := (w.map letter).prod

/-- The corresponding finite permutation tables. -/
def tableLetter : Fin 4 → Equiv.Perm (Fin 100) :=
  ![GeneratorPair.tableA⁻¹, GeneratorPair.tableB⁻¹,
    GeneratorPair.tableA, GeneratorPair.tableB]

theorem inclusion_letter (i : Fin 4) : inclusion (letter i) = tableLetter i := by
  fin_cases i <;>
    simp [letter, tableLetter, inclusion, GeneratorPair.a, GeneratorPair.b,
      GeneratorPair.generatorA_eq_table, GeneratorPair.generatorB_eq_table]

/-- Word comparison used in all later finite permutation certificates. -/
theorem inclusion_word (w : List (Fin 4)) :
    inclusion (word w) = (w.map tableLetter).prod := by
  simp only [word, map_list_prod, List.map_map, Function.comp_def, inclusion_letter]

def leftWord : List (Fin 4) := [0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2]

def leftGenerator : Carrier := word leftWord

def leftValues : Fin 100 → Fin 100 :=
  ![25, 5, 74, 59, 92, 46, 41, 82, 68, 53, 32, 26, 6, 43, 79, 71, 70, 24, 13, 39, 95, 37, 10, 49, 27, 29, 94, 83, 73, 19, 63, 17, 34, 89, 47, 81, 40, 67, 33, 0, 66, 91, 69, 30, 48, 62, 28, 22, 7, 20, 60, 9, 57, 52, 97, 77, 8, 51, 87, 56, 61, 45, 50, 18, 4, 64, 55, 78, 3, 84, 42, 14, 58, 1, 72, 15, 38, 36, 80, 75, 21, 90, 85, 31, 16, 44, 88, 2, 35, 99, 86, 98, 93, 65, 54, 96, 23, 11, 12, 76]

def leftInvValues : Fin 100 → Fin 100 :=
  ![39, 73, 87, 68, 64, 1, 12, 48, 56, 51, 22, 97, 98, 18, 71, 75, 84, 31, 63, 29, 49, 80, 47, 96, 17, 0, 11, 24, 46, 25, 43, 83, 10, 38, 32, 88, 77, 21, 76, 19, 36, 6, 70, 13, 85, 61, 5, 34, 44, 23, 62, 57, 53, 9, 94, 66, 59, 52, 72, 3, 50, 60, 45, 30, 65, 93, 40, 37, 8, 42, 16, 15, 74, 28, 2, 79, 99, 55, 67, 14, 78, 35, 7, 27, 69, 82, 90, 58, 86, 33, 81, 41, 4, 92, 26, 20, 95, 54, 91, 89]

def rightWord : List (Fin 4) := [1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3]

def rightGenerator : Carrier := word rightWord

def rightValues : Fin 100 → Fin 100 :=
  ![99, 25, 21, 48, 17, 29, 16, 9, 85, 36, 18, 45, 84, 1, 65, 92, 23, 74, 73, 33, 54, 79, 63, 26, 72, 76, 62, 58, 39, 38, 46, 2, 13, 47, 43, 3, 81, 75, 34, 89, 90, 70, 20, 5, 57, 12, 19, 30, 51, 94, 41, 77, 66, 40, 60, 88, 82, 55, 78, 7, 91, 98, 6, 28, 31, 83, 86, 15, 44, 95, 49, 93, 67, 0, 37, 4, 32, 35, 71, 64, 14, 59, 53, 87, 96, 52, 8, 80, 68, 22, 56, 42, 24, 27, 50, 97, 11, 61, 69, 10]

def rightInvValues : Fin 100 → Fin 100 :=
  ![73, 13, 31, 35, 75, 43, 62, 59, 86, 7, 99, 96, 45, 32, 80, 67, 6, 4, 10, 46, 42, 2, 89, 16, 92, 1, 23, 93, 63, 5, 47, 64, 76, 19, 38, 77, 9, 74, 29, 28, 53, 50, 91, 34, 68, 11, 30, 33, 3, 70, 94, 48, 85, 82, 20, 57, 90, 44, 27, 81, 54, 97, 26, 22, 79, 14, 52, 72, 88, 98, 41, 78, 24, 18, 17, 37, 25, 51, 58, 21, 87, 36, 56, 65, 12, 8, 66, 83, 55, 39, 40, 60, 15, 71, 49, 69, 84, 95, 61, 0]

/-- Nine fixed lists of words; each list will be summed after condensation.
No normalizer operator occurs in these generators. -/
def generatorWords : Fin 9 → List (List (Fin 4)) :=
  ![[[1, 1, 0, 3, 1, 3, 3, 0, 1, 0, 3, 1, 3, 3, 3, 0, 3, 0, 1, 3], [3, 1, 3, 1, 1, 0, 1, 3, 0, 0, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1], [0, 3, 3, 0, 0, 0, 0, 3, 1, 3, 1, 3, 3, 3, 0, 0, 1, 0, 1, 1], [3, 1, 0, 0, 0, 1, 3, 0, 3, 0, 3, 3, 0, 1, 3, 0, 3, 3, 1, 0], [1, 1, 3, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 3, 3], [0, 3, 0, 1, 0, 3, 0, 1, 3, 3, 3, 3, 1, 1, 1, 0, 1, 0, 3, 0], [0, 1, 3, 0, 1, 1, 1, 3, 1, 0, 0, 3, 3, 3, 3, 0, 1, 3, 3, 3], [0, 1, 0, 0, 3, 1, 0, 3, 0, 0, 0, 1, 3, 1, 1, 3, 3, 3, 3, 0]],
    [[1, 1, 1, 1, 3, 0, 0, 3, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 0], [0, 3, 3, 0, 0, 0, 0, 3, 1, 3, 1, 3, 3, 3, 0, 0, 1, 0, 1, 1], [1, 0, 3, 3, 1, 1, 1, 1, 1, 3, 1, 1, 0, 0, 1, 0, 1, 0, 3, 3], [1, 1, 3, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 3, 3], [3, 1, 3, 1, 1, 3, 3, 3, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 3, 0], [0, 3, 1, 0, 0, 0, 1, 3, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1], [0, 3, 0, 1, 0, 3, 0, 1, 3, 3, 3, 3, 1, 1, 1, 0, 1, 0, 3, 0], [0, 1, 3, 0, 1, 1, 1, 3, 1, 0, 0, 3, 3, 3, 3, 0, 1, 3, 3, 3]],
    [[1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 3, 3, 1, 1, 1, 0, 0, 1, 0], [3, 1, 1, 0, 0, 3, 3, 1, 1, 3, 0, 3, 0, 3, 1, 1, 0, 3, 0, 1], [3, 1, 0, 0, 0, 1, 3, 0, 3, 0, 3, 3, 0, 1, 3, 0, 3, 3, 1, 0], [0, 3, 0, 1, 0, 3, 0, 1, 3, 3, 3, 3, 1, 1, 1, 0, 1, 0, 3, 0], [0, 1, 3, 0, 1, 1, 1, 3, 1, 0, 0, 3, 3, 3, 3, 0, 1, 3, 3, 3], [1, 1, 0, 1, 3, 1, 0, 0, 1, 0, 1, 3, 1, 1, 1, 1, 1, 0, 1, 0], [0, 1, 0, 0, 3, 3, 3, 1, 3, 0, 3, 3, 3, 3, 0, 3, 1, 1, 1, 0], [0, 1, 0, 3, 1, 3, 3, 0, 3, 0, 1, 0, 3, 1, 3, 1, 3, 0, 3, 3]],
    [[3, 1, 1, 1, 3, 1, 0, 3, 3, 1, 3, 3, 0, 3, 0, 0, 1, 3, 0, 3], [0, 3, 1, 1, 0, 0, 1, 3, 1, 1, 1, 3, 3, 3, 0, 0, 1, 1, 0, 1], [3, 1, 1, 0, 3, 3, 3, 0, 1, 1, 3, 3, 0, 0, 3, 1, 1, 0, 0, 1], [1, 3, 0, 1, 1, 1, 1, 1, 3, 0, 1, 1, 3, 0, 3, 3, 1, 0, 1, 3], [3, 1, 3, 1, 1, 3, 3, 3, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 3, 0], [0, 3, 1, 0, 0, 0, 1, 3, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1], [1, 1, 0, 1, 3, 1, 0, 0, 1, 0, 1, 3, 1, 1, 1, 1, 1, 0, 1, 0], [0, 1, 0, 3, 1, 3, 3, 0, 3, 0, 1, 0, 3, 1, 3, 1, 3, 0, 3, 3]],
    [[0, 3, 3, 0, 0, 0, 0, 3, 1, 3, 1, 3, 3, 3, 0, 0, 1, 0, 1, 1], [0, 3, 1, 1, 0, 0, 1, 3, 1, 1, 1, 3, 3, 3, 0, 0, 1, 1, 0, 1], [0, 3, 1, 0, 0, 1, 1, 3, 3, 0, 1, 1, 3, 1, 3, 3, 1, 3, 3, 0], [1, 1, 3, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 3, 3], [1, 3, 0, 1, 1, 1, 1, 1, 3, 0, 1, 1, 3, 0, 3, 3, 1, 0, 1, 3], [0, 3, 0, 3, 0, 3, 0, 0, 3, 0, 3, 0, 0, 3, 0, 1, 0, 0, 0, 3], [1, 1, 0, 1, 3, 1, 0, 0, 1, 0, 1, 3, 1, 1, 1, 1, 1, 0, 1, 0], [0, 1, 0, 3, 1, 3, 3, 0, 3, 0, 1, 0, 3, 1, 3, 1, 3, 0, 3, 3]],
    [[1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 3, 3, 1, 1, 1, 0, 0, 1, 0], [3, 1, 0, 0, 0, 1, 3, 0, 3, 0, 3, 3, 0, 1, 3, 0, 3, 3, 1, 0], [1, 1, 3, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 3, 3], [3, 1, 3, 1, 1, 3, 3, 3, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 3, 0], [0, 3, 1, 0, 0, 0, 1, 3, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1], [1, 3, 1, 1, 3, 3, 1, 1, 3, 0, 1, 3, 3, 0, 0, 0, 0, 1, 1, 3], [0, 1, 0, 0, 3, 1, 0, 3, 0, 0, 0, 1, 3, 1, 1, 3, 3, 3, 3, 0], [1, 1, 0, 1, 3, 1, 0, 0, 1, 0, 1, 3, 1, 1, 1, 1, 1, 0, 1, 0]],
    [[1, 1, 0, 3, 1, 3, 3, 0, 1, 0, 3, 1, 3, 3, 3, 0, 3, 0, 1, 3], [0, 3, 3, 0, 0, 0, 0, 3, 1, 3, 1, 3, 3, 3, 0, 0, 1, 0, 1, 1], [3, 1, 0, 0, 0, 1, 3, 0, 3, 0, 3, 3, 0, 1, 3, 0, 3, 3, 1, 0], [1, 0, 0, 1, 1, 1, 1, 3, 3, 3, 0, 1, 3, 1, 0, 1, 0, 0, 0, 0], [0, 3, 1, 0, 0, 1, 1, 3, 3, 0, 1, 1, 3, 1, 3, 3, 1, 3, 3, 0], [3, 1, 1, 0, 3, 3, 3, 0, 1, 1, 3, 3, 0, 0, 3, 1, 1, 0, 0, 1], [1, 3, 1, 1, 3, 3, 1, 1, 3, 0, 1, 3, 3, 0, 0, 0, 0, 1, 1, 3], [1, 1, 0, 1, 3, 1, 0, 0, 1, 0, 1, 3, 1, 1, 1, 1, 1, 0, 1, 0]],
    [[1, 0, 0, 1, 1, 1, 1, 3, 3, 3, 0, 1, 3, 1, 0, 1, 0, 0, 0, 0], [0, 3, 1, 0, 0, 1, 1, 3, 3, 0, 1, 1, 3, 1, 3, 3, 1, 3, 3, 0], [3, 1, 1, 0, 3, 3, 3, 0, 1, 1, 3, 3, 0, 0, 3, 1, 1, 0, 0, 1], [3, 1, 3, 1, 1, 3, 3, 3, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 3, 0], [0, 3, 0, 3, 0, 3, 0, 0, 3, 0, 3, 0, 0, 3, 0, 1, 0, 0, 0, 3], [0, 3, 0, 1, 0, 3, 0, 1, 3, 3, 3, 3, 1, 1, 1, 0, 1, 0, 3, 0], [1, 1, 0, 1, 3, 1, 0, 0, 1, 0, 1, 3, 1, 1, 1, 1, 1, 0, 1, 0], [0, 1, 0, 0, 3, 3, 3, 1, 3, 0, 3, 3, 3, 3, 0, 3, 1, 1, 1, 0]],
    [[0, 1, 0, 1, 1]]]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
