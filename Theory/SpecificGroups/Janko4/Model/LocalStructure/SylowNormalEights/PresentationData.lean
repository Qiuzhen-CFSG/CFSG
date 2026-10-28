module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.Basic

/-!
# A candidate power-conjugate presentation for the J₄ local two-group

These are definitions transcribed from the exploratory matrix calculation in
`source/pc.json`. They make no assertion that the presented group is the actual
matrix subgroup. The generator indices are zero-based. A word `[i,j]` means
`g i * g j`, and `conjugateWord i j` is the proposed value of
`(g i)⁻¹ * g j * g i` for `i < j`.

The matrix source is the max1 kernel and four quotient Sylow words in
`AutomorphismReduction.FirstGenerator.OddIndex.SylowCandidate`. The comparison
with those literal matrices is a separate proof obligation. See the adjacent
source README for provenance and conventions.
-/

@[expose] public section
namespace Janko4.LocalStructure.SylowNormalEights.Presentation

/-- The candidate square words, in ascending generator order. -/
def squareWord (i : Fin 21) : List (Fin 21) :=
  match i.val with
  | 0 => [14]
  | 2 => [6]
  | 3 => [16, 20]
  | _ => []

/-- The candidate inverse-conjugation words. Only `i < j` is imposed. -/
def conjugateWord (i j : Fin 21) : List (Fin 21) :=
  match i.val, j.val with
  | 0, 1 => [1, 3, 6, 16, 17, 18, 19]
  | 0, 2 => [2, 6, 8, 17, 20]
  | 0, 3 => [3, 11, 14, 17, 19, 20]
  | 0, 4 => [4, 6, 10, 13, 17, 18, 19, 20]
  | 0, 5 => [5, 17, 20]
  | 0, 6 => [6, 11, 14, 17, 20]
  | 0, 7 => [7, 9, 12, 13, 15, 16, 17, 18]
  | 0, 8 => [8, 11, 14, 16, 17, 20]
  | 0, 9 => [9, 14, 17, 19, 20]
  | 0, 10 => [10, 11, 14, 16, 17, 20]
  | 0, 11 => [11, 20]
  | 0, 12 => [12, 14, 20]
  | 0, 13 => [13, 16, 17, 18, 19, 20]
  | 0, 15 => [15, 16, 18, 19, 20]
  | 0, 16 => [16, 20]
  | 0, 17 => [17, 20]
  | 0, 19 => [19, 20]
  | 1, 2 => [2, 4, 9, 10, 18, 20]
  | 1, 3 => [3, 9, 14, 16, 18]
  | 1, 5 => [5, 10, 12, 13, 15, 20]
  | 1, 6 => [6, 9, 14, 16, 18, 19, 20]
  | 1, 8 => [8, 10, 20]
  | 1, 9 => [9, 19, 20]
  | 1, 11 => [11, 14, 16, 17, 18, 19, 20]
  | 1, 12 => [12, 15]
  | 1, 13 => [13, 15]
  | 1, 14 => [14, 18, 19]
  | 1, 16 => [16, 18, 20]
  | 1, 17 => [17, 19, 20]
  | 2, 3 => [3, 6, 13, 16, 19, 20]
  | 2, 4 => [4, 9, 15, 18, 20]
  | 2, 5 => [5, 8, 13, 14, 15, 17, 18, 19, 20]
  | 2, 7 => [7, 16, 18, 20]
  | 2, 8 => [8, 11, 14, 16]
  | 2, 9 => [9, 17]
  | 2, 10 => [10, 14, 15, 16, 17, 20]
  | 2, 11 => [11, 16, 20]
  | 2, 12 => [12, 13, 18, 20]
  | 2, 13 => [13, 16, 18, 19]
  | 2, 14 => [14, 17]
  | 2, 15 => [15, 18]
  | 2, 18 => [18, 19, 20]
  | 3, 4 => [4, 9, 15, 18, 19, 20]
  | 3, 6 => [6, 16, 18, 20]
  | 3, 7 => [7, 18, 20]
  | 3, 8 => [8, 11, 14, 20]
  | 3, 9 => [9, 18]
  | 3, 10 => [10, 14, 16, 19, 20]
  | 3, 11 => [11, 20]
  | 3, 12 => [12, 20]
  | 3, 13 => [13, 16, 18, 19]
  | 3, 14 => [14, 20]
  | 3, 15 => [15, 18, 19]
  | 3, 17 => [17, 20]
  | 4, 5 => [5, 10, 13]
  | 4, 6 => [6, 17, 18, 19, 20]
  | 4, 7 => [7, 15]
  | 4, 8 => [8, 15]
  | 4, 11 => [11, 17, 18, 19]
  | 4, 12 => [12, 15]
  | 4, 14 => [14, 20]
  | 4, 16 => [16, 19]
  | 5, 6 => [6, 11, 14, 17]
  | 5, 7 => [7, 12]
  | 5, 9 => [9, 14, 18, 20]
  | 5, 11 => [11, 20]
  | 5, 14 => [14, 20]
  | 5, 18 => [18, 20]
  | 5, 19 => [19, 20]
  | 6, 7 => [7, 19, 20]
  | 6, 8 => [8, 16, 17, 20]
  | 6, 10 => [10, 17, 18]
  | 6, 12 => [12, 16, 18, 20]
  | 6, 13 => [13, 19, 20]
  | 6, 15 => [15, 19, 20]
  | 7, 8 => [8, 13]
  | 7, 9 => [9, 18, 19]
  | 7, 10 => [10, 15]
  | 7, 11 => [11, 16]
  | 7, 14 => [14, 18, 19]
  | 7, 17 => [17, 19, 20]
  | 8, 9 => [9, 17]
  | 8, 11 => [11, 20]
  | 8, 14 => [14, 20]
  | 8, 18 => [18, 20]
  | 9, 10 => [10, 19, 20]
  | 9, 12 => [12, 18, 19]
  | 9, 13 => [13, 19]
  | 10, 14 => [14, 20]
  | 10, 16 => [16, 20]
  | 11, 15 => [15, 20]
  | 12, 17 => [17, 20]
  | 13, 14 => [14, 20]
  | _, _ => [j]

end Janko4.LocalStructure.SylowNormalEights.Presentation
