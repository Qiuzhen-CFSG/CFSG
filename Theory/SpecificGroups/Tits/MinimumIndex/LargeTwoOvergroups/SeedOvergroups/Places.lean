module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.Seeds

/-!
# Concrete candidate parabolics for the order-64 Tits seeds

The thirty-eight places are literal conjugates of the two marked parabolics.
For each seed the table lists between two and sixteen places, in a candidate
leaf elimination order. The words use Lean's left multiplication convention.
The tables are definitions, not assertions of fixed-point exhaustiveness,
intersection geometry, or overgroup coverage. Their untrusted derivation and
candidate leaf parents are preserved in `source/`.

Source: the Parrott (1972), section 5, p.683 generators, and the actual first
centralizer and second-center normalizer in `RelativeParabolicNormalizers`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups
open Subgroup ExceptionalParabolics

/-- Short words for the conjugating elements; products act on the left. -/
def placeWord : Fin 38 → List ParrottGenerator :=
  ![[],
    [.r8],
    [.r1, .r8],
    [.s8, .r8],
    [.r8, .r1, .r8],
    [.s1, .r1, .r8],
    [.s2, .r1, .r8],
    [.s3, .r1, .r8],
    [.s7, .r1, .r8],
    [.s6, .r8, .r1, .r8],
    [.s7, .r8, .r1, .r8],
    [.s2, .s1, .r1, .r8],
    [.s7, .s1, .r1, .r8],
    [.s7, .s2, .r1, .r8],
    [.r8, .s7, .r1, .r8],
    [.s7, .s6, .r8, .r1, .r8],
    [.s7, .r8, .s1, .r1, .r8],
    [],
    [.r1],
    [.r8, .r1],
    [.s1, .r1],
    [.s3, .r1],
    [.s7, .r1],
    [.s7, .r8, .r1],
    [.s8, .r8, .r1],
    [.r8, .s1, .r1],
    [.r8, .s7, .r1],
    [.s3, .r1, .r8, .r1],
    [.s5, .r1, .r8, .r1],
    [.s8, .s7, .r8, .r1],
    [.s1, .s8, .r8, .r1],
    [.s3, .s8, .r8, .r1],
    [.s7, .s1, .r1, .r8, .r1],
    [.s3, .s2, .r1, .r8, .r1],
    [.s5, .s2, .r1, .r8, .r1],
    [.s4, .s3, .r1, .r8, .r1],
    [.s2, .s5, .r1, .r8, .r1],
    [.s4, .s5, .r1, .r8, .r1]]

/-- The first seventeen entries use the first parabolic. -/
def placeBase (j : Fin 38) : Subgroup Atlas1600Group :=
  if j.val < 17 then first else second

/-- The actual element evaluating the stored conjugating word. -/
def placeConjugator (j : Fin 38) : Atlas1600Group :=
  ((placeWord j).map atlas1600ParrottAssignment).prod

/-- A literal conjugate, with no abstract model tags. -/
def place (j : Fin 38) : Subgroup Atlas1600Group :=
  (placeBase j).map (MulAut.conj (placeConjugator j)).toMonoidHom

/-- The eighteen distinct candidate trees, in leaf elimination order. -/
def placePattern : Fin 18 → List (Fin 38) :=
  ![[0, 3, 4, 9, 14, 16, 17, 19, 23, 25, 1, 26],
    [0, 3, 14, 16, 17, 19, 23, 25, 1, 26],
    [0, 3, 17, 19, 23, 25, 1, 26],
    [0, 3, 10, 14, 15, 16, 17, 19, 23, 25, 1, 26],
    [0, 1, 3, 17],
    [18, 19, 20, 21, 22, 0, 23, 24, 25, 26, 1, 17, 29, 30, 3, 31],
    [0, 1, 17, 24, 29, 30, 3, 31],
    [1, 3, 17, 18, 20, 21, 0, 22],
    [17, 18, 20, 21, 0, 22],
    [0, 17],
    [1, 3, 7, 8, 12, 13, 17, 18, 20, 21, 0, 22],
    [7, 12, 17, 18, 20, 21, 0, 22],
    [2, 5, 6, 11, 17, 18, 20, 21, 0, 22],
    [1, 3, 5, 8, 11, 13, 17, 18, 20, 21, 0, 22],
    [2, 5, 6, 8, 11, 13, 17, 18, 20, 21, 0, 22],
    [1, 3, 7, 12, 17, 18, 20, 21, 0, 22],
    [17, 18, 20, 22, 0, 27, 28, 32, 33, 34, 35, 36, 12, 21, 7, 37],
    [5, 8, 11, 13, 17, 18, 20, 21, 0, 22]]

/-- The candidate tree assigned to each published seed. -/
def seedPattern : Fin 122 → Fin 18 :=
  ![0, 1, 2, 3, 4, 1, 2, 4, 4, 4, 4, 2, 5, 6, 7, 7, 8, 4, 4, 4, 4, 6, 7, 7, 4, 7, 8, 8, 2, 2, 4, 4, 4, 4, 4, 9, 9, 9, 9, 9, 9, 7, 8, 8, 8, 8, 4, 4, 4, 4, 4, 4, 10, 6, 7, 11, 4, 4, 4, 8, 12, 6, 4, 13, 11, 8, 9, 12, 9, 14, 11, 8, 9, 9, 9, 9, 9, 9, 9, 8, 8, 9, 8, 9, 4, 4, 4, 4, 8, 8, 8, 11, 11, 8, 11, 11, 15, 15, 11, 11, 8, 8, 11, 11, 8, 4, 8, 8, 8, 4, 11, 11, 8, 8, 11, 16, 17, 8, 17, 8, 11, 11]

/-- Candidate fixed places for a seed. -/
def placeIds (i : Fin 122) : List (Fin 38) :=
  placePattern (seedPattern i)

/-- The corresponding actual subgroups of the Atlas carrier. -/
def places (i : Fin 122) : List (Subgroup Atlas1600Group) :=
  (placeIds i).map place

/-- Adjoin one actual element to the actual seed. -/
def singleExtension (i : Fin 122) (x : Atlas1600Group) : Subgroup Atlas1600Group :=
  seed i ⊔ closure {x}

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups
