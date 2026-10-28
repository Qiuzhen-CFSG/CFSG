module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# Explicit Schreier tables for the final four Fi₂₃ lift stages

The representatives are positive words in the four generators at each stage,
with identity padding after the last genuine generator. Factors are positive
words in the following stage. Multiplication and table orientation follow
Lean's left action: `generator * representative = nextRepresentative * factor`.

This module checks only the small index permutations and separation of the
proposed orbit labels. The actual permutation identities and the interpretation
of these labels require separate proofs; the numerical witnesses do not prove
stabilizer recognition. Source: retained ATLAS F24G1-p306936B0 data and
`Fi23InFi24Prime/source/faithfulness/`; see `LastFour/source/README.md`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour

/-- Number of proposed coset representatives, independently of subgroup orders. -/
def orbitSize : Fin 4 → Nat
  | 0 => 48
  | 1 => 8
  | 2 => 3
  | 3 => 2

instance (i : Fin 4) : NeZero (orbitSize i) :=
  ⟨by fin_cases i <;> decide⟩

/-- The empty-word representative index. -/
def initial (i : Fin 4) : Fin (orbitSize i) :=
  ⟨0, by fin_cases i <;> decide⟩

def representativeWord : (i : Fin 4) → Fin (orbitSize i) → List (Fin 4)
  | 0 => ![[], [0], [1], [2], [0, 0], [1, 0], [2, 0], [0, 1], [1, 1], [2, 1], [3, 1], [1, 2], [2, 2], [3, 2], [1, 0, 0], [2, 0, 0], [3, 0, 0], [0, 1, 0], [1, 1, 0], [2, 1, 0], [3, 1, 0], [0, 2, 0], [1, 2, 0], [3, 2, 0], [1, 0, 1], [1, 1, 1], [0, 2, 1], [1, 2, 1], [2, 2, 1], [3, 2, 1], [0, 3, 1], [2, 3, 1], [0, 1, 2], [2, 1, 2], [0, 2, 2], [1, 2, 2], [1, 1, 0, 0], [3, 1, 0, 0], [1, 2, 0, 0], [2, 2, 0, 0], [1, 0, 1, 0], [1, 2, 1, 0], [3, 2, 1, 0], [3, 0, 2, 0], [2, 1, 0, 1], [3, 1, 0, 1], [1, 0, 2, 1], [0, 3, 2, 1]]
  | 1 => ![[], [0], [1], [2], [0, 0], [2, 0], [2, 1], [0, 2]]
  | 2 => ![[], [0], [1, 0]]
  | 3 => ![[], [0]]

def orbitPoint : (i : Fin 4) → Fin (orbitSize i) → Fin 306936
  | 0 => ![512, 24462, 1128, 2407, 1216, 1198, 65386, 1138, 2307, 3326, 1088, 147879, 24650, 23273, 3278, 23373, 3141, 1058, 74876, 3168, 2598, 24636, 24470, 65366, 24626, 147883, 558, 74890, 3347, 3176, 24530, 1028, 1036, 2397, 2421, 74927, 3367, 3193, 1188, 23386, 2242, 23286, 3318, 24516, 74940, 24506, 2321, 3133]
  | 1 => ![518, 557, 1163, 537, 3153, 1182, 3152, 547]
  | 2 => ![538, 3143, 1173]
  | 3 => ![1163, 3153]

def transitionIndex : (i : Fin 4) → Fin 4 → Fin (orbitSize i) → Fin (orbitSize i)
  | 0 => ![![1, 4, 7, 8, 11, 17, 21, 12, 3, 26, 30, 32, 34, 23, 27, 6, 19, 10, 24, 16, 2, 13, 38, 43, 28, 31, 22, 14, 35, 47, 46, 9, 42, 40, 39, 45, 18, 44, 25, 20, 33, 5, 0, 15, 37, 36, 41, 29],
      ![2, 5, 8, 11, 14, 18, 22, 24, 25, 27, 21, 17, 35, 4, 36, 38, 39, 40, 31, 41, 6, 19, 12, 1, 16, 34, 46, 13, 42, 7, 23, 30, 20, 0, 33, 32, 9, 15, 44, 43, 26, 45, 37, 29, 28, 47, 3, 10],
      ![3, 6, 9, 12, 15, 19, 17, 22, 5, 28, 31, 33, 29, 10, 25, 39, 21, 38, 2, 24, 16, 27, 23, 34, 44, 40, 8, 0, 7, 45, 47, 35, 18, 30, 4, 46, 41, 26, 13, 32, 20, 1, 36, 37, 11, 14, 42, 43],
      ![0, 1, 10, 13, 16, 20, 23, 17, 15, 29, 2, 11, 30, 3, 37, 8, 4, 7, 35, 42, 5, 43, 22, 6, 45, 25, 26, 44, 33, 9, 12, 31, 32, 28, 41, 18, 40, 14, 47, 46, 36, 34, 19, 21, 27, 24, 39, 38]]
  | 1 => ![![1, 4, 0, 7, 2, 3, 5, 6],
      ![2, 4, 1, 5, 0, 7, 3, 6],
      ![3, 5, 6, 0, 7, 4, 1, 2],
      ![0, 1, 2, 3, 4, 5, 6, 7]]
  | 2 => ![![1, 0, 2],
      ![1, 2, 0],
      ![0, 1, 2],
      ![0, 1, 2]]
  | 3 => ![![1, 0],
      ![0, 1],
      ![0, 1],
      ![0, 1]]

def inverseIndex : (i : Fin 4) → Fin 4 → Fin (orbitSize i) → Fin (orbitSize i)
  | 0 => ![![42, 0, 20, 8, 1, 41, 15, 2, 3, 31, 17, 4, 7, 21, 27, 43, 19, 5, 36, 16, 39, 6, 26, 13, 18, 38, 9, 14, 24, 47, 10, 25, 11, 40, 12, 28, 45, 44, 22, 34, 33, 46, 32, 23, 37, 35, 30, 29],
      ![33, 23, 0, 46, 13, 1, 20, 29, 2, 36, 47, 3, 22, 27, 4, 37, 24, 11, 5, 21, 32, 10, 6, 30, 7, 8, 40, 9, 44, 43, 31, 18, 35, 34, 25, 12, 14, 42, 15, 16, 17, 19, 28, 39, 38, 41, 26, 45],
      ![27, 41, 18, 0, 34, 8, 1, 28, 26, 2, 13, 44, 3, 38, 45, 4, 20, 6, 32, 5, 40, 16, 7, 22, 19, 14, 37, 21, 9, 12, 33, 10, 39, 11, 23, 31, 42, 43, 17, 15, 25, 36, 46, 47, 24, 29, 35, 30],
      ![0, 1, 10, 13, 16, 20, 23, 17, 15, 29, 2, 11, 30, 3, 37, 8, 4, 7, 35, 42, 5, 43, 22, 6, 45, 25, 26, 44, 33, 9, 12, 31, 32, 28, 41, 18, 40, 14, 47, 46, 36, 34, 19, 21, 27, 24, 39, 38]]
  | 1 => ![![2, 0, 4, 5, 1, 6, 7, 3],
      ![4, 2, 0, 6, 1, 3, 7, 5],
      ![3, 6, 7, 0, 5, 1, 2, 4],
      ![0, 1, 2, 3, 4, 5, 6, 7]]
  | 2 => ![![1, 0, 2],
      ![2, 0, 1],
      ![0, 1, 2],
      ![0, 1, 2]]
  | 3 => ![![1, 0],
      ![0, 1],
      ![0, 1],
      ![0, 1]]

def factorWord : (i : Fin 4) → Fin 4 → Fin (orbitSize i) → List (Fin 4)
  | 0 => ![![[], [], [], [0, 2, 0], [0, 0], [], [], [0, 0, 2], [0, 2, 1, 1, 0], [], [], [], [], [0, 2, 0, 0, 0], [0, 0], [2, 0, 0], [2, 2, 1], [1, 0, 2, 0], [2, 2, 0, 0], [0, 1, 1], [0, 1, 1], [0, 1, 0, 0, 0], [0, 0], [1, 0, 0, 0], [0, 0, 2], [2, 2, 1, 0, 0], [0, 2, 1, 1, 0], [2, 2, 1, 0], [0, 2, 0, 0, 0], [], [1], [0, 2, 1, 1], [1, 0, 0], [0, 0, 0, 1], [], [2, 1, 0, 0], [0, 0, 2], [1], [1, 1, 0, 0], [2, 0], [], [1, 0, 0, 0], [2, 2, 0], [2, 2, 1, 0, 0], [0, 1, 0, 0, 0], [1, 1, 0], [0, 2, 1, 1, 0], [2, 2, 0, 0]],
      ![[], [], [], [], [], [], [], [], [], [], [1, 0, 0], [0, 2, 0], [], [0, 0, 0], [], [], [0, 0, 0], [], [2, 2, 1, 0, 0], [], [0, 2], [2, 2], [0, 2, 1, 1, 0], [0], [1], [0, 0, 0, 1], [], [0, 0, 2, 0], [2, 2, 2, 0], [2, 1], [], [2, 2, 0, 0], [2, 2, 2, 1], [], [2, 2, 0, 0], [2], [2], [2, 0], [2, 2, 0, 0], [1, 0, 0], [1, 0, 0, 0], [0, 0, 0], [0, 2, 1, 1, 0], [0, 2, 0, 0, 0], [0, 2, 1, 1, 0], [0, 2, 0], [2, 2, 2, 1, 0], [2, 2, 2, 1, 0]],
      ![[], [], [], [], [], [], [0, 0, 0, 1], [], [2, 1, 1], [], [], [], [1], [1, 0, 0, 0], [2], [], [0], [], [0, 2, 1, 1, 0], [], [1, 0, 2], [2, 0, 0], [0, 0, 0], [2, 1, 0, 0], [], [0, 2, 0], [2, 2, 2, 1, 0], [], [2, 1, 1], [2, 1, 0], [0, 2, 0], [2, 2, 2, 0], [1, 1, 0, 0], [0, 2, 0, 0], [2, 0, 0], [2, 0, 0], [2, 2, 0, 0], [2, 1, 0, 0], [0], [2, 2], [1, 0, 2, 0], [], [0, 0, 1], [0, 2, 0, 0, 0], [0, 2, 1, 1, 0], [2, 2, 1], [0, 1, 0], [0, 2, 1, 1, 0]],
      ![[0, 2], [2, 0], [], [], [], [], [], [2, 1, 0, 0], [0, 1, 1], [], [], [0, 2, 1, 1], [1, 0], [], [], [0, 1, 1], [], [2, 1, 0, 0], [0, 2, 1, 1], [], [], [], [2, 1, 1, 0], [], [], [0, 2], [2, 0], [0, 1, 0, 0, 0], [2, 0, 0, 0], [], [0, 1, 0, 0], [2, 0], [2, 1, 1, 0], [0, 0, 2, 0], [1], [0, 2, 1, 1], [0, 2, 0, 0], [], [2, 2, 2], [1, 0, 2, 0], [2, 2, 2, 1], [2, 2, 0], [], [], [2, 2, 1], [], [2, 2, 2, 0], [2, 2, 2]]]
  | 1 => ![![[], [], [1, 1], [], [1], [1, 1], [0], [0, 1]],
      ![[], [1], [1, 0], [], [0, 1], [0], [1, 1], [1, 0]],
      ![[], [], [], [1], [0], [0, 1], [1], [1]],
      ![[], [], [], [], [], [], [], []]]
  | 2 => ![![[], [], [0]],
      ![[0], [], [0]],
      ![[], [], []],
      ![[], [], []]]
  | 3 => ![![[], []],
      ![[], []],
      ![[], []],
      ![[], []]]

def factorSourceGenerator : (i : Fin 4) → Fin 4 → Fin 4
  | 0 => ![1, 0, 1, 0]
  | 1 => ![0, 0, 0, 0]
  | 2 => ![0, 0, 0, 0]
  | 3 => ![0, 0, 0, 0]

def factorSourceIndex : (i : Fin 4) → Fin 4 → Fin (orbitSize i)
  | 0 => ![23, 30, 35, 0]
  | 1 => ![6, 4, 0, 0]
  | 2 => ![2, 0, 0, 0]
  | 3 => ![0, 0, 0, 0]

def nextLetterWord (i : Fin 4) (a : Fin 4) : List (Fin 4) :=
  if a.val < 3 - i.val then [a] else []

theorem factorSource_spec : ∀ i a,
    factorWord i (factorSourceGenerator i a) (factorSourceIndex i a) =
      nextLetterWord i a := by decide +kernel

/-- Action of a positive word on the finite index set. -/
def walk (i : Fin 4) : List (Fin 4) → Fin (orbitSize i) → Fin (orbitSize i)
  | [], j => j
  | a :: w, j => transitionIndex i a (walk i w j)

theorem representativeWord_walk : ∀ i j,
    walk i (representativeWord i j) (initial i) = j := by decide +kernel

theorem inverseIndex_transitionIndex : ∀ i a j,
    inverseIndex i a (transitionIndex i a j) = j := by decide +kernel

theorem transitionIndex_inverseIndex : ∀ i a j,
    transitionIndex i a (inverseIndex i a j) = j := by decide +kernel

/-- Each transition column is a checked permutation, so inverse group steps
can be deduced from the positive steps. -/
def transition (i : Fin 4) (a : Fin 4) : Equiv.Perm (Fin (orbitSize i)) where
  toFun := transitionIndex i a
  invFun := inverseIndex i a
  left_inv := inverseIndex_transitionIndex i a
  right_inv := transitionIndex_inverseIndex i a

theorem representativeWord_initial : ∀ i,
    representativeWord i (initial i) = [] := by decide +kernel

/-- Only index zero has the proposed base label. -/
theorem orbitPoint_returns : ∀ i j,
    orbitPoint i j = orbitPoint i (initial i) → j = initial i := by decide +kernel

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour
