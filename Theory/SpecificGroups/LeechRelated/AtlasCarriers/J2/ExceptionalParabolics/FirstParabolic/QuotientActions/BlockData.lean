module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.LocalFusion.Soundness
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.FinCases

/-!
# Five blocks for the first Hall--Janko parabolic

The five 16-point radical orbits are encoded by their color, with `none`
for the other twenty points. The centralizer letters induce even permutations
of the colors; the fixed outer word induces a transposition. The identities
below are finite kernel checks against the already certified ATLAS tables.

Source: Aschbacher--Smith F.1.12(I)(10)--(11), printed p.263, and the
ATLAS J2G1-p100B0 data retained in this repository. The block discovery
witnesses are in `FirstParabolic/source/structure-witnesses.json`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.QuotientActions
open Theory.GroupTheory GeneratorPair Seed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

def color (x : Fin 100) : Option (Fin 5) :=
  match x.val with
  | 1 | 6 | 15 | 22 | 24 | 31 | 35 | 42 | 77 | 85 | 88 | 89 | 93 | 95 | 98 | 99 => some 0
  | 2 | 8 | 9 | 17 | 23 | 34 | 39 | 43 | 47 | 56 | 58 | 64 | 69 | 70 | 86 | 94 => some 1
  | 3 | 12 | 16 | 25 | 29 | 30 | 36 | 40 | 53 | 60 | 62 | 65 | 76 | 79 | 80 | 92 => some 2
  | 7 | 13 | 18 | 27 | 37 | 38 | 45 | 48 | 49 | 55 | 59 | 73 | 78 | 87 | 96 | 97 => some 3
  | 10 | 11 | 14 | 19 | 28 | 44 | 46 | 50 | 52 | 54 | 57 | 67 | 74 | 75 | 90 | 91 => some 4
  | _ => none

def basePoint : Fin 5 → Fin 100 := ![1, 2, 3, 7, 10]

theorem color_basePoint : ∀ i, color (basePoint i) = some i := by
  decide +kernel

def letterMap : Fin 3 → Fin 5 → Fin 5 := ![![4, 1, 3, 2, 0], ![4, 2, 3, 0, 1], ![3, 4, 1, 2, 0]]

def inverseLetter : Fin 3 → Fin 3 := ![0, 2, 1]

theorem letterMap_left : ∀ s i, letterMap (inverseLetter s) (letterMap s i) = i := by
  decide +kernel

theorem letterMap_right : ∀ s i, letterMap s (letterMap (inverseLetter s) i) = i := by
  decide +kernel

def letterPerm (s : Fin 3) : Equiv.Perm (Fin 5) :=
  ⟨letterMap s, letterMap (inverseLetter s), letterMap_left s, letterMap_right s⟩

theorem letterPerm_even : ∀ s, letterPerm s ∈ alternatingGroup (Fin 5) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

def evenLetter (s : Fin 3) : alternatingGroup (Fin 5) :=
  ⟨letterPerm s, letterPerm_even s⟩

theorem letter_color_check : ∀ s x,
    color (FirstFusion.LocalCertificate.localLetterValue s x) =
      (color x).map (letterPerm s) := by
  decide +kernel

def outerPerm : Equiv.Perm (Fin 5) := Equiv.swap 2 4

theorem outer_color_check : ∀ x,
    color (SecondParabolic.outerValues x) = (color x).map outerPerm := by
  decide +kernel

def radicalPerm (i : Fin 4) : Equiv.Perm (Fin 100) :=
  evalWord PairNormalizer.SylowData.sGenTable (radicalWord i)

theorem radical_color_check : ∀ i x, color (radicalPerm i x) = color x := by
  decide +kernel

/-- Sixty words giving all even permutations of the five colors. -/
def imageWord : Fin 60 → List (Fin 3) :=
  ![[], [0], [1], [2], [0, 1], [0, 2], [1, 0], [1, 1], [2, 0], [2, 2], [0, 1, 0], [0, 1, 1], [0, 2, 0], [0, 2, 2], [1, 0, 2], [1, 1, 0], [2, 0, 1], [2, 2, 0], [0, 1, 0, 2], [0, 1, 1, 0], [0, 2, 0, 1], [0, 2, 2, 0], [1, 0, 2, 0], [1, 0, 2, 2], [1, 1, 0, 2], [2, 0, 1, 0], [2, 0, 1, 1], [2, 2, 0, 1], [0, 1, 0, 2, 0], [0, 1, 1, 0, 2], [0, 2, 0, 1, 0], [0, 2, 2, 0, 1], [1, 0, 2, 0, 1], [1, 0, 2, 2, 0], [1, 1, 0, 2, 2], [2, 0, 1, 0, 2], [2, 0, 1, 1, 0], [2, 2, 0, 1, 1], [0, 1, 0, 2, 0, 1], [0, 1, 1, 0, 2, 2], [0, 2, 0, 1, 0, 2], [0, 2, 2, 0, 1, 1], [1, 0, 2, 0, 1, 0], [1, 0, 2, 2, 0, 1], [1, 1, 0, 2, 2, 0], [2, 0, 1, 0, 2, 0], [2, 0, 1, 1, 0, 2], [2, 2, 0, 1, 1, 0], [0, 1, 1, 0, 2, 2, 0], [0, 2, 2, 0, 1, 1, 0], [1, 0, 2, 0, 1, 0, 2], [1, 0, 2, 2, 0, 1, 1], [1, 1, 0, 2, 2, 0, 1], [2, 0, 1, 0, 2, 0, 1], [2, 0, 1, 1, 0, 2, 2], [2, 2, 0, 1, 1, 0, 2], [0, 1, 1, 0, 2, 2, 0, 1], [0, 2, 2, 0, 1, 1, 0, 2], [1, 1, 0, 2, 2, 0, 1, 1], [0, 1, 1, 0, 2, 2, 0, 1, 1]]

def imageRepresentative (i : Fin 60) : alternatingGroup (Fin 5) :=
  evalWord evenLetter (imageWord i)

theorem imageRepresentative_val (i : Fin 60) :
    (imageRepresentative i).val = evalWord letterPerm (imageWord i) := by
  have h (w : List (Fin 3)) : (evalWord evenLetter w).val = evalWord letterPerm w := by
    induction w with
    | nil => rfl
    | cons s w ih => change (evenLetter s).val * (evalWord evenLetter w).val = _
                     rw [ih]
                     rfl
  exact h _

theorem imageRepresentative_injective : Function.Injective imageRepresentative := by
  have h : ∀ i j : Fin 60,
      (∀ x : Fin 5, evalWord letterPerm (imageWord i) x =
        evalWord letterPerm (imageWord j) x) → i = j := by
    decide +kernel
  intro i j hij
  apply h i j
  intro x
  simpa only [imageRepresentative_val] using
    congrArg (fun g : alternatingGroup (Fin 5) => g.val x) hij

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.QuotientActions
