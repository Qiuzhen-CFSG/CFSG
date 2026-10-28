module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# An explicit presentation dominating perfect central covers of the J₂ centralizer

Seven short words hold in the marked generators `a,c` of the literal order-1920
centralizer. In a central extension they become central. Two commutator words
express `a,c`; evaluating them at arbitrary lifts gives normalized lifts that
satisfy the same two commutator identities exactly. We impose the fourteen
centrality relations and these two normalization relations on a free group.

The connection to the literal centralizer and the lifting property are proved
in sibling modules. Finiteness and the order bound 3840 are separate obligations.
Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407; the marked generators
and commutator words are from the checked ATLAS J2G1-p100B0 local calculation
in `FirstParabolic/CoverSquareOrbit.lean`. See `source/README.md`.
-/

@[expose] public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation
open scoped commutatorElement

def letter {G : Type*} [Group G] (x y : G) (i : Bool) : G := if i then y else x

/-- GAP's commutator convention, written explicitly. -/
def gapCommutator {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

def baseValue {G : Type*} [Group G] (x y : G) : Fin 7 → G :=
  ![x ^ 2, y ^ 5, (x * y) ^ 12, (x * y ^ 2) ^ 10,
    gapCommutator x y ^ 5, gapCommutator x (y ^ 2) ^ 6,
    (x * y * x * y ^ 2) ^ 4]

def leftWord {G : Type*} [Group G] (x y : G) (i : Bool) : G :=
  if i then y⁻¹ * x * y⁻¹ else y⁻¹ * y⁻¹ * x * y

def rightWord {G : Type*} [Group G] (x y : G) (i : Bool) : G :=
  if i then x * y * x * y⁻¹ * x * y * x else y * x * y⁻¹ * y⁻¹ * x

def normalize {G : Type*} [Group G] (x y : G) (i : Bool) : G :=
  ⁅leftWord x y i, rightWord x y i⁆

/-- The first fourteen words centralize the seven base relations with both
generators; the last two normalize the generators by commutators. -/
def relationValue {G : Type*} [Group G] (x y : G) : Fin 16 → G :=
  ![⁅baseValue x y 0, x⁆, ⁅baseValue x y 0, y⁆,
    ⁅baseValue x y 1, x⁆, ⁅baseValue x y 1, y⁆,
    ⁅baseValue x y 2, x⁆, ⁅baseValue x y 2, y⁆,
    ⁅baseValue x y 3, x⁆, ⁅baseValue x y 3, y⁆,
    ⁅baseValue x y 4, x⁆, ⁅baseValue x y 4, y⁆,
    ⁅baseValue x y 5, x⁆, ⁅baseValue x y 5, y⁆,
    ⁅baseValue x y 6, x⁆, ⁅baseValue x y 6, y⁆,
    normalize x y false * x⁻¹, normalize x y true * y⁻¹]

theorem map_baseValue {G H : Type*} [Group G] [Group H] (f : G →* H)
    (x y : G) (i : Fin 7) : f (baseValue x y i) = baseValue (f x) (f y) i := by
  fin_cases i <;> simp [baseValue, gapCommutator]

theorem map_leftWord {G H : Type*} [Group G] [Group H] (f : G →* H)
    (x y : G) (i : Bool) : f (leftWord x y i) = leftWord (f x) (f y) i := by
  cases i <;> simp [leftWord]

theorem map_rightWord {G H : Type*} [Group G] [Group H] (f : G →* H)
    (x y : G) (i : Bool) : f (rightWord x y i) = rightWord (f x) (f y) i := by
  cases i <;> simp [rightWord]

theorem map_normalize {G H : Type*} [Group G] [Group H] (f : G →* H)
    (x y : G) (i : Bool) : f (normalize x y i) = normalize (f x) (f y) i := by
  simp only [normalize, map_commutatorElement, map_leftWord, map_rightWord]

theorem map_relationValue {G H : Type*} [Group G] [Group H] (f : G →* H)
    (x y : G) (i : Fin 16) : f (relationValue x y i) = relationValue (f x) (f y) i := by
  fin_cases i <;> simp [relationValue, map_commutatorElement, map_baseValue, map_normalize]

def relator : Fin 16 → FreeGroup Bool := relationValue (FreeGroup.of false) (FreeGroup.of true)

abbrev Presentation := PresentedGroup (Set.range relator)

def generator : Bool → Presentation := PresentedGroup.of

theorem generator_relations (i : Fin 16) : relationValue (generator false) (generator true) i = 1 := by
  have h := PresentedGroup.one_of_mem (rels := Set.range relator) ⟨i, rfl⟩
  exact (map_relationValue (PresentedGroup.mk (Set.range relator))
    (FreeGroup.of false) (FreeGroup.of true) i).symm.trans h

def evaluate {G : Type*} [Group G] (x y : G)
    (h : ∀ i, relationValue x y i = 1) : Presentation →* G :=
  PresentedGroup.toGroup (f := letter x y) (by
    rintro _ ⟨i, rfl⟩
    simpa only [relator, map_relationValue, FreeGroup.lift_apply_of, letter,
      Bool.false_eq_true, ↓reduceIte] using h i)

@[simp] theorem evaluate_generator {G : Type*} [Group G] (x y : G)
    (h : ∀ i, relationValue x y i = 1) (i : Bool) :
    evaluate x y h (generator i) = letter x y i := PresentedGroup.toGroup.of _

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation
