module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.Presentation
public import Theory.GroupTheory.CosetWordCertificate.RelatorScan
import Mathlib.Tactic.FinCases

/-!
# Signed words for the normalized J₂ local presentation

The sixteen literal words used by the replay are checked against `relationValue`
in an arbitrary group, including the two exact commutator normalizations.
The alphabet is `0=x, 1=x⁻¹, 2=y, 3=y⁻¹`.
Source: `LocalCentralizer/Presentation.lean`; Aschbacher–Smith I.1.1–I.1.3(1).
-/

@[expose] public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
open Subgroup.CosetWordCertificate
open scoped commutatorElement

def decode (a : Nat) : Letter Bool := (a / 2 % 2 == 1, a % 2 == 0)

def relatorCodes : Fin 16 → List Nat :=
  ![[0, 0, 0, 1, 1, 1],
    [0, 0, 2, 1, 1, 3],
    [2, 2, 2, 2, 2, 0, 3, 3, 3, 3, 3, 1],
    [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3],
    [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1],
    [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 2, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3],
    [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 1],
    [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 2, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 1, 3],
    [1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 0, 3, 1, 2, 0, 3, 1, 2, 0, 3, 1, 2, 0, 3, 1, 2, 0, 3, 1, 2, 0, 1],
    [1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 2, 3, 1, 2, 0, 3, 1, 2, 0, 3, 1, 2, 0, 3, 1, 2, 0, 3, 1, 2, 0, 3],
    [1, 3, 3, 0, 2, 2, 1, 3, 3, 0, 2, 2, 1, 3, 3, 0, 2, 2, 1, 3, 3, 0, 2, 2, 1, 3, 3, 0, 2, 2, 1, 3, 3, 0, 2, 2, 0, 3, 3, 1, 2, 2, 0, 3, 3, 1, 2, 2, 0, 3, 3, 1, 2, 2, 0, 3, 3, 1, 2, 2, 0, 3, 3, 1, 2, 2, 0, 3, 3, 1, 2, 2, 0, 1],
    [1, 3, 3, 0, 2, 2, 1, 3, 3, 0, 2, 2, 1, 3, 3, 0, 2, 2, 1, 3, 3, 0, 2, 2, 1, 3, 3, 0, 2, 2, 1, 3, 3, 0, 2, 2, 2, 3, 3, 1, 2, 2, 0, 3, 3, 1, 2, 2, 0, 3, 3, 1, 2, 2, 0, 3, 3, 1, 2, 2, 0, 3, 3, 1, 2, 2, 0, 3, 3, 1, 2, 2, 0, 3],
    [0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 3, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3, 1, 3, 1, 1],
    [0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 2, 3, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3],
    [3, 3, 0, 2, 2, 0, 3, 3, 0, 3, 1, 2, 2, 1, 2, 2, 1, 3, 1],
    [3, 0, 3, 0, 2, 0, 3, 0, 2, 0, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3]]

def relatorWord (i : Fin 16) : Word Bool := (relatorCodes i).map decode

/-- The replay words are literally the sixteen source words in the free group. -/
theorem mk_relatorWord : ∀ i, FreeGroup.mk (relatorWord i) = relator i := by
  intro i
  fin_cases i <;>
    simp only [relator, relationValue, baseValue, gapCommutator, normalize,
      leftWord, rightWord, commutatorElement_def, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Fin.isValue, Bool.false_eq_true, ↓reduceIte,
      FreeGroup.of, FreeGroup.mul_mk, FreeGroup.inv_mk, FreeGroup.pow_mk] <;>
    apply congrArg FreeGroup.mk <;> decide +kernel

theorem eval_relatorWord {G : Type*} [Group G] (x y : G) (i : Fin 16) :
    eval (letter x y) (relatorWord i) = relationValue x y i := by
  rw [eval, mk_relatorWord, relator, map_relationValue]
  simp [letter]

theorem relatorWord_valid (i : Fin 16) : eval generator (relatorWord i) = 1 := by
  have he : letter (generator false) (generator true) = generator := by
    funext b
    cases b <;> rfl
  rw [← he, eval_relatorWord]
  exact generator_relations i

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
