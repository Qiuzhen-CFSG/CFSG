module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Abel

/-!
# Six source words for the cubic G₂(3) extension

These are the six words of the ATLAS presentation of G₂(3). This module
defines the presented group; its identification with the octonion model is
a separate obligation. The last word has exponent sums `(24, 8)`. Multiplying
it by the first word, the sixth power of the second, and the inverse square
of the third gives a word with zero exponent sums. This corrected word lies
in the free group's derived subgroup and will detect the cubic kernel.

Source: R. A. Wilson, S. J. Nickerson and J. N. Bray, *ATLAS of Finite Group
Representations*, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/G23G1-P1,
retrieved 9 October 2026. The source commutator is `x⁻¹ y⁻¹ x y`.
The downloadable BBox file computes the fifth word but omits its final
identity test; all six displayed relations are retained here. This is data
transcription, not a port of code from the local ATLAS project.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.Presentation

def sourceCommutator {H : Type*} [Group H] (x y : H) : H :=
  x⁻¹ * y⁻¹ * x * y

/-- The six displayed ATLAS relators, indexed from zero. -/
def word {H : Type*} [Group H] (a b : H) : Fin 6 → H :=
  ![a ^ 2, b ^ 3, (a * b) ^ 13, sourceCommutator a b ^ 13,
    (a * b) ^ 2 * sourceCommutator a b ^ 4 * (a * b) ^ 3 *
      sourceCommutator a (b * a * b) ^ 3,
    (((a * b) ^ 3 * (a * b⁻¹)) ^ 2 * (a * b) ^ 2 * (a * b⁻¹) ^ 2) ^ 2]

theorem map_word {H K : Type*} [Group H] [Group K] (f : H →* K)
    (a b : H) (i : Fin 6) : f (word a b i) = word (f a) (f b) i := by
  fin_cases i <;> simp [word, sourceCommutator]

/-- Correct the exponent sums without changing evaluation when the first
three words evaluate to one. -/
def defectWord {H : Type*} [Group H] (a b : H) : H :=
  word a b 5 * word a b 0 * word a b 1 ^ 6 * (word a b 2 ^ 2)⁻¹

theorem map_defectWord {H K : Type*} [Group H] [Group K] (f : H →* K)
    (a b : H) : f (defectWord a b) = defectWord (f a) (f b) := by
  simp only [defectWord, map_mul, map_inv, map_pow, map_word]

theorem defectWord_eq_last {H : Type*} [Group H] (a b : H)
    (h0 : word a b 0 = 1) (h1 : word a b 1 = 1) (h2 : word a b 2 = 1) :
    defectWord a b = word a b 5 := by
  simp [defectWord, h0, h1, h2]

theorem defectWord_mem_commutator {H : Type*} [Group H] (a b : H) :
    defectWord a b ∈ commutator H := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_defectWord]
  simp only [defectWord, word, Matrix.cons_val_zero]
  apply Additive.ofMul.injective
  let x : Additive (Abelianization H) := Additive.ofMul (Abelianization.of a)
  let y : Additive (Abelianization H) := Additive.ofMul (Abelianization.of b)
  change 2 • (2 • (3 • (x + y) + (x + -y)) + 2 • (x + y) + 2 • (x + -y)) +
    2 • x + 6 • (3 • y) + -(2 • (13 • (x + y))) = 0
  abel

abbrev Free := FreeGroup Bool

def relator : Fin 6 → Free := word (FreeGroup.of false) (FreeGroup.of true)

abbrev Presented := PresentedGroup (Set.range relator)

def generator (b : Bool) : Presented := PresentedGroup.of b

def toPresented : Free →* Presented := PresentedGroup.mk (Set.range relator)

theorem toPresented_surjective : Function.Surjective toPresented :=
  PresentedGroup.mk_surjective _

@[simp] theorem toPresented_relator (i : Fin 6) : toPresented (relator i) = 1 :=
  PresentedGroup.one_of_mem ⟨i, rfl⟩

def defect : Free := defectWord (FreeGroup.of false) (FreeGroup.of true)

theorem defect_mem_commutator : defect ∈ commutator Free :=
  defectWord_mem_commutator _ _

@[simp] theorem toPresented_defect : toPresented defect = 1 := by
  change toPresented (relator 5 * relator 0 * relator 1 ^ 6 * (relator 2 ^ 2)⁻¹) = 1
  simp

/-- Evaluate the source generators after proving all six relations. -/
def hom {H : Type*} [Group H] (a b : H) (h : ∀ i, word a b i = 1) :
    Presented →* H :=
  PresentedGroup.toGroup (f := fun x => if x then b else a) (by
    rintro _ ⟨i, rfl⟩
    simpa only [relator, map_word, FreeGroup.lift_apply_of, Bool.false_eq_true,
      reduceIte] using h i)

@[simp] theorem hom_generator {H : Type*} [Group H] (a b : H)
    (h : ∀ i, word a b i = 1) (x : Bool) :
    hom a b h (generator x) = if x then b else a :=
  PresentedGroup.toGroup.of _

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.Presentation
