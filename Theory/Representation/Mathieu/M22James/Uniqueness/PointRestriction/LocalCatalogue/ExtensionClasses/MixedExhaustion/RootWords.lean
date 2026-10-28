module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.MixedExhaustion.Data

/-!
# Root words and the two mixed templates

Every elementary transvection over F₄ is given as a word of length at most ten
in x₀₁(1), x₀₁(ω), and the cyclic coordinate permutation. Both the group word
and the cross-block value of each of the two templates are checked directly.
These are finite matrix identities on specified words; they do not assume or
prove global cocycle laws for the templates. Combined with the elimination
certificate, they give the required comparison on every transvection.

Source context: James (1973), Lemma 8.3; Aschbacher–Smith H.12.1, pp.393–394.
-/

@[expose] public noncomputable section

open Matrix
namespace Representation.SL3FourLocalCatalogue.ExtensionExhaustion
open SL3FourNaturalDual ExtensionCoordinates

def rootWord (i j : Fin 3) (a : Fin 4) : List (Fin 3) :=
  ![![![[], [], [], []], ![[], [0], [1], [0, 1]], ![[], [0, 2, 0, 2, 2, 0, 2, 0, 2, 2], [0, 2, 1, 2, 2, 0, 2, 1, 2, 2], [1, 2, 1, 2, 2, 1, 2, 1, 2, 2]]], ![![[], [2, 0, 2, 0, 2, 2, 0, 2, 0, 2], [2, 0, 2, 1, 2, 2, 0, 2, 1, 2], [2, 1, 2, 1, 2, 2, 1, 2, 1, 2]], ![[], [], [], []], ![[], [2, 0, 2, 2], [2, 1, 2, 2], [2, 0, 1, 2, 2]]], ![![[], [2, 2, 0, 2], [2, 2, 1, 2], [2, 2, 0, 1, 2]], ![[], [0, 2, 2, 0, 2, 0, 2, 2, 0, 2], [0, 2, 2, 1, 2, 0, 2, 2, 1, 2], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2]], ![[], [], [], []]]] i j a

lemma scalar_surjective : Function.Surjective scalar := by decide +kernel

lemma rootWord_value : ∀ (i j : Fin 3) (hij : i ≠ j) (a : Fin 4),
    word (rootWord i j a) = Matrix.SpecialLinearGroup.transvection hij (scalar a) := by
  decide +kernel

/-- The first template has the published value on every root word. -/
lemma rootWord_symmetric : ∀ (i j : Fin 3) (hij : i ≠ j) (a : Fin 4),
    wordMap (rootWord i j a) symmetricInputs =
      symmetricMatrix (Matrix.SpecialLinearGroup.transvection hij (scalar a)) := by
  decide +kernel

/-- The second template has the published value on every root word. -/
lemma rootWord_dual : ∀ (i j : Fin 3) (hij : i ≠ j) (a : Fin 4),
    wordMap (rootWord i j a) dualInputs =
      dualSymmetricMatrix (Matrix.SpecialLinearGroup.transvection hij (scalar a)) := by
  decide +kernel

end Representation.SL3FourLocalCatalogue.ExtensionExhaustion
