module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Data

/-!
# Ordered-basis witnesses for the max4 eight action

The two permutations already certified on the eight words have an orbit of
168 ordered bases. Breadth-first search supplies a word for each basis;
`wordFor_spec` checks every witness against the literal multiplication table.
No matrix arithmetic or unverified group-order calculation is used here.

The generator actions and multiplication table retain the ATLAS attribution
in `Max4.NormalEight`. See `source/generate.py` for witness generation.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightAction
open Janko4.LocalStructure.SymmetricLinear.NormalEight

/-- Right conjugation by a word, at the level of the eight indices. -/
def wordAction : List Bool → Fin 8 → Fin 8
  | [], i => i
  | b :: w, i => wordAction w (if b then actionY i else actionX i)

/-- Independence of three indices in the literal elementary-eight table. -/
def IsBasis (a b c : Fin 8) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ b ≠ a ∧ c ≠ 0 ∧ c ≠ a ∧ c ≠ b ∧ c ≠ productIndex a b

instance (a b c : Fin 8) : Decidable (IsBasis a b c) := inferInstanceAs
  (Decidable (a ≠ 0 ∧ b ≠ 0 ∧ b ≠ a ∧ c ≠ 0 ∧ c ≠ a ∧ c ≠ b ∧ c ≠ productIndex a b))

/-- A short word for each ordered basis; nonbases receive the empty word. -/
def wordFor : Fin 8 → Fin 8 → Fin 8 → List Bool :=
  ![![![[], [], [], [], [], [], [], []],
      ![[], [], [], [], [], [], [], []],
      ![[], [], [], [], [], [], [], []],
      ![[], [], [], [], [], [], [], []],
      ![[], [], [], [], [], [], [], []],
      ![[], [], [], [], [], [], [], []],
      ![[], [], [], [], [], [], [], []],
      ![[], [], [], [], [], [], [], []]],
    ![![[], [], [], [], [], [], [], []],
      ![[], [], [], [], [], [], [], []],
      ![[], [], [], [], [true, true, true, false, true], [], [true, true, false, true, false, true, true, true, false, true, false, true], [true, true, false, true, false, true, false, true, true, false]],
      ![[], [], [false], [], [], [true, true, true, false, true, false], [true, false, true, false, true, false, true, true, false, true, false, true], [true, true, false, true, false, true, false, true, true]],
      ![[], [], [false, true, true, true, false, true], [], [], [true, true, true, false, true, false, true, true, true, false, true], [true, false, true, false, true, true, false, true, false], [true, false, true, false, true, true, true, false]],
      ![[], [], [], [false, true, true, true, false, true, false], [false, true, true, true, false, true, false, true, true, true, false, true], [], [true, false, true, false, true, true, false, true], [true, false, true, false, true, true, true]],
      ![[], [], [false, true, true, false, true, false, true, true, true, false, true, false, true], [false, true, false, true, false, true, false, true, true, false, true, false, true], [false, true, false, true, false, true, true, false, true, false], [false, true, false, true, false, true, true, false, true], [], []],
      ![[], [], [false, true, true, false, true, false, true, false, true, true, false], [false, true, true, false, true, false, true, false, true, true], [false, true, false, true, false, true, true, true, false], [false, true, false, true, false, true, true, true], [], []]],
    ![![[], [], [], [], [], [], [], []],
      ![[], [], [], [true, false, true, false, true, true, false, true, false, true, false, true, false], [true, true, true, false, true, false, true, false, true, true, true, false], [], [false, true, false, true, false, true, true, false, true, false, true], [false, true, false, true, true, true, false]],
      ![[], [], [], [], [], [], [], []],
      ![[], [true, false, true, false, true, false, true, true, false, true, false, true, true], [], [], [false, true], [true, true, false, true, false, true, false, true, true, true], [], [true, true, true, false, true, false, true]],
      ![[], [false, true, true, true, false, true, false, true, false, true, true, true, false], [], [true], [], [false, true, true, true, false, true, false, true, false, true, false], [true, false, true, true, false], []],
      ![[], [], [], [false, true, true, false, true, false, true, false, true, true, true], [true, true, true, false, true, false, true, false, true, false], [], [false, true, false, true, false, true, true, true, false, true], [false, true, false, true, false]],
      ![[], [true, false, true, false, true, true, false, true, false, true], [], [], [false, true, false, true, true, false], [true, false, true, false, true, true, true, false, true], [], [true, true, true, false, true, false, true, false, true, true, false]],
      ![[], [true, false, true, true, true, false], [], [false, true, true, true, false, true, false, true], [], [true, false, true, false], [false, true, true, true, false, true, false, true, false, true, true, false], []]],
    ![![[], [], [], [], [], [], [], []],
      ![[], [], [true, false, true, false, true, true, false, true, false, true, false, true], [], [], [true, true, true, false, true, false, true, false, true, true, true], [true, false, true, false, true, true, true, false, true, false, true], [false, true, false, true, true, true]],
      ![[], [true, false, true, false, true, true, true, false, true, false, true, true], [], [], [true, true, false, true, false, true, false, true, true, true, false], [false, true, false], [], [true, true, true, false, true, false, true, false]],
      ![[], [], [], [], [], [], [], []],
      ![[], [], [false, true, true, false, true, false, true, false, true, true, true, false], [], [], [true, true, true, false, true, false, true, false, true], [false, true, false, true, false, true, true, true, false, true, false], [false, true, false, true]],
      ![[], [false, true, true, true, false, true, false, true, false, true, true, true], [true, false], [], [false, true, true, true, false, true, false, true, false, true], [], [true, false, true, true], []],
      ![[], [true, false, true, false, true, true, false, true, false, true, false], [], [], [true, false, true, false, true, true, true, false, true, false], [false, true, false, true, true], [], [true, true, true, false, true, false, true, false, true, true]],
      ![[], [true, false, true, true, true], [false, true, true, true, false, true, false, true, false], [], [true, false, true], [], [false, true, true, true, false, true, false, true, false, true, true], []]],
    ![![[], [], [], [], [], [], [], []],
      ![[], [], [true, false, true, false, true, true, false, true, false, true, true], [], [], [true, false, true, true, true, false, true, false, true, false, true, false], [false, true, false, true, true, false, true], [true, false, true, false, true, false, true, true, false]],
      ![[], [false, true, false, true, false, true, true, false, true, false, true, true], [], [false, true, false, true, true, false, true, false, true, false, true, false], [], [false, true, false, true, true, true, false, true], [true, false, true, false, true, false, true, true, true, false, true, false], []],
      ![[], [], [true, false, true, true, false, true, false, true, false, true, false], [], [], [true, true, true, false, true, false, true, true], [false, true, true], [true, true, false, true, false, true, false]],
      ![[], [], [], [], [], [], [], []],
      ![[], [false, true, false, true, true, true, false, true, false, true, false, true, false], [true, false, true, true, true, false, true], [false, true, true, true, false, true, false, true, true], [], [], [], [true, false, true, false, true]],
      ![[], [true, false, true, true, false, true], [false, true, false, true, false, true, false, true, true, true, false, true, false], [true, true], [], [], [], [true, true, false, true, false, true, true, true, false]],
      ![[], [false, true, false, true, false, true, false, true, true, false], [], [false, true, true, false, true, false, true, false], [], [false, true, false, true, false, true], [false, true, true, false, true, false, true, true, true, false], []]],
    ![![[], [], [], [], [], [], [], []],
      ![[], [], [], [true, false, true, true, true, false, true, false, true, true], [true, false, true, true, true, false, true, false, true, false, true], [], [false, true, false, true, true, false, true, false], [true, false, true, false, true, false, true, true]],
      ![[], [], [], [true, false, true, true, false, true, false, true, false, true], [true, false, true, true, false, true, false, true, true], [], [false, true, true, false], [true, true, false, true, false, true]],
      ![[], [false, true, false, true, true, true, false, true, false, true, true], [false, true, false, true, true, false, true, false, true, false, true], [], [false, true, false, true, true, true, false, true, false], [], [true, false, true, false, true, false, true, true, true, false, true], []],
      ![[], [false, true, false, true, true, true, false, true, false, true, false, true], [false, true, false, true, true, false, true, false, true, true], [true, false, true, true, true, false, true, false], [], [], [], [true, false, true, false, true, false]],
      ![[], [], [], [], [], [], [], []],
      ![[], [true, false, true, true, false, true, false], [true, true, false], [false, true, false, true, false, true, false, true, true, true, false, true], [], [], [], [true, true, false, true, false, true, true, true]],
      ![[], [false, true, false, true, false, true, false, true, true], [false, true, true, false, true, false, true], [], [false, true, false, true, false, true, false], [], [false, true, true, false, true, false, true, true, true], []]],
    ![![[], [], [], [], [], [], [], []],
      ![[], [], [true, true, true, false], [true, true, true], [true, true, false, true, false, true, true, true, false, true, false], [true, true, false, true, false, true, true, true, false, true], [], []],
      ![[], [false, true, true, true, false], [], [], [true, true, false, true, false, true, false, true, false], [true, false, true, false, true, false, true, true, false, true], [], [true, true, true, false, true, false, true, true, true, false]],
      ![[], [false, true, true, true], [], [], [true, false, true, false, true, false, true, true, false, true, false], [true, true, false, true, false, true, false, true], [], [true, true, true, false, true, false, true, true, true]],
      ![[], [false, true, true, false, true, false, true, true, true, false, true, false], [false, true, true, false, true, false, true, false, true, false], [false, true, false, true, false, true, false, true, true, false, true, false], [], [], [], [false, true, false, true, false, true, true, false]],
      ![[], [false, true, true, false, true, false, true, true, true, false, true], [false, true, false, true, false, true, false, true, true, false, true], [false, true, true, false, true, false, true, false, true], [], [], [], [false, true, false, true, false, true, true]],
      ![[], [], [], [], [], [], [], []],
      ![[], [], [false, true, true, true, false, true, false, true, true, true, false], [false, true, true, true, false, true, false, true, true, true], [true, false, true, false, true, true, false], [true, false, true, false, true, true], [], []]],
    ![![[], [], [], [], [], [], [], []],
      ![[], [], [true, false, true, true, false, true, false, true], [true, false, true, true, false, true, false, true, false], [true, true, false, true], [true, true, false, true, false], [], []],
      ![[], [false, true, false, true, true, false, true, false, true], [], [true, false, true, true, true, false, true, false, true, true, true], [], [true, false, true, false, true, false, true, true, true], [false, true, false, true, true, true, false, true, false, true, false], []],
      ![[], [false, true, false, true, true, false, true, false, true, false], [false, true, false, true, true, true, false, true, false, true, true, true], [], [true, false, true, false, true, false, true, true, true, false], [], [false, true, false, true, true, true, false, true, false, true], []],
      ![[], [false, true, true, false, true], [], [false, true, false, true, false, true, false, true, true, true, false], [], [true, true, false, true, false, true, true], [false, true, false, true, false, true, false, true, false], []],
      ![[], [false, true, true, false, true, false], [false, true, false, true, false, true, false, true, true, true], [], [false, true, true, false, true, false, true, true], [], [false, true, false, true, false, true, false, true], []],
      ![[], [], [true, false, true, true, true, false, true, false, true, false], [true, false, true, true, true, false, true, false, true], [true, false, true, false, true, false, true, false], [true, false, true, false, true, false, true], [], []],
      ![[], [], [], [], [], [], [], []]]]

/-- Checked coverage of every possible ordered basis by the two actual actions. -/
theorem wordFor_spec : ∀ a b c : Fin 8, IsBasis a b c →
    wordAction (wordFor a b c) 1 = a ∧
    wordAction (wordFor a b c) 2 = b ∧
    wordAction (wordFor a b c) 3 = c := by
  decide +kernel

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightAction
