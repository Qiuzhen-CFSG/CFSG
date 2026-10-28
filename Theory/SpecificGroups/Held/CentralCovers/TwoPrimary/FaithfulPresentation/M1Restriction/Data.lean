module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.Generators
public import Theory.GroupTheory.CosetWordCertificate

/-!
# A candidate finite presentation on the marked M₁ generators

The twelve words are frozen from GAP's multistage presentation discovery on
`[x, x^(y²), x^(y⁻²)]` in the retained ATLAS permutation model. They define an
independent abstract group. Neither their vanishing in the original Held
presentation nor finiteness of this new presentation is assumed or proved here.

The three squares and the fifth power of the product of the last two generators
are proved from the original source in `SourceRelations`. The remaining word
identities and the cardinal bound have separate certificate contracts.

See `source/README.md`, `source/extract.g` and the frozen `source/levels.json`.
The model generator conversion inverts each GAP permutation, so words retain
GAP multiplication order. All letters in these twelve relators are positive.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
open Subgroup.CosetWordCertificate

/-- Literal positive-generator sequences, with zero-based generator indices. -/
def relationIndices : Fin 12 → List (Fin 3)
  | 0 => [2, 2]
  | 1 => [0, 0]
  | 2 => [1, 1]
  | 3 => [2, 1, 2, 1, 2, 1, 2, 1, 2, 1]
  | 4 => [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
  | 5 => [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2]
  | 6 => [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0]
  | 7 => [2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 2, 1, 0, 1]
  | 8 => [0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 1, 0, 1, 0, 2, 1, 2]
  | 9 => [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2]
  | 10 => [2, 1, 0, 2, 1, 2, 1, 0, 2, 0, 2, 1, 0, 2, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2,
      0, 1, 2, 1]
  | 11 => [1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1,
      2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2]

/-- Signed words for the common checked word-evaluation interface. -/
def relationLetters (i : Fin 12) : Word (Fin 3) :=
  (relationIndices i).map (fun a => (a, true))

def localRelator (i : Fin 12) : FreeGroup (Fin 3) := FreeGroup.mk (relationLetters i)

/-- The auxiliary group defined by exactly the twelve frozen relators. -/
abbrev LocalPresentation := PresentedGroup (Set.range localRelator)

/-- The required identities are equations in the original abstract presentation. -/
def LiftedRelations : Prop := ∀ i, eval liftedGenerator (relationLetters i) = 1

/-- The finite abstract upper-bound contract. -/
def LocalPresentationBound : Prop :=
  Finite LocalPresentation ∧ Nat.card LocalPresentation ≤ 1958400

/-- The concrete lower-bound contract uses the actual marked subgroup of Held. -/
def ConcreteLowerBound : Prop := 1958400 ≤ Nat.card concreteSubgroup

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
