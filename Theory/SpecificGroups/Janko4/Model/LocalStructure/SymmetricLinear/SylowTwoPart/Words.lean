module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Definitions
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Fifteen words in the intrinsic max4 seed normal closure

The words below are products of the first sixteen terms of the already
defined alternating conjugation sequence. Their memberships in the relative
normal closure are carried by their types. `binaryProduct` is an explicit
candidate injection from fifteen binary choices to that normal closure.
Its injectivity is a separate matrix certificate obligation.

The proposed ordering comes from elimination of the literal matrices in the
published characteristic-two coordinates. Reproduction data are retained in
`SylowTwoPart/source`; that computation is not a Lean proof of injectivity.
Source matrices and word-program provenance: `Janko4.Model.Data` and
`SymmetricLinear.Model`.
-/

@[expose] public section

namespace Janko4.LocalStructure.SymmetricLinear.SylowTwoPart
open CharacteristicTwo

/-- A term of the literal alternating sequence, with its proved membership. -/
def q (k : ℕ) : seedNormalClosure :=
  ⟨seedConjugate k, seedConjugate_mem_normalClosure k⟩

def word00 : seedNormalClosure := q 0
def word01 : seedNormalClosure := q 2 * word00
def word02 : seedNormalClosure := q 3 * word00
def word03 : seedNormalClosure := q 4 * word00
def word04 : seedNormalClosure := q 5 * word01
def word05 : seedNormalClosure := q 6 * word02
def word06 : seedNormalClosure := q 7 * word03
def word07 : seedNormalClosure := q 8 * word00 * word02
def word08 : seedNormalClosure := q 9 * word00 * word02 * word07 * word04
def word09 : seedNormalClosure := q 10 * word07
def word10 : seedNormalClosure := q 11 * word00 * word07 * word09
def word11 : seedNormalClosure := q 12 * word07 * word05 * word04 * word09
def word12 : seedNormalClosure := q 13 * word00 * word09 * word08 * word06
def word13 : seedNormalClosure :=
  q 14 * word03 * word01 * word07 * word05 * word09 * word08 * word06
def word14 : seedNormalClosure :=
  q 15 * word02 * word01 * word07 * word05 * word04 * word09 * word08 * word06 *
    word13 * word10

/-- The fifteen words, ordered by their proposed first nonidentity entries. -/
def pivotWord : Fin 15 → seedNormalClosure :=
  ![word00, word02, word03, word01, word07, word05, word04, word09,
    word08, word11, word06, word12, word13, word10, word14]

/-- An actual word of the normal closure for each sequence of fifteen bits. -/
def binaryProduct (bits : Fin 15 → Fin 2) : seedNormalClosure :=
  (List.ofFn (fun i => pivotWord i ^ (bits i).val)).prod

/-- The explicit injection certificate supplies the normal-closure lower bound. -/
theorem seed_card_lower_of_binaryProduct_injective
    (h : Function.Injective binaryProduct) : 2 ^ 15 ≤ Nat.card seedNormalClosure := by
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective _ h

end Janko4.LocalStructure.SymmetricLinear.SylowTwoPart
