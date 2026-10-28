module

public import Theory.SpecificGroups.Triality.BinarySevenPlane.Torus
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.MatrixRealization
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.RootConjugation.RootCurves

/-!
# Concrete Weyl words for the binary triality seven-plane

The three displayed words act on the literal twenty-four D₄ roots. Faithfulness
of the split Weyl realization lifts the checked permutation identities to the
actual Geck group. In particular both quaternion words are fixed by the
inner twist of graph-field action, with no torus correction.

Source: the nonsplit seven-torus normalizer at q = 2 (ATLAS, printed p.89),
with the explicit D₄ words and coordinate marking of the construction.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.BinarySevenPlane
open ConcreteBruhat ConcreteBruhat.MatrixRealization Parabolics
open PositiveCoordinates.SumExchangeData
noncomputable section
local notation "P" => binaryParameters 1 Nat.zero_lt_one

lemma prime_two : (P).prime = 2 := rfl

def word (l : List (Fin 4)) : SplitGroup P :=
  ((l.map (splitWeylGenerator P)).prod : splitWeylSubgroup P).val

def rootWord (l : List (Fin 4)) : rootWeylGroup := (l.map rootWeylGenerator).prod

def permWord : List (Fin 4) → Fin 24 → Fin 24
  | [], r => r
  | i::l, r => reflectionTable i (permWord l r)

lemma word_nil : word [] = 1 := rfl
lemma word_cons (i : Fin 4) (l) : word (i::l) = weylWord P i 1 * word l := rfl
lemma word_append (l m) : word (l++m) = word l * word m := by
  simp only [word, List.map_append, List.prod_append, Subgroup.coe_mul]
lemma rootAction_rootWord (l) (r) : rootAction (rootWord l) r = permWord l r := by
  induction l with
  | nil => simp [rootWord, permWord]
  | cons i l ih =>
    change rootAction (rootWeylGenerator i * rootWord l) r = _
    rw [map_mul, Equiv.Perm.mul_apply, rootAction_simple, ih]
    rfl
lemma word_eq {l m} (h : ∀ r, permWord l r = permWord m r) : word l = word m := by
  apply congrArg Subtype.val
  apply (splitWeylEquiv P prime_two).injective
  have he (l) : splitWeylEquiv P prime_two (l.map (splitWeylGenerator P)).prod = rootWord l := by
    induction l with
    | nil => exact map_one _
    | cons i l ih =>
      change splitWeylEquiv P prime_two (splitWeylGenerator P i * _) = rootWeylGenerator i * _
      rw [map_mul]
      exact congrArg₂ (· * ·) (splitWeylEquiv_generator P prime_two i) ih
  rw [he, he]
  apply rootAction_injective
  apply Equiv.ext
  intro r
  simpa only [rootAction_rootWord] using h r
lemma graphField_word (l) : graphFieldAutomorphism P (word l) =
    word (l.map typeD4DiagramPermutation) := by
  induction l with
  | nil => exact map_one _
  | cons i l ih =>
    simpa only [word_cons, List.map_cons, map_mul, graphField_weylWord, map_one] using
      congrArg (fun g => weylWord P (typeD4DiagramPermutation i) 1 * g) ih

def arms : SplitGroup P := word [0,2,3]
def twistWord : SplitGroup P := word [1,0,2,3,1,0,2,3]
def firstWord : SplitGroup P := word [1,0,2,1,0,3]
def secondWord : SplitGroup P := word [1,2,3,1,0,2]
lemma graphField_arms : graphFieldAutomorphism P arms = arms := by
  rw [arms, graphField_word]
  apply word_eq
  decide +kernel
lemma twist_first : twistWord * graphFieldAutomorphism P firstWord = firstWord * twistWord := by
  rw [firstWord, graphField_word, twistWord, ← word_append, ← word_append]
  apply word_eq
  decide +kernel
lemma twist_second : twistWord * graphFieldAutomorphism P secondWord = secondWord * twistWord := by
  rw [secondWord, graphField_word, twistWord, ← word_append, ← word_append]
  apply word_eq
  decide +kernel
lemma realizes_word (l) : Realizes P (word l) (rootWord l) := by
  induction l with
  | nil => exact realizes_one P
  | cons i l ih => exact realizes_mul (realizes_simple P prime_two i) ih

end
end Triality.Standard.BinarySevenPlane
