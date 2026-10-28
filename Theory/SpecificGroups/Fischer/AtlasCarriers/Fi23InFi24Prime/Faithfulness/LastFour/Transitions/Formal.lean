module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Setup

/-!
# Transitions that follow from the words alone

Spanning-tree transitions have an empty factor and their representative is
literally the generator prepended to the preceding word. Identity-padding
transitions also have empty factors. Both kinds hold in the literal carrier
without any numerical check or comparison hypothesis. `formalEntry` selects
these 77 of the 244 entries, leaving 167 ambient equations to certify.

Source: the left-action Schreier tables in `LastFour/source/schreier.json`,
from ATLAS F24G1-p306936B0; see `LastFour/source/README.md`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions

/-- Number of genuine generators in a padded stage. -/
def generatorCount : Fin 5 → Nat
  | 0 => 4
  | 1 => 3
  | 2 => 2
  | 3 => 1
  | 4 => 0

theorem generator_padding (i : Fin 5) (a : Fin 4)
    (h : generatorCount i ≤ a.val) : LastFour.generator i a = 1 := by
  fin_cases i <;> fin_cases a <;> simp [generatorCount] at h <;> rfl

/-- Decidable word-level reasons that require no ambient computation. -/
def formalEntry (i : Fin 4) (a : Fin 4) (j : Fin (orbitSize i)) : Bool :=
  decide ((representativeWord i (transitionIndex i a j) = a :: representativeWord i j ∧
      factorWord i a j = []) ∨
    (transitionIndex i a j = j ∧ factorWord i a j = [] ∧
      generatorCount i.castSucc ≤ a.val))

/-- The selected entries are actual equalities in the original carrier. -/
theorem step_of_formalEntry (i : Fin 4) (a : Fin 4) (j : Fin (orbitSize i))
    (h : formalEntry i a j = true) :
    LastFour.generator i.castSucc a * representative i j =
      representative i (transitionIndex i a j) * factor i a j := by
  have hh := of_decide_eq_true h
  rcases hh with ⟨hr, hf⟩ | ⟨ht, hf, hg⟩
  · simp only [representative, factor, hr, hf, evaluate, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  · rw [generator_padding _ _ hg, ht]
    simp only [factor, hf, evaluate, List.map_nil, List.prod_nil, one_mul, mul_one]

/-- Checked count of transitions discharged by the formal argument. -/
theorem formalEntry_count :
    ((List.finRange 4).map fun i => ((List.finRange 4).map fun a =>
      ((List.finRange (orbitSize i)).filter (formalEntry i a)).length).sum).sum = 77 := by
  decide +kernel

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions
