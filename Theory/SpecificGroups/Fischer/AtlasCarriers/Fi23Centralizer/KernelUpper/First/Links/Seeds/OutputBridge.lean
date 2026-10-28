module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Seeds.Certificate
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Seeds.Paths

/-!
# Finite word comparisons imply the actual Fi23 seed output identities

The checked source and target words are the literal tree representatives.
Comparing their actions avoids unfolding the well-founded representative
definition or the long shared subgroup words during finite checks. The target
representative is cancelled as a genuine permutation; no normality or changed
action convention is used.

Source: ATLAS F23G1-p31671B0, inverse-cycle convention; GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links.Seeds
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

/-- These eleven pointwise finite equations have no subgroup-membership premise. -/
def OutputEquations : Prop := ∀ i : Fin 11, ∀ x : Fin 31671,
  wordRun (targetWord i) (table (output i) x) = sourceA (wordRun (sourceWord i) x)

theorem outputs_of_word_equations (h : OutputEquations) : Outputs := by
  intro i x
  have hx := h i x
  rw [wordRun_eq, targetWord_eq, wordRun_eq, sourceWord_eq,
    ← generatorA_apply_eq_sourceA] at hx
  apply (representative (generatorA (seedLetter i))).injective
  rw [hx]
  change generatorA (representative (seedLetter i) x) =
    (representative (generatorA (seedLetter i)))
      ((representative (generatorA (seedLetter i))).symm
        (generatorA (representative (seedLetter i) x)))
  exact ((representative (generatorA (seedLetter i))).apply_symm_apply _).symm

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links.Seeds
