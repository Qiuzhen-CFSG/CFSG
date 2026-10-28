module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Evaluation

/-!
# Independent finite action contracts for the Fi23 loop witnesses

These predicates separate the shared-register comparison from the numerical
A and B action squares. The assembly in `First.Loops` must prove every premise.
They assert exact equations on the retained ATLAS action, with no subgroup
recognition, order, or external computation assumed.

Source: ATLAS F23G1-p31671B0 and GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops

/-- Remaining equations for the 695 enumerated first-generator loops. -/
def AActions : Prop := ∀ i : Fin 722, i.val < 695 → ∀ x, ActionCheck i x

/-- Remaining equations for the 27 enumerated second-generator loops. -/
def BActions : Prop := ∀ i : Fin 722, 695 ≤ i.val → ∀ x, ActionCheck i x

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops
