module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.Model
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.ProjectiveComparison.ConcreteLifts.Words
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.ProjectiveComparison.LiftContract
import Mathlib.Tactic.FinCases

/-!
# Concrete Held lifts of the two projective generators

The literal words from `ConcreteLifts.Words` belong to the derived subgroup
of the 2A centralizer by their checked coprime triangle relations. The 42
point equations below certify their actual degree-2058 permutation actions
against the existing projective matrices' permutations. Labels are in the
projective-vector order of `Coordinates`, not sorted ambient-point order.
This supplies the finite `GeneratorLifts` contract with no extra hypotheses.

Source: GLS3 Table 5.3p and the cover conventions on pp.260–261. The retained
candidate words and inverse GAP permutations are in
`TwoA/CentralizerCertificate/Source/discovery.json`; the conversion preserves
word order. Original ATLAS attribution is in `Held/Model/Source/README.md`.
The assertions are checked on the actual words; stored permutations are
only discovery data.
-/

@[expose] public section

namespace Held.InvolutionFixedData.TwoA.ProjectiveComparison.ConcreteLifts
set_option maxRecDepth 4096

/-- The literal derived-subgroup lift of the first projective generator. -/
def liftA : derived := ⟨x, words_mem_derived.1⟩
/-- The literal derived-subgroup lift of the second projective generator. -/
def liftB : derived := ⟨y, words_mem_derived.2⟩

/-- The first word acts by `permA` on the 21 projective labels. -/
theorem x_action (i : Fin 21) :
    representation x.val (pointLabel i) = pointLabel (permA i) := by
  fin_cases i <;> decide +kernel

/-- The second word acts by `permB` on the 21 projective labels. -/
theorem y_action (i : Fin 21) :
    representation y.val (pointLabel i) = pointLabel (permB i) := by
  fin_cases i <;> decide +kernel

end Held.InvolutionFixedData.TwoA.ProjectiveComparison.ConcreteLifts

namespace Held.InvolutionFixedData.TwoA.ProjectiveComparison

/-- The actual Held words discharge the projective generator-lift contract. -/
theorem generator_lifts : GeneratorLifts :=
  ⟨ConcreteLifts.liftA, ConcreteLifts.liftB, ConcreteLifts.x_action, ConcreteLifts.y_action⟩

end Held.InvolutionFixedData.TwoA.ProjectiveComparison
