module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.SourceActions.GeneratorA
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.SourceActions.GeneratorB

/-!
# Exact Fi23 generator actions in the packed source coordinates

The two numerical maps agree pointwise with the original cycle-decoded
permutations. Checked character lists connect the original strings to explicit
cycles; disjointness reduces evaluation to the checked action on each cycle
and the fixed complement. Inverse-cycle evaluation preserves the published
right-action to left-action conversion in `CycleEncoding`.

These equalities discharge the two source-map premises of
`exists_generator_comparison_of_pointwise_certificates`. The remaining ambient
word intertwinings are independent; `SourceActions.Comparison` gives that
specialized consumer.

Source: ATLAS F23G1-p31671B0.g1/.g2, retained with attribution and hashes in
`AtlasCarriers/source/`; GLS3 Table 5.3v and
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, around line 1053.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate
open Fi23.CentralizerSection.KernelCertificate
open Fi23.CentralizerSection.KernelCertificate.FixedLetterCheck
open SourceActionCheck

/-- The first exact cycle-decoded generator agrees with the packed source map. -/
theorem generatorA_apply_eq_sourceA :
    ∀ i : Fin 31671, Sporadic.Fischer.Fi23.generatorA i = sourceA i := by
  intro i
  rw [← fastA_eq]
  exact cyclesInv_eq_of_tests sourceA cyclesA maskA cyclesA_certificate
    sourceA_cycle_actions sourceA_fixed_complement i

/-- The second exact cycle-decoded generator agrees with the packed source map. -/
theorem generatorB_apply_eq_sourceB :
    ∀ i : Fin 31671, Sporadic.Fischer.Fi23.generatorB i = sourceB i := by
  intro i
  rw [← fastB_eq]
  exact cyclesInv_eq_of_tests sourceB cyclesB maskB cyclesB_certificate
    sourceB_cycle_actions sourceB_fixed_complement i

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate
