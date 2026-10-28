module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Generator0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Generator1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Generator2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Generator3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Generator4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Generator5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.GeneratorAgreement.Generator6
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Reduction
import Mathlib.Tactic.FinCases

/-!
# Agreement of all seven third-stage Fi23 generators

Each packed permutation equals the unchanged literal cycle-decoded generator.
The block certificates check the original string decoding, disjoint cycle
supports, inverse-cycle action, and fixed complement. Thus the stabilizer
reduction can use `KernelData.intermediate` with no generator-comparison premise.
The independent Schreier transition certificates remain explicit.

Source: ATLAS F23G1-p31671B0; GLS3 Table 5.3u and the Fischer paragraph in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, near line 1042.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection

namespace KernelUpperThird

/-- The packed candidates are exactly the original cycle-decoded permutations. -/
theorem packedGenerator_eq (i : Fin 7) : packedGenerator i = KernelData.generator i := by
  fin_cases i
  · exact GeneratorAgreement.permutation0_eq
  · exact GeneratorAgreement.permutation1_eq
  · exact GeneratorAgreement.permutation2_eq
  · exact GeneratorAgreement.permutation3_eq
  · exact GeneratorAgreement.permutation4_eq
  · exact GeneratorAgreement.permutation5_eq
  · exact GeneratorAgreement.permutation6_eq

end KernelUpperThird

/-- Discharges the generator agreement premise of the third stabilizer step.
The parent assembly must still supply the independent transition identities. -/
theorem third_stabilizer_le_of_transitions
    (hTransitions : ∀ a, KernelUpperThird.Step a) :
    ∀ p ∈ KernelUpperData.second, p 27 = 27 → p ∈ KernelData.intermediate :=
  third_stabilizer_le_of_certificates KernelUpperThird.packedGenerator_eq hTransitions

end Sporadic.Fischer.Fi23.CentralizerSection
