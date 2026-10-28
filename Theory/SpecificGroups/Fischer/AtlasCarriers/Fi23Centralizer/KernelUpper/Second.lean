module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.Transitions
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Second.Representatives
public import Theory.GroupAction.GeneratorStabilizerReduction

/-!
# Assembly of the second Fi23 prefix stabilizer step

The concrete orbit tree supplies representatives and bijective positive
transition maps. Tree and reverse-tree Schreier factors are already proved
trivial. This reduction consumes membership of the remaining factors for each
of the two literal first generators. Those two finite certificate obligations
are explicit; this module does not yet assert the unconditional containment.

The intended conclusion supplies exactly the second premise of
`prefix_stabilizer_le_intermediate_of_steps`, with no first-step assumption.
Source application: ATLAS F23G1-p31671B0 and GLS3 Table 5.3u, discussed in
`refs/KGroup/GLS3/Chapter5(sec3-).tex` near line 1042.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection
open SecondCertificate

/-- Actual consumer of the two remaining Schreier certificate families.
Final assembly must discharge both hypotheses before exporting
`second_stabilizer_le`. -/
theorem second_stabilizer_le_of_non_tree
    (h₀ : ∀ i, ¬ TreeEdge 0 i → schreier 0 i ∈ KernelUpperData.second)
    (h₁ : ∀ i, ¬ TreeEdge 1 i → schreier 1 i ∈ KernelUpperData.second) :
    ∀ p ∈ KernelUpperData.first, p 13 = 13 → p ∈ KernelUpperData.second := by
  have hm : ∀ a i, schreier a i ∈ KernelUpperData.second := by
    intro a
    fin_cases a
    · exact schreier_mem_of_non_tree 0 h₀
    · exact schreier_mem_of_non_tree 1 h₁
  let C := Subgroup.GeneratorStabilizerReduction.ofPermutations
    KernelUpperData.firstGenerator KernelUpperData.second (13 : Fin 31671)
    representative 0 representative_zero transition
    (fun a i => ⟨schreier a i, hm a i⟩)
    (by
      intro a i
      change KernelUpperData.firstGenerator a * representative i =
        representative (next a i) * schreier a i
      simp only [schreier, ← mul_assoc, mul_inv_cancel, one_mul])
    (fun k => (KernelUpperData.second_fixes k.property).2)
    representative_returns
  intro p hp hfix
  exact C.mem_next hp hfix

end Sporadic.Fischer.Fi23.CentralizerSection
