module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Representatives
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Packed
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.Transitions
public import Theory.GroupAction.GeneratorStabilizerReduction

/-!
# The remaining finite identities for the third Fi23 prefix step

All orbit representatives, inverse transition maps, and fixation of the next
subgroup are checked independently. It remains to check the positive transition
identities on every letter and identify the seven packed generators with the
original cycle-decoded `KernelData.generator` permutations. The final theorem
below discharges inverse transitions algebraically and uses both certificates
with the literal source and target subgroups.

No group order, orbit-size theorem or stabilizer equality is assumed.
Source: ATLAS F23G1-p31671B0; GLS3 Table 5.3u and the Fischer paragraph of
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, near line 1042.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird
open KernelUpperData

/-- The displayed factor is already a proved member of the packed subgroup. -/
def factor (a : Fin 6) (r : Fin 693) : packedSubgroup :=
  ⟨wordValue signedGenerator (factorCode a r.val).1 (factorCode a r.val).2,
   wordValue_mem packedSubgroup signedGenerator signedGenerator_mem _ _⟩

def factorRun (a : Fin 6) (r : Fin 693) (x : Fin 31671) : Fin 31671 :=
  wordRun signedMap (factorCode a r.val).1 (factorCode a r.val).2 x

theorem factorRun_eq (a : Fin 6) (r : Fin 693) (x : Fin 31671) :
    factorRun a r x = (factor a r).val x :=
  wordRun_eq signedGenerator signedMap signedMap_eq _ _ _

/-- A concrete finite identity, with the exact numerical words and maps. -/
def Step (a : Fin 6) : Prop :=
  ∀ r : Fin 693, ∀ x : Fin 31671,
    secondMap a (representativeRun r x) =
      representativeRun (transitionForward a r) (factorRun a r x)

theorem step_eq (a : Fin 6) (h : Step a) (r : Fin 693) :
    secondGenerator a * representative r =
      representative (transition a r) * (factor a r).val := by
  apply Equiv.ext
  intro x
  simpa only [secondMap_eq, representativeRun_eq, factorRun_eq,
    Equiv.Perm.mul_apply, transition_apply] using h r x

/-- Positive identities give a full reduction, including all inverse steps. -/
def reduction (h : ∀ a, Step a) :
    Subgroup.GeneratorStabilizerReduction secondGenerator packedSubgroup
      (27 : Fin 31671) (Fin 693) :=
  Subgroup.GeneratorStabilizerReduction.ofPermutations secondGenerator packedSubgroup
    (27 : Fin 31671) representative 0 representative_initial transition factor
    (fun a r => step_eq a (h a) r) packedSubgroup_fixes representative_returns

/-- The packed group is compared with the unchanged literal target generators. -/
theorem packedSubgroup_le_intermediate
    (h : ∀ i, packedGenerator i = KernelData.generator i) :
    packedSubgroup ≤ KernelData.intermediate := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  rw [h i]
  exact Subgroup.subset_closure ⟨i, rfl⟩

end KernelUpperThird

/-- Conditional assembly of the third step. Its two remaining premises are
finite certificate obligations, and are not asserted source theorems. -/
theorem third_stabilizer_le_of_certificates
    (hGenerators : ∀ i, KernelUpperThird.packedGenerator i = KernelData.generator i)
    (hTransitions : ∀ a, KernelUpperThird.Step a) :
    ∀ p ∈ KernelUpperData.second, p 27 = 27 → p ∈ KernelData.intermediate := by
  intro p hp hfix
  apply KernelUpperThird.packedSubgroup_le_intermediate hGenerators
  exact (KernelUpperThird.reduction hTransitions).mem_next hp hfix

end Sporadic.Fischer.Fi23.CentralizerSection
