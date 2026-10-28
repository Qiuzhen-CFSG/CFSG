module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.AfterOne
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Packed
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterTwo
import Mathlib.Tactic.FinCases

/-!
# Word actions for the two suffix steps

The first source is the existing seven packed permutations; their agreement
with the literal `KernelData` generators is the independent
`KernelUpper.Third.GeneratorAgreement` contract. The second source is the four
literal `afterOne` generators. The second target is exactly the published
`KernelLowerData.afterTwo`. Signed words have proved membership in each target.
Source: ATLAS F23G1-p31671B0; GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair
open KernelLowerData

def afterTwoForward : Fin 8 → Fin 31671 → Fin 31671
  | 0 => AfterTwo0.forward
  | 1 => AfterTwo1.forward
  | 2 => AfterTwo2.forward
  | 3 => AfterTwo3.forward
  | 4 => AfterTwo4.forward
  | 5 => AfterTwo5.forward
  | 6 => AfterTwo6.forward
  | 7 => AfterTwo7.forward

def afterTwoBackward : Fin 8 → Fin 31671 → Fin 31671
  | 0 => AfterTwo0.backward
  | 1 => AfterTwo1.backward
  | 2 => AfterTwo2.backward
  | 3 => AfterTwo3.backward
  | 4 => AfterTwo4.backward
  | 5 => AfterTwo5.backward
  | 6 => AfterTwo6.backward
  | 7 => AfterTwo7.backward

theorem afterTwoForward_eq (i : Fin 8) (x : Fin 31671) :
    afterTwoForward i x = afterTwoGenerator i x := by
  fin_cases i <;> rfl

theorem afterTwoBackward_eq (i : Fin 8) (x : Fin 31671) :
    afterTwoBackward i x = (afterTwoGenerator i)⁻¹ x := by
  fin_cases i <;> rfl

namespace First

def signedGenerator (i : Fin 8) : Equiv.Perm (Fin 31671) :=
  if i.val < 4 then afterOneGenerator (Fin.ofNat 4 i.val)
  else (afterOneGenerator (Fin.ofNat 4 (i.val - 4)))⁻¹

def signedMap (i : Fin 8) : Fin 31671 → Fin 31671 :=
  if i.val < 4 then afterOneForward (Fin.ofNat 4 i.val)
  else afterOneBackward (Fin.ofNat 4 (i.val - 4))

theorem signedMap_eq (i : Fin 8) (x : Fin 31671) :
    signedMap i x = signedGenerator i x := by
  simp only [signedMap, signedGenerator]
  split
  · exact afterOneForward_eq _ _
  · exact afterOneBackward_eq _ _

theorem signedGenerator_mem (i : Fin 8) : signedGenerator i ∈ afterOne := by
  simp only [signedGenerator]
  split
  · exact Subgroup.subset_closure ⟨_, rfl⟩
  · exact afterOne.inv_mem (Subgroup.subset_closure ⟨_, rfl⟩)

end First

namespace Second

def signedGenerator (i : Fin 16) : Equiv.Perm (Fin 31671) :=
  if i.val < 8 then afterTwoGenerator (Fin.ofNat 8 i.val)
  else (afterTwoGenerator (Fin.ofNat 8 (i.val - 8)))⁻¹

def signedMap (i : Fin 16) : Fin 31671 → Fin 31671 :=
  if i.val < 8 then afterTwoForward (Fin.ofNat 8 i.val)
  else afterTwoBackward (Fin.ofNat 8 (i.val - 8))

theorem signedMap_eq (i : Fin 16) (x : Fin 31671) :
    signedMap i x = signedGenerator i x := by
  simp only [signedMap, signedGenerator]
  split
  · exact afterTwoForward_eq _ _
  · exact afterTwoBackward_eq _ _

theorem signedGenerator_mem (i : Fin 16) : signedGenerator i ∈ afterTwo := by
  simp only [signedGenerator]
  split
  · exact Subgroup.subset_closure ⟨_, rfl⟩
  · exact afterTwo.inv_mem (Subgroup.subset_closure ⟨_, rfl⟩)

end Second

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair
