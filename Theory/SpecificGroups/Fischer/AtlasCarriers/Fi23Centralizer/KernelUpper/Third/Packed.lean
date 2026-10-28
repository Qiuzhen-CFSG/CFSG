module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Packed0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Packed1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Packed2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Packed3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Packed4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Packed5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Packed6
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Word
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic.FinCases

/-!
# The seven packed third-stage permutations

Each permutation has a checked inverse and fixes letter 27. The literal target
of the prefix theorem remains `KernelData.intermediate`; identifying these
packed permutations with its cycle-decoded generators is a separate obligation.
Signed words below provide subgroup members for the Schreier transitions.

Source: ATLAS F23G1-p31671B0; GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird

def packedGenerator : Fin 7 → Equiv.Perm (Fin 31671)
  | 0 => Packed0.permutation
  | 1 => Packed1.permutation
  | 2 => Packed2.permutation
  | 3 => Packed3.permutation
  | 4 => Packed4.permutation
  | 5 => Packed5.permutation
  | 6 => Packed6.permutation

def packedForward : Fin 7 → Fin 31671 → Fin 31671
  | 0 => Packed0.forward
  | 1 => Packed1.forward
  | 2 => Packed2.forward
  | 3 => Packed3.forward
  | 4 => Packed4.forward
  | 5 => Packed5.forward
  | 6 => Packed6.forward

def packedBackward : Fin 7 → Fin 31671 → Fin 31671
  | 0 => Packed0.backward
  | 1 => Packed1.backward
  | 2 => Packed2.backward
  | 3 => Packed3.backward
  | 4 => Packed4.backward
  | 5 => Packed5.backward
  | 6 => Packed6.backward

theorem packedForward_eq (i : Fin 7) (x : Fin 31671) :
    packedForward i x = packedGenerator i x := by
  fin_cases i <;> rfl

theorem packedBackward_eq (i : Fin 7) (x : Fin 31671) :
    packedBackward i x = (packedGenerator i)⁻¹ x := by
  fin_cases i <;> rfl

theorem packedGenerator_fixes (i : Fin 7) : packedGenerator i 27 = 27 := by
  fin_cases i
  · exact Packed0.fixes_27
  · exact Packed1.fixes_27
  · exact Packed2.fixes_27
  · exact Packed3.fixes_27
  · exact Packed4.fixes_27
  · exact Packed5.fixes_27
  · exact Packed6.fixes_27

/-- Positive letters 0–6 and inverse letters 7–13. -/
def signedGenerator (i : Fin 14) : Equiv.Perm (Fin 31671) :=
  if i.val < 7 then packedGenerator (Fin.ofNat 7 i.val)
  else (packedGenerator (Fin.ofNat 7 (i.val - 7)))⁻¹

def signedMap (i : Fin 14) : Fin 31671 → Fin 31671 :=
  if i.val < 7 then packedForward (Fin.ofNat 7 i.val)
  else packedBackward (Fin.ofNat 7 (i.val - 7))

theorem signedMap_eq (i : Fin 14) (x : Fin 31671) :
    signedMap i x = signedGenerator i x := by
  simp only [signedMap, signedGenerator]
  split
  · exact packedForward_eq _ _
  · exact packedBackward_eq _ _

def packedSubgroup : Subgroup (Equiv.Perm (Fin 31671)) :=
  Subgroup.closure (Set.range packedGenerator)

theorem signedGenerator_mem (i : Fin 14) : signedGenerator i ∈ packedSubgroup := by
  simp only [signedGenerator]
  split
  · exact Subgroup.subset_closure ⟨_, rfl⟩
  · exact packedSubgroup.inv_mem (Subgroup.subset_closure ⟨_, rfl⟩)

theorem packedSubgroup_fixes (p : packedSubgroup) : p.val 27 = 27 := by
  have hle : packedSubgroup ≤
      MulAction.stabilizer (Equiv.Perm (Fin 31671)) (27 : Fin 31671) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact packedGenerator_fixes i
  exact hle p.property

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird
