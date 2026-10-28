module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.AfterOne0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.AfterOne1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.AfterOne2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.AfterOne3
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic.FinCases

/-!
# The four-generator subgroup after the first suffix point

The subgroup is defined by checked literal permutations fixing 40. Its
relationship to the preceding group's stabilizer is certified separately.
These four tables are the first output of `KernelLower/source/Generate.py`.
Source application: GLS3 Table 5.3u; retained ATLAS F23G1-p31671B0.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair

def afterOneGenerator : Fin 4 → Equiv.Perm (Fin 31671)
  | 0 => AfterOne0.permutation
  | 1 => AfterOne1.permutation
  | 2 => AfterOne2.permutation
  | 3 => AfterOne3.permutation

def afterOneForward : Fin 4 → Fin 31671 → Fin 31671
  | 0 => AfterOne0.forward
  | 1 => AfterOne1.forward
  | 2 => AfterOne2.forward
  | 3 => AfterOne3.forward

def afterOneBackward : Fin 4 → Fin 31671 → Fin 31671
  | 0 => AfterOne0.backward
  | 1 => AfterOne1.backward
  | 2 => AfterOne2.backward
  | 3 => AfterOne3.backward

theorem afterOneForward_eq (i : Fin 4) (x : Fin 31671) :
    afterOneForward i x = afterOneGenerator i x := by
  fin_cases i <;> rfl

theorem afterOneBackward_eq (i : Fin 4) (x : Fin 31671) :
    afterOneBackward i x = (afterOneGenerator i)⁻¹ x := by
  fin_cases i <;> rfl

def afterOne : Subgroup (Equiv.Perm (Fin 31671)) :=
  Subgroup.closure (Set.range afterOneGenerator)

theorem afterOneGenerator_fixes (i : Fin 4) : afterOneGenerator i 40 = 40 := by
  fin_cases i
  · exact AfterOne0.fixes_40
  · exact AfterOne1.fixes_40
  · exact AfterOne2.fixes_40
  · exact AfterOne3.fixes_40

theorem afterOne_fixes (p : afterOne) : p.val 40 = 40 := by
  have hle : afterOne ≤
      MulAction.stabilizer (Equiv.Perm (Fin 31671)) (40 : Fin 31671) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact afterOneGenerator_fixes i
  exact hle p.property

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair
