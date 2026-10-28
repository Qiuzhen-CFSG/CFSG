module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterTwo0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterTwo1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterTwo2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterTwo3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterTwo4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterTwo5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterTwo6
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterTwo7
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelData
import Mathlib.Tactic.FinCases

/-!
# The explicit subgroup after two suffix points

The generators are actual permutations with checked inverse tables. This module
defines their closure and proves that it fixes the preceding base points. Its
relationship to the preceding group's stabilizer is a separate obligation.
These definitions are shared endpoints for the Schreier certificates proving
the Fi23 seven-point bound, used for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerData

def afterTwoGenerator : Fin 8 → Equiv.Perm (Fin 31671)
  | 0 => AfterTwo0.permutation
  | 1 => AfterTwo1.permutation
  | 2 => AfterTwo2.permutation
  | 3 => AfterTwo3.permutation
  | 4 => AfterTwo4.permutation
  | 5 => AfterTwo5.permutation
  | 6 => AfterTwo6.permutation
  | 7 => AfterTwo7.permutation

def afterTwo : Subgroup (Equiv.Perm (Fin 31671)) :=
  Subgroup.closure (Set.range afterTwoGenerator)

theorem afterTwoGenerator_fixes_1 (i : Fin 8) :
    afterTwoGenerator i 1 = 1 := by
  fin_cases i
  · exact AfterTwo0.fixes_1
  · exact AfterTwo1.fixes_1
  · exact AfterTwo2.fixes_1
  · exact AfterTwo3.fixes_1
  · exact AfterTwo4.fixes_1
  · exact AfterTwo5.fixes_1
  · exact AfterTwo6.fixes_1
  · exact AfterTwo7.fixes_1

theorem afterTwo_fixes_1 {p : Equiv.Perm (Fin 31671)}
    (hp : p ∈ afterTwo) : p 1 = 1 := by
  induction hp using Subgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact afterTwoGenerator_fixes_1 i
  | one => rfl
  | mul p q _ _ hp hq =>
    change p (q 1) = 1
    rw [hq, hp]
  | inv p _ hp =>
    apply p.injective
    change p (p.symm 1) = p 1
    rw [p.apply_symm_apply, hp]

theorem afterTwoGenerator_fixes_13 (i : Fin 8) :
    afterTwoGenerator i 13 = 13 := by
  fin_cases i
  · exact AfterTwo0.fixes_13
  · exact AfterTwo1.fixes_13
  · exact AfterTwo2.fixes_13
  · exact AfterTwo3.fixes_13
  · exact AfterTwo4.fixes_13
  · exact AfterTwo5.fixes_13
  · exact AfterTwo6.fixes_13
  · exact AfterTwo7.fixes_13

theorem afterTwo_fixes_13 {p : Equiv.Perm (Fin 31671)}
    (hp : p ∈ afterTwo) : p 13 = 13 := by
  induction hp using Subgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact afterTwoGenerator_fixes_13 i
  | one => rfl
  | mul p q _ _ hp hq =>
    change p (q 13) = 13
    rw [hq, hp]
  | inv p _ hp =>
    apply p.injective
    change p (p.symm 13) = p 13
    rw [p.apply_symm_apply, hp]

theorem afterTwoGenerator_fixes_27 (i : Fin 8) :
    afterTwoGenerator i 27 = 27 := by
  fin_cases i
  · exact AfterTwo0.fixes_27
  · exact AfterTwo1.fixes_27
  · exact AfterTwo2.fixes_27
  · exact AfterTwo3.fixes_27
  · exact AfterTwo4.fixes_27
  · exact AfterTwo5.fixes_27
  · exact AfterTwo6.fixes_27
  · exact AfterTwo7.fixes_27

theorem afterTwo_fixes_27 {p : Equiv.Perm (Fin 31671)}
    (hp : p ∈ afterTwo) : p 27 = 27 := by
  induction hp using Subgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact afterTwoGenerator_fixes_27 i
  | one => rfl
  | mul p q _ _ hp hq =>
    change p (q 27) = 27
    rw [hq, hp]
  | inv p _ hp =>
    apply p.injective
    change p (p.symm 27) = p 27
    rw [p.apply_symm_apply, hp]

theorem afterTwoGenerator_fixes_40 (i : Fin 8) :
    afterTwoGenerator i 40 = 40 := by
  fin_cases i
  · exact AfterTwo0.fixes_40
  · exact AfterTwo1.fixes_40
  · exact AfterTwo2.fixes_40
  · exact AfterTwo3.fixes_40
  · exact AfterTwo4.fixes_40
  · exact AfterTwo5.fixes_40
  · exact AfterTwo6.fixes_40
  · exact AfterTwo7.fixes_40

theorem afterTwo_fixes_40 {p : Equiv.Perm (Fin 31671)}
    (hp : p ∈ afterTwo) : p 40 = 40 := by
  induction hp using Subgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact afterTwoGenerator_fixes_40 i
  | one => rfl
  | mul p q _ _ hp hq =>
    change p (q 40) = 40
    rw [hq, hp]
  | inv p _ hp =>
    apply p.injective
    change p (p.symm 40) = p 40
    rw [p.apply_symm_apply, hp]

theorem afterTwoGenerator_fixes_46 (i : Fin 8) :
    afterTwoGenerator i 46 = 46 := by
  fin_cases i
  · exact AfterTwo0.fixes_46
  · exact AfterTwo1.fixes_46
  · exact AfterTwo2.fixes_46
  · exact AfterTwo3.fixes_46
  · exact AfterTwo4.fixes_46
  · exact AfterTwo5.fixes_46
  · exact AfterTwo6.fixes_46
  · exact AfterTwo7.fixes_46

theorem afterTwo_fixes_46 {p : Equiv.Perm (Fin 31671)}
    (hp : p ∈ afterTwo) : p 46 = 46 := by
  induction hp using Subgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact afterTwoGenerator_fixes_46 i
  | one => rfl
  | mul p q _ _ hp hq =>
    change p (q 46) = 46
    rw [hq, hp]
  | inv p _ hp =>
    apply p.injective
    change p (p.symm 46) = p 46
    rw [p.apply_symm_apply, hp]

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerData
