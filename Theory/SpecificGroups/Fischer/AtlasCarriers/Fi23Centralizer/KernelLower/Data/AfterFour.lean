module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterFour0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterFour1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterFour2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterFour3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterFour4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterFour5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelData
import Mathlib.Tactic.FinCases

/-!
# The explicit subgroup after four suffix points

The generators are actual permutations with checked inverse tables. This module
defines their closure and proves that it fixes the preceding base points. Its
relationship to the preceding group's stabilizer is a separate obligation.
These definitions are shared endpoints for the Schreier certificates proving
the Fi23 seven-point bound, used for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerData

def afterFourGenerator : Fin 6 → Equiv.Perm (Fin 31671)
  | 0 => AfterFour0.permutation
  | 1 => AfterFour1.permutation
  | 2 => AfterFour2.permutation
  | 3 => AfterFour3.permutation
  | 4 => AfterFour4.permutation
  | 5 => AfterFour5.permutation

def afterFour : Subgroup (Equiv.Perm (Fin 31671)) :=
  Subgroup.closure (Set.range afterFourGenerator)

theorem afterFourGenerator_square (i : Fin 6) :
    afterFourGenerator i * afterFourGenerator i = 1 := by
  fin_cases i
  · exact AfterFour0.square_eq_one
  · exact AfterFour1.square_eq_one
  · exact AfterFour2.square_eq_one
  · exact AfterFour3.square_eq_one
  · exact AfterFour4.square_eq_one
  · exact AfterFour5.square_eq_one

theorem afterFourGenerator_fixes_1 (i : Fin 6) :
    afterFourGenerator i 1 = 1 := by
  fin_cases i
  · exact AfterFour0.fixes_1
  · exact AfterFour1.fixes_1
  · exact AfterFour2.fixes_1
  · exact AfterFour3.fixes_1
  · exact AfterFour4.fixes_1
  · exact AfterFour5.fixes_1

theorem afterFour_fixes_1 {p : Equiv.Perm (Fin 31671)}
    (hp : p ∈ afterFour) : p 1 = 1 := by
  induction hp using Subgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact afterFourGenerator_fixes_1 i
  | one => rfl
  | mul p q _ _ hp hq =>
    change p (q 1) = 1
    rw [hq, hp]
  | inv p _ hp =>
    apply p.injective
    change p (p.symm 1) = p 1
    rw [p.apply_symm_apply, hp]

theorem afterFourGenerator_fixes_13 (i : Fin 6) :
    afterFourGenerator i 13 = 13 := by
  fin_cases i
  · exact AfterFour0.fixes_13
  · exact AfterFour1.fixes_13
  · exact AfterFour2.fixes_13
  · exact AfterFour3.fixes_13
  · exact AfterFour4.fixes_13
  · exact AfterFour5.fixes_13

theorem afterFour_fixes_13 {p : Equiv.Perm (Fin 31671)}
    (hp : p ∈ afterFour) : p 13 = 13 := by
  induction hp using Subgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact afterFourGenerator_fixes_13 i
  | one => rfl
  | mul p q _ _ hp hq =>
    change p (q 13) = 13
    rw [hq, hp]
  | inv p _ hp =>
    apply p.injective
    change p (p.symm 13) = p 13
    rw [p.apply_symm_apply, hp]

theorem afterFourGenerator_fixes_27 (i : Fin 6) :
    afterFourGenerator i 27 = 27 := by
  fin_cases i
  · exact AfterFour0.fixes_27
  · exact AfterFour1.fixes_27
  · exact AfterFour2.fixes_27
  · exact AfterFour3.fixes_27
  · exact AfterFour4.fixes_27
  · exact AfterFour5.fixes_27

theorem afterFour_fixes_27 {p : Equiv.Perm (Fin 31671)}
    (hp : p ∈ afterFour) : p 27 = 27 := by
  induction hp using Subgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact afterFourGenerator_fixes_27 i
  | one => rfl
  | mul p q _ _ hp hq =>
    change p (q 27) = 27
    rw [hq, hp]
  | inv p _ hp =>
    apply p.injective
    change p (p.symm 27) = p 27
    rw [p.apply_symm_apply, hp]

theorem afterFourGenerator_fixes_40 (i : Fin 6) :
    afterFourGenerator i 40 = 40 := by
  fin_cases i
  · exact AfterFour0.fixes_40
  · exact AfterFour1.fixes_40
  · exact AfterFour2.fixes_40
  · exact AfterFour3.fixes_40
  · exact AfterFour4.fixes_40
  · exact AfterFour5.fixes_40

theorem afterFour_fixes_40 {p : Equiv.Perm (Fin 31671)}
    (hp : p ∈ afterFour) : p 40 = 40 := by
  induction hp using Subgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact afterFourGenerator_fixes_40 i
  | one => rfl
  | mul p q _ _ hp hq =>
    change p (q 40) = 40
    rw [hq, hp]
  | inv p _ hp =>
    apply p.injective
    change p (p.symm 40) = p 40
    rw [p.apply_symm_apply, hp]

theorem afterFourGenerator_fixes_46 (i : Fin 6) :
    afterFourGenerator i 46 = 46 := by
  fin_cases i
  · exact AfterFour0.fixes_46
  · exact AfterFour1.fixes_46
  · exact AfterFour2.fixes_46
  · exact AfterFour3.fixes_46
  · exact AfterFour4.fixes_46
  · exact AfterFour5.fixes_46

theorem afterFour_fixes_46 {p : Equiv.Perm (Fin 31671)}
    (hp : p ∈ afterFour) : p 46 = 46 := by
  induction hp using Subgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact afterFourGenerator_fixes_46 i
  | one => rfl
  | mul p q _ _ hp hq =>
    change p (q 46) = 46
    rw [hq, hp]
  | inv p _ hp =>
    apply p.injective
    change p (p.symm 46) = p 46
    rw [p.apply_symm_apply, hp]

theorem afterFourGenerator_fixes_63 (i : Fin 6) :
    afterFourGenerator i 63 = 63 := by
  fin_cases i
  · exact AfterFour0.fixes_63
  · exact AfterFour1.fixes_63
  · exact AfterFour2.fixes_63
  · exact AfterFour3.fixes_63
  · exact AfterFour4.fixes_63
  · exact AfterFour5.fixes_63

theorem afterFour_fixes_63 {p : Equiv.Perm (Fin 31671)}
    (hp : p ∈ afterFour) : p 63 = 63 := by
  induction hp using Subgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact afterFourGenerator_fixes_63 i
  | one => rfl
  | mul p q _ _ hp hq =>
    change p (q 63) = 63
    rw [hq, hp]
  | inv p _ hp =>
    apply p.injective
    change p (p.symm 63) = p 63
    rw [p.apply_symm_apply, hp]

theorem afterFourGenerator_fixes_66 (i : Fin 6) :
    afterFourGenerator i 66 = 66 := by
  fin_cases i
  · exact AfterFour0.fixes_66
  · exact AfterFour1.fixes_66
  · exact AfterFour2.fixes_66
  · exact AfterFour3.fixes_66
  · exact AfterFour4.fixes_66
  · exact AfterFour5.fixes_66

theorem afterFour_fixes_66 {p : Equiv.Perm (Fin 31671)}
    (hp : p ∈ afterFour) : p 66 = 66 := by
  induction hp using Subgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact afterFourGenerator_fixes_66 i
  | one => rfl
  | mul p q _ _ hp hq =>
    change p (q 66) = 66
    rw [hq, hp]
  | inv p _ hp =>
    apply p.injective
    change p (p.symm 66) = p 66
    rw [p.apply_symm_apply, hp]

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerData
