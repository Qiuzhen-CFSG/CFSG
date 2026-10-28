module

public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.LeftSupport.Commutators
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.Tactic.FinCases

/-!
# Perfectness of the concrete J₃ centralizer candidate

The certified commutator words put every literal generator in the derived
subgroup. Closure then proves perfectness. This supplies the perfectness
premise for the conjugated left support in the three-cover construction,
without using an assumed centralizer shape or ambient simplicity.
Source: GLS3, Table 5.3h, printed p.269.
-/

namespace Sporadic.Janko3.ThreeCoverConfig.LeftSupportCertificate
open Theory.GroupTheory TwoLocal
open scoped commutatorElement

/-- The fixed word-generated centralizer candidate is perfect. -/
public theorem centralizerCandidate_perfect : Group.IsPerfect centralizerCandidate := by
  have hletter (i : Fin 6) : commutatorLetter centralizerGenerator i ∈
      ⁅centralizerCandidate, centralizerCandidate⁆ := by
    have h23 := Subgroup.commutator_mem_commutator
      (centralizerGenerator_mem 2) (centralizerGenerator_mem 3)
    have h24 := Subgroup.commutator_mem_commutator
      (centralizerGenerator_mem 2) (centralizerGenerator_mem 4)
    have h34 := Subgroup.commutator_mem_commutator
      (centralizerGenerator_mem 3) (centralizerGenerator_mem 4)
    fin_cases i
    · exact h23
    · exact h24
    · exact h34
    · exact Subgroup.inv_mem _ h23
    · exact Subgroup.inv_mem _ h24
    · exact Subgroup.inv_mem _ h34
  have hword (w : List (Fin 6)) : evalWord (commutatorLetter centralizerGenerator) w ∈
      ⁅centralizerCandidate, centralizerCandidate⁆ := by
    induction w with
    | nil => exact Subgroup.one_mem _
    | cons i w ih => exact Subgroup.mul_mem _ (hletter i) ih
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm
  · exact (Subgroup.commutator_le_sup _ _).trans (sup_idem _).le
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    rw [centralizerGenerator_word]
    exact hword _

end Sporadic.Janko3.ThreeCoverConfig.LeftSupportCertificate
