module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.ElementaryComparison
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Words
import Mathlib.Tactic.FinCases
/-!
# Selecting the Rudvalis four-group row

The first catalogue row is cyclic of order two. Every row from index two
onwards contains five explicit elements, distinguished by their images of
point zero in the existing degree-4060 permutation action. Hence only row
one can be a four-group. This needs neither a new group-order computation
nor exact orders for the other catalogue rows.

The cached elementary permutations are compared with the original words by
`ElementaryComparison`; the order-two fact comes from `Max6Normalizers.Words`.
All underlying ATLAS data and attribution remain in `LocalCover.Data` and
`SylowOvergroups.Definitions`. The source application is Aschbacher--Smith,
15.3.43, printed p.1140, with the sporadic list in 1.1.5(3)(f), p.502.
-/

open Subgroup Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate
namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.RankOneRows
private theorem zero_card_le : Nat.card (elementary 0) ≤ 2 := by
  change Nat.card (closure {elementaryGenerator 0}) ≤ 2
  rw [← zpowers_eq_closure, Nat.card_zpowers,
    Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.elementary_zero_order]

private def fiveWords : Fin 5 → Model :=
  ![1, elementaryGenerator 0, elementaryGenerator 1,
    elementaryGenerator 0 * elementaryGenerator 1, elementaryGenerator 2]

private def fivePerms : Fin 5 → Equiv.Perm (Fin 4060) :=
  ![1, elementaryPermutation 0, elementaryPermutation 1,
    elementaryPermutation 0 * elementaryPermutation 1, elementaryPermutation 2]

private theorem five_eq (i : Fin 5) : fivePerms i = modelSubgroup.subtype (fiveWords i) := by
  fin_cases i <;> simp only [fivePerms, fiveWords, elementaryPermutation_eq] <;> rfl

private theorem five_separated : Function.Injective (fun i => fivePerms i 0) := by
  decide +kernel

private theorem five_mem (i : Fin 5) : fiveWords i ∈ elementary 2 := by
  have h0 : elementaryGenerator 0 ∈ elementary 2 := subset_closure (by simp)
  have h1 : elementaryGenerator 1 ∈ elementary 2 := subset_closure (by simp)
  have h2 : elementaryGenerator 2 ∈ elementary 2 := subset_closure (by simp)
  fin_cases i
  · exact (elementary 2).one_mem
  · exact h0
  · exact h1
  · exact (elementary 2).mul_mem h0 h1
  · exact h2

/-- Five explicit distinct elements certify nontriviality and exclude order four. -/
public theorem five_le_card_elementary_two : 5 ≤ Nat.card (elementary 2) := by
  let f : Fin 5 → elementary 2 := fun i => ⟨fiveWords i, five_mem i⟩
  have hf : Function.Injective f := by
    intro i j h
    apply five_separated
    simpa only [five_eq] using congrArg
      (fun z : elementary 2 => modelSubgroup.subtype z.val 0) h
  simpa using Nat.card_le_card_of_injective f hf

/-- The only catalogue row that can have order four is the marked plane. -/
public theorem index_eq_one_of_card_four (i : Fin 6) (hcard : Nat.card (elementary i) = 4) : i = 1 := by
  have hlarge (j : Fin 6) (hle : elementary 2 ≤ elementary j) :
      5 ≤ Nat.card (elementary j) := five_le_card_elementary_two.trans
        (Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))
  fin_cases i
  · change Nat.card (elementary 0) = 4 at hcard
    have := zero_card_le
    omega
  · rfl
  · change Nat.card (elementary 2) = 4 at hcard
    have := five_le_card_elementary_two
    omega
  · have hl := hlarge 3 (closure_mono (by simp [Set.subset_def]))
    change Nat.card (elementary 3) = 4 at hcard
    omega
  · have hl := hlarge 4 (closure_mono (by simp [Set.subset_def]))
    change Nat.card (elementary 4) = 4 at hcard
    omega
  · have hl := hlarge 5 (closure_mono (by simp [Set.subset_def]))
    change Nat.card (elementary 5) = 4 at hcard
    omega
end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.RankOneRows
