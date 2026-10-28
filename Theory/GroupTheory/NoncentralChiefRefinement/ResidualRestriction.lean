module

public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Sections
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Counting
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Transport

/-!
# Assembling a comparison after restriction of the actor

Intersect a complete chief series with a subgroup and refine each normal
interval. If its noncentral binary sections survive restriction, and a
noncentral binary section of the restricted actor has a noncentral chief
factor, each original counted factor contributes at least one. The proof
constructs a complete refinement and retains all the intersected terms.

The two action hypotheses below are explicit local obligations, not source
theorems. Their discharge for the two-residual is required before applying
this assembly unconditionally to Aschbacher–Smith 14.7.70, printed p.1074.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K] [Finite K]

/-- Local action survival gives the count comparison, with the actual
intersections and their chief refinement exhibited. This conditional assembly
does not assert that its action hypotheses hold for an arbitrary subgroup. -/
theorem ChiefSeries.exists_comparison_of_restriction_survival
    (s : ChiefSeries K) (R : Subgroup K) (h0 : s.head = ⊥) (h1 : s.last = ⊤)
    (hsection : ∀ i : Fin s.length,
      IsNoncentralTwo (s i.castSucc) (s i.succ) →
        IsNoncentralTwo (restrictNormalNode R (s i.castSucc)) (restrictNormalNode R (s i.succ)))
    (hrefine : ∀ t : ChiefSeries R, IsNoncentralTwo t.head t.last →
      ∃ j : Fin t.length, IsNoncentralTwo (t j.castSucc) (t j.succ)) :
    ∃ (t : ChiefSeries R) (ι : Fin (s.length + 1) →o Fin (t.length + 1)),
      (∀ i, t (ι i) = restrictNormalNode R (s i)) ∧
      ι 0 = 0 ∧ ι (Fin.last s.length) = Fin.last t.length ∧
      t.head = ⊥ ∧ t.last = ⊤ ∧ s.noncentralTwoCount ≤ t.noncentralTwoCount := by
  obtain ⟨t, ι, hi, hi0, hi1, hc⟩ :=
    (s.restrictionFiltration R).exists_refinement_counting_surviving_strata
      (fun i => IsNoncentralTwo (s i.castSucc) (s i.succ)) hsection hrefine
  refine ⟨t, ι, hi, hi0, hi1, ?_, ?_, ?_⟩
  · have h := hi 0
    rw [hi0] at h
    exact h.trans (by change restrictNormalNode R s.head = ⊥; rw [h0, restrictNormalNode_bot])
  · have h := hi (Fin.last s.length)
    rw [hi1] at h
    exact h.trans (by change restrictNormalNode R s.last = ⊤; rw [h1, restrictNormalNode_top])
  · rw [s.noncentralTwoCount_eq_sum]
    exact hc

end NoncentralChiefRefinement
