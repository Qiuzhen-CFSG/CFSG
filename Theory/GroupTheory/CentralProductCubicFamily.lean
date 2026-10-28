module
public import Theory.GroupTheory.CentralProductCubicContainment
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! A finite central product inherits the two-factor cubic-centralizer
containment theorem. The same cubic normalizes every factor, so induction
selects one factor containing the original perfect subgroup. This supplies
the actual component-family step in source2.4.25, printed p542. -/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem perfect_subgroup_le_member_of_cubic_centralizer
    (F : Set (Subgroup G))
    (hc : Set.Pairwise F (fun K C => K ≤ centralizer (C : Set G)))
    (L : Subgroup G) [Group.IsPerfect L] (hL0 : L ≠ ⊥) (hL : L ≤ sSup F)
    (hcyc : ∀ P : Sylow 3 L, IsCyclic P) (hres : primeToResidual 3 L = ⊤)
    (b : G) (hb : orderOf b = 3)
    (hbn : ∀ K ∈ F, b ∈ normalizer (K : Set G))
    (hbL : b ∈ centralizer (L : Set G)) (hr : primeRank 3 G ≤ 2) :
    ∃ K ∈ F, L ≤ K := by
  classical
  have hfin := Set.toFinite F
  induction F, hfin using Set.Finite.induction_on with
  | empty => simp only [sSup_empty] at hL; exact (hL0 (le_bot_iff.mp hL)).elim
  | @insert K F hKF hfin ih =>
    have hcF : Set.Pairwise F (fun K C : Subgroup G => K ≤ centralizer (C : Set G)) :=
      hc.mono (Set.subset_insert _ _)
    have hbF : ∀ C ∈ F, b ∈ normalizer (C : Set G) :=
      fun C hC => hbn C (Set.mem_insert_of_mem _ hC)
    have hKC : K ≤ centralizer ((sSup F : Subgroup G) : Set G) := by
      apply le_centralizer_iff.mp
      exact sSup_le fun C hC => le_centralizer_iff.mp
        (hc (Set.mem_insert _ _) (Set.mem_insert_of_mem _ hC) (fun he => hKF (he ▸ hC)))
    have hbC : b ∈ normalizer ((sSup F : Subgroup G) : Set G) := by
      have h : zpowers b ≤ normalizer ((sSup F : Subgroup G) : Set G) := by
        rw [sSup_eq_iSup']
        exact (le_iInf fun C : F => zpowers_le.mpr (hbF C C.property)).trans
          (iInf_normalizer_le_normalizer_iSup _)
      exact h (mem_zpowers b)
    rw [sSup_insert] at hL
    rcases perfect_subgroup_le_factor_of_cubic_centralizer K (sSup F) L hKC hL
      hcyc hres b hb (hbn K (Set.mem_insert _ _)) hbC hbL hr with hK | hF
    · exact ⟨K,Set.mem_insert _ _,hK⟩
    · obtain ⟨C,hC,hLC⟩ := ih hcF hF hbF
      exact ⟨C,Set.mem_insert_of_mem _ hC,hLC⟩
end Theory.GroupTheory
