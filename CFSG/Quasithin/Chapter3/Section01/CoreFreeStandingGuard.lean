module

public import CFSG.Quasithin.Chapter3.Section01.StandingGuard
public import Theory.GroupTheory.SylowCoreRestriction

/-!
# A core-free local pair supplies the source standing guard

Suppose two overgroups of the same Sylow two-subgroup have nontrivial
two-cores but their join has trivial two-core. Extend each to a maximal
two-local. They are distinct, since the core of a common maximal overgroup
would lie in the Sylow subgroup and in the core-free join. Consequently
every selected maximal two-local has an actual outside maximal overgroup.

Source: the standing assumption after Aschbacher--Smith 2.1.1, p.518.
The F.9.1 source pair supplies these hypotheses directly.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3
variable {G : Type*} [Group G] [Finite G]

/-- Two source local groups with core-free join have distinct maximal overgroups. -/
theorem exists_two_distinct_of_core_free_pair (T : Sylow 2 G) (A B : Subgroup G)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (hA : pCore 2 A ≠ ⊥) (hB : pCore 2 B ≠ ⊥)
    (hAB : pCore 2 (A ⊔ B : Subgroup G) = ⊥) :
    ∃ M N : Subgroup G, IsMaximalTwoLocal M ∧ IsMaximalTwoLocal N ∧
      A ≤ M ∧ B ≤ N ∧ (T : Subgroup G) ≤ M ∧ (T : Subgroup G) ≤ N ∧ M ≠ N := by
  obtain ⟨M,hM,hAM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot A hA
  obtain ⟨N,hN,hBN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot B hB
  refine ⟨M,N,hM,hN,hAM,hBN,hTA.trans hAM,hTB.trans hBN,?_⟩
  intro he
  have hcore : pCore 2 M ≠ ⊥ := by
    intro hb
    apply Chapter1.mem_H_of_isTwoLocal hM.1
    change (pCore 2 M).map M.subtype = ⊥
    rw [hb, Subgroup.map_bot]
  exact not_le_of_sylow_le_of_core_eq_bot T (hTA.trans le_sup_left) hAB hcore
    (sup_le hAM (he.symm ▸ hBN))

/-- The pair supplies the genuine outside guard for any selected maximal local. -/
theorem hasMaximalOutside_of_core_free_pair (T : Sylow 2 G) (A B : Subgroup G)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (hA : pCore 2 A ≠ ⊥) (hB : pCore 2 B ≠ ⊥)
    (hAB : pCore 2 (A ⊔ B : Subgroup G) = ⊥)
    (M : Subgroup G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M) :
    HasMaximalOutside T M := by
  obtain ⟨N,P,hN,hP,_,_,hTN,hTP,hNP⟩ :=
    exists_two_distinct_of_core_free_pair T A B hTA hTB hA hB hAB
  by_cases he : N = M
  · exact hasMaximalOutside_of_two_distinct hM hP hTM hTP
      (fun hPM => hNP (he.trans hPM.symm))
  · exact hasMaximalOutside_of_two_distinct hM hN hTM hTN he

end CFSG.Quasithin.Chapter3
