module

public import CFSG.Quasithin.Chapter1.Section02.Adequate.Faithful
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients

/-!
# Restricting the local family to the Sylow stabilizer

The ambient two-core normalizes every C-component, by uniqueness of lifting
through a solvable quotient. Thus the original nontrivial two-core survives
when the Sylow actor S is replaced by N_S(B). The usual local Sylow
normalizer calculation supplies the Sylow condition, and subnormality
restricts the component to the smaller join.

This preserves all three clauses of the original local family, rather than
only its C-component clause. Source: Aschbacher--Smith 1.2.3 and A.3.11,
printed pp.505 and 46; applied in 10.2.3(4), printed p.747.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The original join's two-core lies in the Sylow stabilizer of its component. -/
theorem local_join_twoCore_le_sylow_stabilizer {S B : Subgroup G}
    (hB : B ∈ Chapter1.L G S) :
    (B ⊔ S).pCoreIn 2 ≤ S ⊓ normalizer (B : Set G) := by
  let H := B ⊔ S
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  have hcore : pCore 2 H ≤ normalizer (B.subgroupOf H : Set H) := by
    rw [← normalizer_cComponent_quotient hB.1 (pCore 2 H)]
    simpa only [q, QuotientGroup.ker_mk'] using
      MonoidHom.ker_le_comap q (normalizer ((B.subgroupOf H).map q : Set (H ⧸ pCore 2 H)))
  have hnorm : H.pCoreIn 2 ≤ normalizer (B : Set G) := by
    have hBH : B ≤ H := le_sup_left
    rw [← subgroupOf_normalizer_eq hBH] at hcore
    rintro x ⟨y, hy, rfl⟩
    exact hcore hy
  obtain ⟨P, hP⟩ := hB.2.1
  exact le_inf ((pCoreIn_le_sylow H P).trans hP.le) hnorm

/-- The full original local-family condition survives restriction to N_S(B). -/
theorem mem_L_sylow_stabilizer {S B : Subgroup G}
    (hB : B ∈ Chapter1.L G S) :
    B ∈ Chapter1.L G (S ⊓ normalizer (B : Set G)) := by
  have hcore : (B ⊔ S).pCoreIn 2 ≤
      (B ⊔ (S ⊓ normalizer (B : Set G))).pCoreIn 2 :=
    (le_inf ((local_join_twoCore_le_sylow_stabilizer hB).trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 (sup_le_sup_left inf_le_left B))
  exact ⟨ChapterA.Section03.localCComponents_antitone inf_le_left hB.1,
    Adequate.local_normalizer_isSylow hB,
    fun he => hB.2.2 (bot_unique (hcore.trans he.le))⟩

end CFSG.Quasithin.Chapter1.Section02
