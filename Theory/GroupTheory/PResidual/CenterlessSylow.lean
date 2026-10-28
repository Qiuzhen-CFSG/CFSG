module

public import Theory.GroupTheory.PResidual.FixedNormalCenter

/-!
# Sylow centralizers of the residual in a center-free group

In a finite center-free group, the centralizer of the p-residual inside
any Sylow p-subgroup is trivial. This centralizer is normalized by the
Sylow subgroup and centralized by the residual, so it is normal in their
join, the whole group. A nontrivial normal p-subgroup fixed by the
residual would contain a nontrivial ambient central element.

Source application: Aschbacher–Smith 13.2.11(1), printed p.881.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- No nonidentity element of the Sylow subgroup centralizes the
p-residual of a center-free finite group. -/
theorem sylow_inf_centralizer_pResidual_eq_bot_of_center_eq_bot
    {p : ℕ} [Fact p.Prime] (T : Sylow p G) (hz : center G = ⊥) :
    (T : Subgroup G) ⊓ centralizer (pResidual p G : Set G) = ⊥ := by
  let A := (T : Subgroup G) ⊓ centralizer (pResidual p G : Set G)
  have hRA : pResidual p G ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mp inf_le_right
  have hTn : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hn : A.Normal := normalizer_eq_top_iff.mp (top_unique (by
    have hgn : pResidual p G ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) :=
      sup_le (hRA.trans (Subgroup.centralizer_le_normalizer _)) hTn
    rwa [pResidual_sup_sylow_eq_top T] at hgn))
  let := hn
  by_contra hne
  obtain ⟨a, _, hane, hac⟩ := exists_nontrivial_center_mem_normal_of_residual_centralizes
    T A (T.isPGroup'.to_le inf_le_left) hne hRA
  exact hane (mem_bot.mp (hz ▸ hac))

end Subgroup
