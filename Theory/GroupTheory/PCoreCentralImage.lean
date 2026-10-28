module
public import Theory.GroupTheory.PStar.ActionTools
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Normal Sylow images in p-perfect quotients

If a finite p-perfect group has a p-core of index prime to p, a normal
subgroup containing the commutator of that core with the group contains
the core itself. In the quotient the core becomes a central Sylow subgroup;
Burnside transfer and p-perfectness make the quotient a p'-group.

This transfer is used to identify the two residual cores in
Aschbacher–Smith, 14.7.20(3), printed p.1049.
-/

public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A central image of a normal Sylow subgroup vanishes in a p-perfect quotient. -/
theorem pCore_le_of_commutator_le_of_coprime_index
    (hG : IsPPerfect p G) (hindex : Nat.Coprime p (pCore p G).index)
    (N : Subgroup G) [N.Normal] (hc : ⁅pCore p G, (⊤ : Subgroup G)⁆ ≤ N) :
    pCore p G ≤ N := by
  let q := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  let S : Sylow p G := pCore_isPGroup.toSylow
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hindex)
  have hcentral : (pCore p G).map q ≤ center (G ⧸ N) := by
    apply commutator_top_right_eq_bot_iff_le_center.mp
    rw [← map_top_of_surjective q hq, ← map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q, QuotientGroup.ker_mk'] using hc
  have hcop : Nat.Coprime p (Nat.card (G ⧸ N)) :=
    Theory.GroupTheory.PStarAction.coprime_card_of_central_sylow
      (hG.of_surjective q hq) (S.mapSurjective hq) hcentral
  have hcard : Nat.card ((pCore p G).map q) = 1 :=
    ((pCore_isPGroup (p := p) (G := G)).map q).card_eq_or_dvd.resolve_right
      (fun hd => ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop)
        (hd.trans ((pCore p G).map q).card_subgroup_dvd_card))
  have he : (pCore p G).map q = ⊥ := eq_bot_of_card_eq _ hcard
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
end Subgroup
