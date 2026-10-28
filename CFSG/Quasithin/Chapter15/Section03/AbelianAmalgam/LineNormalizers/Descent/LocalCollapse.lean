module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.Frattini
public import Theory.GroupTheory.LocalNormalizerUniqueness
/-!
# The local obstruction to a common normal residual

A nontrivial normal subgroup of a group of characteristic two has nontrivial
two-core: otherwise its intersection with the ambient two-core is trivial,
so it centralizes that core and must lie in it. The characteristic two-core
of a subgroup normalized by both `M` and `H` therefore puts both in a
two-local subgroup. Maximality of the two-local `M` contradicts `H ≰ M`.

This proves the obstruction from the actual local hypotheses. It does not
assume a common-normal-subgroup exclusion. Applying it to the source
`O^{2,3}` still requires proving that residual's equality and relative
normality in the two overgroups.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of Lemma 15.3.67, printed p.1154, PDF p.1171.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent
variable {G : Type*} [Group G]

private theorem normal_eq_bot_of_core_eq_bot (N : Subgroup G) [N.Normal]
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hN : pCore 2 N = ⊥) : N = ⊥ := by
  have hi : (pCore 2 G).subgroupOf N ≤ pCore 2 N :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  rw [hN] at hi
  have hinf : N ⊓ pCore 2 G = ⊥ := by
    have hm := congrArg (Subgroup.map N.subtype) (eq_bot_iff.mpr hi)
    simpa only [subgroupOf_map_subtype, Subgroup.map_bot, inf_comm] using hm
  have hcomm : ⁅N, pCore 2 G⁆ = ⊥ :=
    eq_bot_iff.mpr ((commutator_le_inf (H₁ := N) (H₂ := pCore 2 G)).trans_eq hinf)
  have hNQ := (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hc
  exact eq_bot_iff.mpr ((le_inf le_rfl hNQ).trans_eq hinf)

/-- Maximal two-locality and characteristic two kill a common normal subgroup. -/
theorem common_normal_eq_bot [Finite G] (M H D : Subgroup G)
    (hM : IsMaximalTwoLocal M)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hout : ¬ H ≤ M) (hDM : D ≤ M) (hDH : D ≤ H)
    (hDnM : (D.subgroupOf M).Normal) (hDnH : (D.subgroupOf H).Normal) : D = ⊥ := by
  let : (D.subgroupOf M).Normal := hDnM
  have hMN : M ≤ normalizer (D : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hDM).mp hDnM
  have hHN : H ≤ normalizer (D : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hDH).mp hDnH
  by_contra hD
  have hcore : pCore 2 D ≠ ⊥ := by
    intro hbot
    let e := subgroupOfEquivOfLe hDM
    have hcore' : pCore 2 (D.subgroupOf M) = ⊥ := by
      have hm := pCore_map_iso 2 e
      rw [hbot] at hm
      exact ((pCore 2 (D.subgroupOf M)).map_eq_bot_iff_of_injective e.injective).mp hm
    have he := normal_eq_bot_of_core_eq_bot (D.subgroupOf M) hchar hcore'
    have hm := congrArg (Subgroup.map M.subtype) he
    rw [map_subgroupOf_eq_of_le hDM, Subgroup.map_bot] at hm
    exact hD hm
  obtain ⟨L, hL, hNL⟩ := exists_twoLocal_overgroup_normalizer D (pCore 2 D)
    hcore pCore_isPGroup
  have hML : M ≤ L := hMN.trans hNL
  have he : M = L := hM.eq_of_le hL hML
  exact hout ((hHN.trans hNL).trans_eq he.symm)
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent
