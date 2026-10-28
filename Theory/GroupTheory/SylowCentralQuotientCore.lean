module

public import Theory.GroupTheory.PCoreCentralQuotientImage

/-!
# A Sylow subgroup abelian modulo a central subgroup

In a finite group of characteristic p, a Sylow p-subgroup whose derived
subgroup is central is the p-core. In the central quotient its image
centralizes the image of the p-core, so self-centralization puts the
whole Sylow image in that core image. The central kernel already lies
in the p-core, and the assertion lifts.

Source application: Aschbacher–Smith, Lemma 13.9.7, printed p.971,
with the actual common centralizer and denominator ⟨t,z⟩.
-/

namespace Sylow
open Subgroup

/-- A Sylow subgroup abelian modulo a central subgroup equals the p-core
when that core is self-centralizing. -/
public theorem eq_pCore_of_commutator_le_central
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ center G)
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (hcomm : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ Z) :
    (S : Subgroup G) = pCore p G := by
  let q := QuotientGroup.mk' Z
  have hZQ : Z ≤ pCore p G := (hZ.trans (center_le_centralizer _)).trans hc
  have hQS : pCore p G ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  have hab : ⁅(S : Subgroup G).map q, (S : Subgroup G).map q⁆ = ⊥ := by
    rw [← map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q, QuotientGroup.ker_mk'] using hcomm
  have himage : (S : Subgroup G).map q ≤ (pCore p G).map q :=
    ((commutator_eq_bot_iff_le_centralizer.mp hab).trans
      (centralizer_le (map_mono hQS))).trans
        (centralizer_image_pCore_le_of_central_quotient Z hZ hc)
  apply le_antisymm _ hQS
  have hpre := map_le_iff_le_comap.mp himage
  rwa [comap_map_eq_self (show q.ker ≤ pCore p G by
    simpa only [q, QuotientGroup.ker_mk'] using hZQ)] at hpre

end Sylow
