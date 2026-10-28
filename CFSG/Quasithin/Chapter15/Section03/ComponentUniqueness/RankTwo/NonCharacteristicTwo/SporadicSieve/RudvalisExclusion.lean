module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoModel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ModelAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ShadowBounds
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.TwoLocalOrder
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Excluding the Rudvalis component in the rank-two local configuration

Write H = I/C_I(L) and K = L⁺. The actual marking L/O₂(L) ≃ Ru identifies
K with the fixed degree-4060 carrier. Since I = LS and S⁺ is Sylow in H,
H/K is a two-group. The subgroup M_I⁺ has characteristic two, so the
Rudvalis local order obstruction makes its order indivisible by nine.
The full quotient Y₊⁺S⁺/O_{2,Φ}(Y₊⁺S⁺) ≃ S₃ × S₃ instead forces
36 to divide its order, giving the contradiction.

The two-extension argument intersects M_I⁺ with K and uses the normalizer
of that intersection's nontrivial intrinsic two-core. It discharges the
local coverage directly from the checked six-member elementary catalogue.
No automorphism classification or additional core premise is required.
The input retains every `ComponentSetup` and `LocalConfiguration` clause,
including relative normality and maximality subject to F* = O₂.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.41--42, printed p.1138, and 1.1.5(3f), printed pp.501--503;
GLS3 Table 5.3r, printed p.279.
-/

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.RudvalisExclusion
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] {I L M Y S : Subgroup G}
variable [(L.subgroupOf I).Normal]

private theorem component_quotient_isTwoGroup (d : ComponentSetup I L M Y S) :
    IsPGroup 2 (ComponentQuotient I L ⧸ componentImage I L L) := by
  obtain ⟨P, hP⟩ := d.quotient_local.sylow
  apply isPGroup_quotient_of_sup_eq_top (componentImage I L L)
    (componentImage I L S) (hP ▸ P.isPGroup')
  have hLI : L.subgroupOf I ⊔ S.subgroupOf I = ⊤ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le d.component_le,
      map_subgroupOf_eq_of_le (d.join_eq ▸ le_sup_right)]
    simpa only [← MonoidHom.range_eq_map, range_subtype] using d.join_eq.symm
  change (L.subgroupOf I).map (centralizerQuotientMap (L.subgroupOf I)) ⊔
    (S.subgroupOf I).map (centralizerQuotientMap (L.subgroupOf I)) = ⊤
  rw [← Subgroup.map_sup, hLI]
  exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
/-- The full source local configuration cannot have the actual Rudvalis
carrier as its component quotient. All hypotheses are those of the standing
setup and the supplied model equivalence. -/
public theorem rudvalis_exclusion [Finite G] (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* Rudvalis.Model) : False := by
  obtain ⟨P, hP⟩ := d.quotient_local.sylow
  have hchar : centralizer (pCore 2 (componentImage I L M) : Set (componentImage I L M)) ≤
      pCore 2 (componentImage I L M) := by
    rw [← d.quotient_local.characteristicTwo]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hn := Rudvalis.SylowOvergroups.not_nine_dvd_card_twoExtension
    (componentImage I L L) (componentModel d e) (component_quotient_isTwoGroup d)
    P (componentImage I L M) (hP.symm ▸ d.quotient_local.sylow_le) hchar
  have hd := shadow_local_order_bounds P (componentImage I L M) (componentImage I L Y)
    (componentImage I L S) hP d.quotient_local.sylow_le
    (d.quotient_local.yplus_le.trans inf_le_left) d.quotient_local.shadow
  exact hn ((by decide : 9 ∣ 36).trans hd.1)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.RudvalisExclusion
