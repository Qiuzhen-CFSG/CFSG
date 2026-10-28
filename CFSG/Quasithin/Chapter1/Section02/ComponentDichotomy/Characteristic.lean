module
public import CFSG.Quasithin.Chapter1.Section01Overgroups
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.CharacteristicCentralizerFusion


/-!
# Characteristic two from the source central involution

The ambient centralizer of a Sylow-central involution has characteristic two.
The source core-centralizer bound then passes characteristic two to its
intersection with H. Once the involution lies in O₂(H), that intersection
contains C_H(O₂(H)), and the core-centralizer overgroup criterion gives
characteristic two in H itself. All centralizers and cores retain their
original ambient maps.

Source: Aschbacher–Smith 1.2.11, final paragraph, printed p.508.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1
variable {G : Type*} [Group G] [Finite G]

theorem he_of_central_involution_in_core (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T) (H : Subgroup G) (z : G)
    (hs : IsSylowIn 2 ((T : Subgroup G) ⊓ H) H)
    (hz : orderOf z = 2) (hzH : z ∈ H.pCoreIn 2)
    (hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hCT : (T : Subgroup G) ⊓ centralizer (H.pCoreIn 2 : Set G) ≤
      (T : Subgroup G) ⊓ H) : H ∈ He G := by
  let C := centralizer ({z} : Set G)
  let N := H ⊓ C
  have hzH' : z ∈ H := pCoreIn_le 2 H hzH
  have hzN : z ∈ N := ⟨hzH', mem_centralizer_singleton_iff.mpr rfl⟩
  have hz1 : z ≠ 1 := by intro he; simp only [he, orderOf_one] at hz; omega
  have hTC : (T : Subgroup G) ≤ C := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzc t ht)
  have hC : C ∈ He G := by
    have hp : IsPGroup 2 (zpowers z) := by
      let := IsElementaryAbelian.zpowers_of_pow_eq_one (hz ▸ pow_orderOf_eq_one z)
      exact IsElementaryAbelian.isPGroup 2 _
    have hne : zpowers z ≠ ⊥ := by
      intro he
      exact hz1 (mem_bot.mp (he ▸ mem_zpowers z))
    apply twoLocal_mem_He_of_sylow_le T hE ?_ hTC
    exact ⟨zpowers z, hne, hp, (normalizer_zpowers_eq_centralizer_of_order_two z hz).symm⟩
  obtain ⟨S,hS⟩ := hs
  have hHT : H.pCoreIn 2 ≤ (T : Subgroup G) :=
    ((pCoreIn_le_sylow H S).trans_eq hS).trans inf_le_left
  have hHN : H.pCoreIn 2 ≤ N := by
    intro x hx
    exact ⟨pCoreIn_le 2 H hx, mem_centralizer_singleton_iff.mpr (hzc x (hHT hx))⟩
  have hcore : H.pCoreIn 2 ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) hHN
      (inf_le_left.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  have hCT' : C.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow C (T.subtype hTC)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTC] using hh
  have hN : N ∈ He G := by
    apply lemma_1_1_4_4 (fun he => hz1 (mem_bot.mp (he ▸ hzN))) inf_le_right hC
    intro x hx
    exact ⟨(hCT ⟨hCT' hx.1, centralizer_le hcore hx.2⟩).2, pCoreIn_le 2 C hx.1⟩
  apply mem_He_iff.mpr
  apply centralizer_pCore_le_of_overgroup 2 (N.subgroupOf H)
  · exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe (show N ≤ H from inf_le_left))).mpr (mem_He_iff.mp hN)
  · intro x hx
    refine ⟨x.property, mem_centralizer_singleton_iff.mpr ?_⟩
    obtain ⟨a,ha,he⟩ := mem_map.mp hzH
    have hh := congrArg Subtype.val (hx a ha)
    change (a : G) * (x : G) = (x : G) * (a : G) at hh
    change (a : G) = z at he
    rw [he] at hh
    exact hh.symm
end CFSG.Quasithin.Chapter1
