module

public import CFSG.Quasithin.Chapter2.Section01To03.Elementary
public import CFSG.Quasithin.Chapter1.Section01Overgroups
/-!
# Two-cores and Sylow subgroups above β

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 2.3.2(3), printed pp.521–522. Extend a β-subgroup to an actual
Sylow subgroup of H, and then to an ambient Sylow R. The β normalizer
condition keeps R inside M. Characteristic two in M puts Z(R) in O₂(M);
β's centralizer condition then puts Z(R) in the Sylow of H, and
characteristic two in H puts it in O₂(H). The nontrivial center gives
Chapter 1's central-Sylow intersection criterion.

The hypotheses used are even characteristic and M ∈ He, both supplied
by the chapter's simple QTKE and maximal-two-local hypotheses. The
ambient core and order interfaces are unchanged.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M U H : Subgroup G}

omit [Finite G] in
theorem twoCore_eq_pCoreIn (H : Subgroup G) : twoCore H = H.pCoreIn 2 := rfl
omit [Finite G] in
theorem le_normalizer_twoCore (H : Subgroup G) : H ≤ normalizer (twoCore H : Set G) := by
  simpa only [twoCore, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (pCore 2 H).le_normalizer_map H.subtype

theorem sylow_image_card (H : Subgroup G) (S : Sylow 2 H) :
    Nat.card ((S : Subgroup H).map H.subtype) = twoPart H :=
  (card_map_of_injective H.subtype_injective).trans S.card_eq_multiplicity

theorem exists_sylow_of_card {S H : Subgroup G} (hSH : S ≤ H)
    (hc : Nat.card S = twoPart H) :
    ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = S := by
  have hc' : Nat.card (S.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv).trans hc
  exact ⟨Sylow.ofCard _ hc', map_subgroupOf_eq_of_le hSH⟩

theorem twoPart_mono {H K : Subgroup G} (hHK : H ≤ K) : twoPart H ≤ twoPart K := by
  let S : Sylow 2 H := Classical.choice inferInstance
  obtain ⟨R, hR⟩ := (S.isPGroup'.map H.subtype).comap_of_injective K.subtype K.subtype_injective |>.exists_le_sylow
  have hSR : (S : Subgroup H).map H.subtype ≤ (R : Subgroup K).map K.subtype := by
    change ((S : Subgroup H).map H.subtype).subgroupOf K ≤ (R : Subgroup K) at hR
    have hm := map_mono hR (f := K.subtype)
    simpa only [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hHK)] using hm
  rw [← sylow_image_card H S, ← sylow_image_card K R]
  exact card_le_of_le hSR

theorem sylow_image_in_inf (S : Sylow 2 H)
    (hSM : (S : Subgroup H).map H.subtype ≤ M) :
    ∃ R : Sylow 2 ↥(H ⊓ M), (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype =
      (S : Subgroup H).map H.subtype := by
  apply exists_sylow_of_card (le_inf (map_subtype_le _) hSM)
  apply le_antisymm
  · let K := M.subgroupOf H
    have hSK : (S : Subgroup H) ≤ K := fun s hs => hSM (mem_map.mpr ⟨s, hs, rfl⟩)
    have hKcard : Nat.card K = Nat.card ↥(H ⊓ M) := by
      have hc := card_map_of_injective (K := K) H.subtype_injective
      rw [subgroupOf_map_subtype, inf_comm] at hc
      exact hc.symm
    rw [sylow_image_card, twoPart, ← S.card_eq_multiplicity]
    have hc : Nat.card ((S.subtype hSK : Sylow 2 K) : Subgroup K) =
        Nat.card (S : Subgroup H) := Nat.card_congr (subgroupOfEquivOfLe hSK).toEquiv
    rw [← hc, (S.subtype hSK).card_eq_multiplicity, hKcard]
    rfl
  · rw [sylow_image_card]
    exact twoPart_mono inf_le_left

theorem beta_twoCore_mem_S2e (hEven : IsEvenCharacteristic G)
    (hM : M ∈ Chapter1.He G) (hU : U ∈ beta M) (hUH : U ≤ H)
    (hH : H ∈ Chapter1.He G) : twoCore H ∈ Chapter1.S2e G := by
  obtain ⟨S, hUS, hS⟩ := beta_exists_sylow hU hUH
  obtain ⟨R, hSR⟩ := (S.isPGroup'.map H.subtype).exists_le_sylow
  have hRb : (R : Subgroup G) ∈ beta M := beta_mono hS hSR R.isPGroup'
  have hRM : (R : Subgroup G) ≤ M := hRb.2.1
  have hQMR : twoCore M ≤ (R : Subgroup G) := by
    have hm := pCoreIn_le_sylow M (R.subtype hRM)
    simpa only [twoCore_eq_pCoreIn, Sylow.coe_subtype, map_subgroupOf_eq_of_le hRM] using hm
  let Z := (center (R : Subgroup G)).map (R : Subgroup G).subtype
  have hZR : Z ≤ (R : Subgroup G) := map_subtype_le _
  have hZcentral : Z ≤ centralizer (R : Set G) := by
    rintro z ⟨a, ha, rfl⟩ r hr
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨r, hr⟩)
  have hZQM : Z ≤ twoCore M := fun z hz =>
    hM ⟨hRM (hZR hz), centralizer_le hQMR (hZcentral hz)⟩
  have hZS : Z ≤ (S : Subgroup H).map H.subtype := fun z hz =>
    hS.2.2.2 ⟨hZQM hz, centralizer_le hSR (hZcentral hz)⟩
  have hZQ : Z ≤ twoCore H := fun z hz => hH ⟨map_subtype_le _ (hZS hz),
    centralizer_le ((pCoreIn_le_sylow H S).trans hSR) (hZcentral hz)⟩
  have hRne : (R : Subgroup G) ≠ ⊥ := hRb.1.1
  have : Nontrivial (R : Subgroup G) := ((R : Subgroup G).nontrivial_iff_ne_bot).mpr hRne
  have hZne : Z ≠ ⊥ := fun he => (ne_of_gt R.isPGroup'.bot_lt_center)
    ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp he)
  have hQne : twoCore H ≠ ⊥ := fun he => hZne (bot_unique (he ▸ hZQ))
  exact Chapter1.lemma_1_1_4_3 R (hEven R) hQne (isPGroup_pCoreIn 2 H)
    (by change Z ⊓ twoCore H ≠ ⊥; rwa [inf_eq_left.mpr hZQ])

theorem beta_mem_S2e (hEven : IsEvenCharacteristic G)
    (hM : M ∈ Chapter1.He G) (hU : U ∈ beta M) : U ∈ Chapter1.S2e G := by
  have hcore : twoCore U = U := le_antisymm (pCoreIn_le 2 U)
    (le_pCoreIn_of_normalizes hU.1.2 le_rfl U.le_normalizer)
  have hHU : U ∈ Chapter1.He G := by
    change U ⊓ centralizer (twoCore U : Set G) ≤ twoCore U
    rw [hcore]
    exact inf_le_left
  simpa only [hcore] using beta_twoCore_mem_S2e hEven hM hU le_rfl hHU
end CFSG.Quasithin.Chapter2
