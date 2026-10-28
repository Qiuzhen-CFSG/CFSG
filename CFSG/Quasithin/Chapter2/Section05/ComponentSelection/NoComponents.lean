module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SourceConfiguration
public import Theory.GroupTheory.GeneralizedFitting.NoComponentInverter

/-!
# Excluding the component-free case of 2.5.3

The selected saturated pair supplies N=O2(H_U), with O2(H) contained in N
and the original marked involution z in Z(N). If H has no components,
O2(H)<z>O(H) is normal in H. Its intersection with N is exactly O2(H)<z>,
because N and O(H) have coprime orders. Thus H_U normalizes this nontrivial
two-subgroup D. The original ambient two-central mark puts N_G(D) in He,
while S normalizes D. Source 2.5.1 forces N_G(D) into M, contradicting
the actual local pair H_U outside M.

Source: Aschbacher--Smith, the component-free final paragraph of 2.5.3(4),
printed p.553. This is the genuine branch contradiction; the separate
component-present induction must still select a non-Bender component.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}

/-- The original normalizer-intersection source group has a component.
All maximal-pair, saturation, Sylow and involution inputs are constructed. -/
theorem exists_component_of_normalizer_intersection
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → (T₀ : Subgroup G) ≤ X → X = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G)) :
    ∃ K : Subgroup H, IsComponent H K := by
  by_contra hnone
  have hnc : ∀ K : Subgroup H, ¬ IsComponent H K := by simpa only [not_exists] using hnone
  obtain ⟨U, HU, S, T, z, d, hpair, hUS, hQS, hzNcenter, hsat⟩ :=
    exists_saturated_source_configuration hG T₀ hM hT₀M hunique hH B hp hBH hHnorm
  have hMe : M ∈ Chapter1.He G :=
    Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T₀ M hM hT₀M)
  obtain ⟨hHeS, _hgreatest, P, hP⟩ := lemma_2_5_1 hMe hempty d
  have hSH : S ≤ H := hP ▸ map_subtype_le (P : Subgroup H)
  have hzS : z ∈ S := d.center_le d.mem_center
  have hzc (x : G) (hx : x ∈ T) : x * z = z * x := by
    obtain ⟨a, ha, rfl⟩ := d.mem_center
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨x, hx⟩)
  have hMcentral : ∃ R : Sylow 2 M,
      ∀ x ∈ (R : Subgroup M).map M.subtype, x * z = z * x := by
    obtain ⟨R, hR⟩ := d.sylow_maximal
    exact ⟨R, fun x hx => hzc x (hR ▸ hx)⟩
  have h115 := lemma_2_3_8_6 hG T₀ hM hT₀M hunique hH hpair P
    (hP.symm ▸ hUS) d.involution (hP.symm ▸ hzS)
    (fun x hx => hzc x (d.lt.le (hP ▸ hx))) hMcentral
  let N := twoCore HU
  let Q := twoCore H
  let Y := (pPrimeCore 2 H).map H.subtype
  let D := Q ⊔ zpowers z
  let zH : H := ⟨z, hSH hzS⟩
  have hzN : z ∈ N := map_subtype_le _ hzNcenter
  have hQN : Q ≤ N := hsat Q (pCoreIn_le 2 H) (isPGroup_pCoreIn 2 H)
    (hpair.2.trans (le_normalizer_twoCore H))
  have hDN : D ≤ N := sup_le hQN (zpowers_le.mpr hzN)
  have hNH : N ≤ H := (pCoreIn_le 2 HU).trans hpair.2
  have hDH : D ≤ H := hDN.trans hNH
  have hDp : IsPGroup 2 D := (isPGroup_pCoreIn 2 HU).to_le hDN
  have hzD : z ∈ D := (show zpowers z ≤ D from le_sup_right) (mem_zpowers z)
  have hz1 : z ≠ 1 := by intro hz; simpa [hz] using d.involution
  have hDne : D ≠ ⊥ := by intro hb; exact hz1 (mem_bot.mp (hb ▸ hzD))
  have hfix : zH ∈ centralizer (pCore 2 H : Set H) := by
    intro q hq
    exact Subtype.ext (hzc q (d.lt.le (hP ▸ pCoreIn_le_sylow H P
      (mem_map_of_mem H.subtype hq))))
  have hinv : ∀ y ∈ pPrimeCore 2 H, zH * y * zH⁻¹ = y⁻¹ := by
    intro y hy
    exact Subtype.ext (h115.inverts_oddCore y hy)
  let W : Subgroup H := pCore 2 H ⊔ zpowers zH ⊔ pPrimeCore 2 H
  let : W.Normal := no_component_inverted_core_product_normal 2 hnc zH hfix hinv
  have hWmap : W.map H.subtype = D ⊔ Y := by
    dsimp [W, D, Q, Y, twoCore, pCoreIn]
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  have hHW : H ≤ normalizer ((D ⊔ Y : Subgroup G) : Set G) := by
    rw [← hWmap]
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using W.le_normalizer_map H.subtype
  have hHY : H ≤ normalizer (Y : Set G) := by
    change H ≤ normalizer ((pPrimeCore 2 H).map H.subtype : Set G)
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pPrimeCore 2 H).le_normalizer_map H.subtype
  have hYcard : Nat.card Y = Nat.card (pPrimeCore 2 H) :=
    (Nat.card_congr ((pPrimeCore 2 H).equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm
  have hdis : Disjoint N Y := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k, hk⟩ := (isPGroup_pCoreIn 2 HU).exists_card_eq
    change Nat.card (twoCore HU) = 2 ^ k at hk
    change Nat.Coprime (Nat.card (twoCore HU)) (Nat.card Y)
    rw [hk, hYcard]
    exact (pPrimeCore_coprime_card (p := 2) (G := H)).pow_left k
  have hinter : N ⊓ (D ⊔ Y) = D := by
    apply le_antisymm
    · rintro x ⟨hxN, hx⟩
      have hprod : x ∈ (D : Set G) * (Y : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right D Y (hDH.trans hHY)]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hprod
      have hbN : b ∈ N := (N.mul_mem_cancel_left (hDN ha)).mp hxN
      have hb1 : b = 1 := mem_bot.mp ((disjoint_iff.mp hdis) ▸ ⟨hbN, hb⟩)
      change a * b ∈ D
      rw [hb1, mul_one]
      exact ha
    · exact le_inf hDN le_sup_left
  have hHUD : HU ≤ normalizer (D : Set G) := by
    rw [← hinter]
    intro x hx y
    exact and_congr (le_normalizer_twoCore HU hx y) (hHW (hpair.2 hx) y)
  have hSD : S ≤ normalizer (D : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (twoCore H ⊔ zpowers z).map (MulAut.conj s).toMonoidHom = twoCore H ⊔ zpowers z
    have hmapQ : (twoCore H).map (MulAut.conj s).toMonoidHom = twoCore H :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_twoCore H (hSH hs))
    rw [Subgroup.map_sup, hmapQ, MonoidHom.map_zpowers]
    have he : (MulAut.conj s) z = z := by
      change s * z * s⁻¹ = z
      rw [hzc s (d.lt.le hs)]
      simp
    change twoCore H ⊔ zpowers ((MulAut.conj s) z) = twoCore H ⊔ zpowers z
    rw [he]
  have hTcard : Nat.card T = 2 ^ (Nat.card G).factorization 2 := by
    obtain ⟨R, hR⟩ := d.sylow_maximal
    rw [← hR, sylow_image_card, twoPart_eq_sylow_card T₀ hT₀M]
    exact T₀.card_eq_multiplicity
  let R : Sylow 2 G := Sylow.ofCard T hTcard
  have hRT : (R : Subgroup G) = T := Sylow.coe_ofCard T hTcard
  have hZcap : (center (R : Subgroup G)).map (R : Subgroup G).subtype ⊓ D ≠ ⊥ := by
    rw [hRT]
    intro hb
    exact hz1 (mem_bot.mp (hb ▸ (show z ∈
      (center T).map T.subtype ⊓ D from ⟨d.mem_center, hzD⟩)))
  have hDe := Chapter1.lemma_1_1_4_3 R (hG.evenCharacteristic R) hDne hDp hZcap
  have hNcore : twoCore (normalizer (D : Set G)) ≠ ⊥ := by
    intro hb
    have hle := le_pCoreIn_of_normalizes hDp D.le_normalizer le_rfl
    exact hDne (bot_unique (hb ▸ hle))
  have hNM : normalizer (D : Set G) ≤ M :=
    hHeS _ ⟨hDe.2.2, hNcore, hSD⟩
  exact hpair.1.2.2.2.2 (hHUD.trans hNM)

/-- Apply the proved component-free exclusion to the actual core
normalizer. Both original starred-family conditions persist. -/
theorem core_normalizer_has_component
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → (T₀ : Subgroup G) ≤ X → X = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅) :
    normalizer (twoCore H : Set G) ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M →
        normalizer (twoCore H : Set G) ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M →
        normalizer (twoCore H : Set G) ∈ gammaMax (Chapter1.He G) M) ∧
      ∃ K : Subgroup (normalizer (twoCore H : Set G)),
        IsComponent (normalizer (twoCore H : Set G)) K := by
  let N := normalizer (twoCore H : Set G)
  have hgamma : H ∈ gamma (Chapter1.He G) M :=
    hH.elim (fun hh => hh.1.1) (fun hh => hh.1)
  have hNcore : twoCore N ≠ ⊥ := by
    intro hb
    have hle := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
      (twoCore H).le_normalizer (show N ≤ normalizer (twoCore H : Set G) from le_rfl)
    exact hgamma.1 (bot_unique (hb ▸ hle))
  have hn := gammaZero_overgroup hH (le_normalizer_twoCore H) hNcore
  refine ⟨hn.1, hn.2.2.1, hn.2.2.2, ?_⟩
  apply exists_component_of_normalizer_intersection hG T₀ hM hT₀M hunique hn.1 hempty
    (fun _ : Fin 1 => twoCore H) (fun _ => isPGroup_pCoreIn 2 H)
    (fun _ => (twoCore H).le_normalizer)
  simp only [iInf_const]

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
