module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.LocalConfiguration
public import Theory.GroupTheory.PGroupNormalizerCharacteristic
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.RankOneFourNormalizer

/-!
# The J₂ and HS exclusions from the normal four-group

The source residual and S₃ shadow imply that nine does not divide the order
of the maximal local subgroup M. The moved four-group V lies inside the
normal component K. Restricting the ambient Sylow subgroup to K therefore
produces an actual Sylow-normal elementary four-group.

An intrinsic subgroup Q characteristic in that Sylow subgroup, whose
normalizer covers the four-group normalizer and whose centralizer is a
two-group, gives an ambient characteristic-two normalizer containing M.
Maximality makes it equal M. This excludes either a normalizer with order
divisible by nine (J₂), or one that fails to normalize V
(HS). Component--Sylow generation handles all allowed
extensions without an assumed automorphism-group catalogue.

The intrinsic normalizer theorems for the fixed ATLAS carriers supply both
witnesses, including exhaustive coverage and transport through actual model
equivalences. The final exclusions have no additional local-model premises.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.43,
sporadic paragraph on printed p.1140; the carrier list is 1.1.5(3)(f), p.502.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels.JankoTwoHigmanSims
variable {G : Type*} [Group G] [Finite G] {K S M Y V : Subgroup G}

omit [Finite G] in
/-- The moved four-group lies in the normal component. -/
theorem plane_le_component (c : LocalConfiguration K S M Y V) : V ≤ K := by
  let : K.Normal := c.normal
  rw [← c.plane_commutator]
  exact (commutator_mono le_rfl c.y_le_component).trans (commutator_le_right V K)

/-- The literal residual and S₃ quotient exclude nine from the local order. -/
theorem local_nine_not_dvd (c : LocalConfiguration K S M Y V) : ¬ 9 ∣ Nat.card M := by
  intro h9
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := M) 3 (n := 2) h9
  have hPY : P.map M.subtype ≤ Y := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := (IsPGroup.of_card hP) (⟨x, hx⟩ : P)
    rw [c.residual]
    exact mem_map.mpr ⟨x, mem_primePowerGenerated_of_pow
      (congrArg (fun a : P => (a : M)) hn), rfl⟩
  have hd : 9 ∣ Nat.card (Y ⊔ S : Subgroup G) := by
    have hh := card_dvd_of_le (hPY.trans (le_sup_left : Y ≤ Y ⊔ S))
    rwa [card_map_of_injective M.subtype_injective, hP] at hh
  obtain ⟨e⟩ := c.shadow
  have hi : (pCore 2 (Y ⊔ S : Subgroup G)).index = 6 := by
    change Nat.card ((Y ⊔ S : Subgroup G) ⧸ pCore 2 (Y ⊔ S : Subgroup G)) = 6
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := (Y ⊔ S : Subgroup G))).exists_card_eq
  rw [← (pCore 2 (Y ⊔ S : Subgroup G)).card_mul_index, hn, hi] at hd
  have hc : Nat.Coprime 9 (2 ^ n) := (by decide : Nat.Coprime 9 2).pow_right n
  exact (by decide : ¬ 9 ∣ 6) (hc.dvd_of_dvd_mul_left hd)

omit [Finite G] in
/-- Component--Sylow generation makes the ambient quotient a two-group. -/
theorem quotient_is_two_group (c : LocalConfiguration K S M Y V) [K.Normal] :
    IsPGroup 2 (G ⧸ K) := by
  obtain ⟨P, hP⟩ := c.sylow
  have hs : IsPGroup 2 S := hP ▸ P.isPGroup'
  let f := QuotientGroup.mk' K
  have hmap : S.map f = ⊤ := by
    have he := congrArg (Subgroup.map f) c.generated
    rw [Subgroup.map_sup, map_top_of_surjective _ (QuotientGroup.mk'_surjective K)] at he
    have hk : K.map f = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      exact le_of_eq (QuotientGroup.ker_mk' K).symm
    rwa [hk, bot_sup_eq] at he
  have ht : IsPGroup 2 (⊤ : Subgroup (G ⧸ K)) := hmap ▸ hs.map f
  exact ht.of_equiv Subgroup.topEquiv

omit [Finite G] in
/-- A component centralizer that is a two-group remains one in every allowed extension. -/
theorem centralizer_is_two_group (c : LocalConfiguration K S M Y V)
    (Q : Subgroup G)
    (hc : IsPGroup 2 ((centralizer (Q : Set G)).subgroupOf K)) :
    IsPGroup 2 (centralizer (Q : Set G)) := by
  let : K.Normal := c.normal
  intro x
  obtain ⟨n, hn⟩ := quotient_is_two_group c (QuotientGroup.mk' K (x : G))
  have hk : (x : G) ^ (2 ^ n) ∈ K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' K ((x : G) ^ (2 ^ n)) = 1
    rwa [map_pow]
  have hx : (⟨(x : G) ^ (2 ^ n), hk⟩ : K) ∈
      (centralizer (Q : Set G)).subgroupOf K :=
    (centralizer (Q : Set G)).pow_mem x.property _
  obtain ⟨m, hm⟩ := hc ⟨⟨(x : G) ^ (2 ^ n), hk⟩, hx⟩
  refine ⟨n + m, Subtype.ext ?_⟩
  have hh := congrArg (fun y : (centralizer (Q : Set G)).subgroupOf K => ((y : K) : G)) hm
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul] using hh

/-- A covered normalizer with two-group centralizer is forced to be the maximal local. -/
theorem local_eq_normalizer (c : LocalConfiguration K S M Y V)
    (Q : Subgroup G) (hq : IsPGroup 2 Q)
    (hc : IsPGroup 2 ((centralizer (Q : Set G)).subgroupOf K))
    (hS : S ≤ normalizer (Q : Set G))
    (hcover : K ⊓ normalizer (V : Set G) ≤ normalizer (Q : Set G)) :
    M = normalizer (Q : Set G) := by
  let : K.Normal := c.normal
  have hMV : M ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer c.plane_le_local).mp c.plane_normal
  have hMN : M ≤ normalizer (Q : Set G) := by
    intro x hx
    have hgen : x ∈ K ⊔ S := c.generated.ge (mem_top x)
    obtain ⟨k, hk, s, hs, rfl⟩ := mem_sup_of_normal_left.mp hgen
    have hkM : k ∈ M := by
      have hh := M.mul_mem hx (M.inv_mem (c.sylow_le_local hs))
      simpa only [mul_inv_cancel_right] using hh
    exact (normalizer (Q : Set G)).mul_mem (hcover ⟨hk, hMV hkM⟩) (hS hs)
  have hp := Theory.GroupTheory.generalizedFitting_normalizer_eq_pCore_of_centralizer_isPGroup Q hq (centralizer_is_two_group c Q hc)
  exact c.maximal.eq_of_le hp hMN

/-- Either a larger three-part or failure to preserve the four-group excludes the local. -/
theorem component_normalizer_contradiction (c : LocalConfiguration K S M Y V)
    [K.Normal] (Q : Subgroup K)
    (hq : IsPGroup 2 Q) (hc : IsPGroup 2 (centralizer (Q : Set K)))
    (hstable : ∀ s ∈ S, Q.map (MulAut.conjNormal s).toMonoidHom = Q)
    (hcover : normalizer (V.subgroupOf K : Set K) ≤ normalizer (Q : Set K))
    (hbad : 9 ∣ Nat.card (normalizer (Q : Set K)) ∨
      ¬ normalizer (Q : Set K) ≤ normalizer (V.subgroupOf K : Set K)) : False := by
  let R := Q.map K.subtype
  have hcentral : (centralizer (R : Set G)).subgroupOf K = centralizer (Q : Set K) := by
    ext x
    constructor
    · intro hx q hq
      apply Subtype.ext
      exact mem_centralizer_iff.mp hx q (mem_map.mpr ⟨q, hq, rfl⟩)
    · intro hx q hqR
      obtain ⟨a, ha, he⟩ := (mem_map (f := K.subtype) (K := Q)).mp hqR
      rw [← he]
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx a ha)
  have hS : S ≤ normalizer (R : Set G) := by
    apply le_normalizer_iff.mpr
    intro s hs r hr
    obtain ⟨q, hq, rfl⟩ := mem_map.mp hr
    have hm := mem_map_of_mem (MulAut.conjNormal s).toMonoidHom hq
    rw [hstable s hs] at hm
    exact mem_map.mpr ⟨MulAut.conjNormal s q, hm, rfl⟩
  have hVnormalizer : (normalizer (V : Set G)).subgroupOf K =
      normalizer (V.subgroupOf K : Set K) := subgroupOf_normalizer_eq (plane_le_component c)
  have hcover' : K ⊓ normalizer (V : Set G) ≤ normalizer (R : Set G) := by
    intro x hx
    have hv : (⟨x, hx.1⟩ : K) ∈ normalizer (V.subgroupOf K : Set K) := by
      rw [← hVnormalizer]
      exact hx.2
    exact Q.le_normalizer_map K.subtype (mem_map.mpr ⟨⟨x, hx.1⟩, hcover hv, rfl⟩)
  have he := local_eq_normalizer c R (hq.map K.subtype)
    (hcentral.symm ▸ hc) hS hcover'
  have hNM : (normalizer (Q : Set K)).map K.subtype ≤ M :=
    he.symm ▸ Q.le_normalizer_map K.subtype
  rcases hbad with h9 | hn
  · apply local_nine_not_dvd c
    have hd := card_dvd_of_le hNM
    rw [card_map_of_injective K.subtype_injective] at hd
    exact h9.trans hd
  · apply hn
    intro x hx
    rw [← hVnormalizer]
    exact ((normal_subgroupOf_iff_le_normalizer c.plane_le_local).mp c.plane_normal)
      (hNM (mem_map.mpr ⟨x, hx, rfl⟩))

/-- Intrinsic normalizer witnesses suffice uniformly for every allowed extension. -/
theorem not_of_normalizer_enlargements (c : LocalConfiguration K S M Y V)
    (hmodel : ∀ (T : Sylow 2 K) (W : Subgroup K), W ≤ (T : Subgroup K) →
      (W.subgroupOf (T : Subgroup K)).Normal → IsElementaryAbelian 2 W → Nat.card W = 4 →
      ∃ Q : Subgroup K, Q ≤ (T : Subgroup K) ∧
        (Q.subgroupOf (T : Subgroup K)).Characteristic ∧
        IsPGroup 2 (centralizer (Q : Set K)) ∧
        normalizer (W : Set K) ≤ normalizer (Q : Set K) ∧
        (9 ∣ Nat.card (normalizer (Q : Set K)) ∨
          ¬ normalizer (Q : Set K) ≤ normalizer (W : Set K))) : False := by
  let : K.Normal := c.normal
  obtain ⟨P, hP⟩ := c.sylow
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_normal K
  rw [hP] at hT
  let W := V.subgroupOf K
  have hWT : W ≤ (T : Subgroup K) := by
    rw [hT]
    exact fun _ hx => c.plane_le_sylow hx
  have hnormal : (W.subgroupOf (T : Subgroup K)).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    intro t ht
    have htS : (t : G) ∈ S := (show t ∈ S.subgroupOf K from hT ▸ ht)
    have hm : (t : G) ∈ normalizer (V : Set G) :=
      ((normal_subgroupOf_iff_le_normalizer c.plane_le_local).mp c.plane_normal)
        (c.sylow_le_local htS)
    have hh : t ∈ (normalizer (V : Set G)).subgroupOf K := hm
    rwa [subgroupOf_normalizer_eq (plane_le_component c)] at hh
  let : IsElementaryAbelian 2 V := c.plane_elementary
  have hW : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf (plane_le_component c)
  have hcard : Nat.card W = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (plane_le_component c)).toEquiv).trans c.plane_card
  obtain ⟨Q, hQT, hchar, hc, hcover, hbad⟩ := hmodel T W hWT hnormal hW hcard
  apply component_normalizer_contradiction c Q (T.isPGroup'.to_le hQT) hc ?_ hcover hbad
  intro s hs
  let β : MulAut K := MulAut.conjNormal s
  have hTmap : (T : Subgroup K).map β.toMonoidHom = (T : Subgroup K) := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro x ⟨t, ht, rfl⟩
      rw [hT] at ht ⊢
      change s * (t : G) * s⁻¹ ∈ S
      exact S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs)
    · exact (Nat.card_congr (β.subgroupMap (T : Subgroup K)).toEquiv).le
  let φ : MulAut T := (β.subgroupMap (T : Subgroup K)).trans (MulEquiv.subgroupCongr hTmap)
  have hfixed := characteristic_iff_map_eq.mp hchar φ
  have hh := congrArg (Subgroup.map (T : Subgroup K).subtype) hfixed
  have hcomp : (T : Subgroup K).subtype.comp φ.toMonoidHom =
      β.toMonoidHom.comp (T : Subgroup K).subtype := rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, map_subgroupOf_eq_of_le hQT] at hh
  exact hh

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels.JankoTwoHigmanSims

namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
variable {G : Type*} [Group G] [Finite G]

/-- J₂ and every ambient extension satisfying the source configuration are
excluded by a subgroup characteristic in the Sylow whose normalizer order is divisible by nine. -/
theorem LocalConfiguration.not_janko_two {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V)
    (e : K ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  apply JankoTwoHigmanSims.not_of_normalizer_enlargements c
  intro T W hWT hn he hc
  obtain ⟨Q, hQT, hchar, hcent, hcover, h9⟩ :=
    Sporadic.LeechRelated.J2.RankOneFourNormalizer.enlargement_of_equiv e T W hWT hn he hc
  exact ⟨Q, hQT, hchar, hcent, hcover, Or.inl h9⟩

/-- HS and every ambient extension satisfying the source configuration are
excluded by the characteristic eight whose normalizer moves the normal four-group. -/
theorem LocalConfiguration.not_higman_sims {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V)
    (e : K ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  apply JankoTwoHigmanSims.not_of_normalizer_enlargements c
  intro T W hWT hn he hc
  obtain ⟨Q, hQT, hchar, hcent, hcover, hbad⟩ :=
    Sporadic.LeechRelated.HS.RankOneFourNormalizer.enlargement_of_equiv e T W hWT hn he hc
  exact ⟨Q, hQT, hchar, hcent, hcover, Or.inr hbad⟩

/-- Exclude J₂ for the actual component image, retaining the original central cover. -/
theorem reduced_not_janko_two {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂)
    (e : c.toComponentAction.image L ≃* Sporadic.LeechRelated.J2.Carrier) : False :=
  (localConfiguration_of_reduced c).not_janko_two e

/-- Exclude HS for the actual component image, retaining the original central cover. -/
theorem reduced_not_higman_sims {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂)
    (e : c.toComponentAction.image L ≃* Sporadic.LeechRelated.HS.Carrier) : False :=
  (localConfiguration_of_reduced c).not_higman_sims e

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
