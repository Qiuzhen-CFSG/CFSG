module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.Inputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.Transport
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero

/-!
# Borel three-rank across the actual component map

The restriction of a surjection to a Sylow normalizer has a two-group
kernel whenever the original map does. The prime-rank kernel inequality
therefore bounds its three-rank by that of the image normalizer. Apply
this to L → L/Z(L) ≃ L⁺, using the earlier identity Z(L) = O₂(L).
No centerless-cover or multiplier assertion is needed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final proof
of 15.3.35, printed p.1139, with the earlier component inputs of 15.3.33
and 15.3.41.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField.LinearSelection

variable {K H : Type*} [Group K] [Finite K] [Group H] [Finite H]

private theorem three_rank_normalizer_le_of_two_kernel
    (f : K →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (P : Sylow 2 K) :
    primeRank 3 (normalizer (P : Set K)) ≤
      primeRank 3 (normalizer (P.mapSurjective hf : Set H)) := by
  let Q := P.mapSurjective hf
  let N := normalizer (P : Set K)
  let fN : N →* normalizer (Q : Set H) :=
    (f.comp N.subtype).codRestrict _ (fun x =>
      (P : Subgroup K).le_normalizer_map f (mem_map_of_mem f x.property))
  let k : fN.ker →* f.ker :=
    ((N.subtype.comp fN.ker.subtype).codRestrict _ (fun x =>
      congrArg Subtype.val x.property))
  have hki : Function.Injective k := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : K)) h))
  have hkt : IsPGroup 2 fN.ker := IsPGroup.of_injective hk k hki
  have hkr : primeRank 3 fN.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨n, hn⟩ := hkt.exists_card_eq
    rw [hn]
    intro hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hr := primeRank_le_ker_add (p := 3) fN
  simpa only [hkr, zero_add] using hr

variable {G : Type*} [Group G] [Finite G]

/-- A bound for every component-image Sylow normalizer also bounds the original Borel. -/
theorem three_rank_borel_le_of_component_image
    (I L M Yplus S B : Subgroup G) [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (hB : BorelOverSylow L S B) {r : ℕ}
    (hbound : ∀ P : Sylow 2 (componentImage I L L),
      primeRank 3 (normalizer (P : Set (componentImage I L L))) ≤ r) :
    primeRank 3 B ≤ r := by
  obtain ⟨P, _, rfl⟩ := hB
  rw [← primeRank_equiv 3 ((normalizer (P : Set L)).equivMapOfInjective
    L.subtype L.subtype_injective)]
  let e := componentImageCenterEquiv I L c.component_le
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := by
    ext x
    change e (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hp : IsPGroup 2 f.ker := by
    rw [hk, c.center_eq]
    exact pCore_isPGroup
  exact (three_rank_normalizer_le_of_two_kernel f hf hp P).trans (hbound _)

/-- The earlier rank-two actor excludes a three-free component Borel. -/
theorem no_three_free_component_borel
    (I L M Yplus S B : Subgroup G) [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (hB : BorelOverSylow L S B) (hYB : Yplus ≤ B)
    (hfree : ∀ P : Sylow 2 (componentImage I L L),
      ¬ 3 ∣ Nat.card (normalizer (P : Set (componentImage I L L)))) : False := by
  have hBzero := three_rank_borel_le_of_component_image I L M Yplus S B c hB
    (fun P => (PrimeRank.eq_zero_iff_not_dvd_card.mpr (hfree P)).le)
  have hY := primeRank_le_of_injective 3 (inclusion hYB) (inclusion_injective hYB)
  rw [c.yplus_three_rank] at hY
  omega
end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField.LinearSelection
