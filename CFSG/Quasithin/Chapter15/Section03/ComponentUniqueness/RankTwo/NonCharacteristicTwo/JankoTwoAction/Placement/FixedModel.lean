module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoAction.Models
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits
public import Theory.GroupTheory.CharacteristicCentralizerSylow


/-!
# Sylow overgroups prime to five in the full automorphism group of J₂

The checked double-coset cover places every prime-five-free overgroup of
`Seed.s` in its second normalizer inside J₂. The fixed outer Sylow subgroup
normalizes the inner radical because that radical is characteristic in
`Seed.s`. The index-two inner automorphism subgroup then extends the
containment to the full automorphism group.

The inner normalizer has order 1152, so its full automorphism normalizer
has order at most 2304. A subgroup containing the full Sylow subgroup of
order 256 and having order divisible by nine attains this bound. Sylow
conjugacy therefore supplies an actual conjugation onto the fixed normalizer.
All finite certificates are reused; no additional enumeration is introduced.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the local
inspection in 15.3.42, printed p.1138, and the overgroup calculation used
in 1.3.4, printed p.511; GLS3 Table 5.3g. The imported ATLAS J2G1-p100B0
words, normal forms, and kernel-checked certificates retain their attribution.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction.Placement
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
open GeneratorPair

/-- The checked permutation extension realizes every automorphism. -/
noncomputable def fullAut : Extension ≃* Model :=
  extensionEquivAut_of_pair_calculations first_generator_conjugate second_generator_orbits

/-- The automorphism realization agrees with literal inner conjugation. -/
theorem fullAut_inner (x : Carrier) : fullAut (intoExtension x) = MulAut.conj x :=
  extensionAction_inner x

/-- The inner action on the actual carrier is faithful. -/
theorem conj_injective : Function.Injective (MulAut.conj : Carrier →* Model) := by
  intro x y h
  exact SecondParabolic.intoExtension_injective (fullAut.injective
    (by simpa only [fullAut_inner] using h))

/-- The inner automorphism subgroup, using the literal conjugation map. -/
abbrev inner : Subgroup Model := (MulAut.conj : Carrier →* Model).range

/-- The checked outer automorphism quotient has order two. -/
theorem inner_index : inner.index = 2 := by
  have hAut : Nat.card Model = 2 * Nat.card Carrier := by
    rw [← Nat.card_congr fullAut.toEquiv]
    exact card_sup_zpowers_of_normalizing_involution _ _
      (by simpa only [pow_two] using involution_mul_self)
      involution_not_mem_generated involution_mem_normalizer
  have hinner : Nat.card inner = Nat.card Carrier :=
    (Nat.card_congr (MonoidHom.ofInjective conj_injective).toEquiv).symm
  have hc := inner.card_mul_index
  rw [hinner, hAut, Nat.mul_comm 2] at hc
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hc

/-- The full Sylow subgroup carried from the concrete permutation extension. -/
noncomputable def fixedSylow : Sylow 2 Model :=
  (SecondParabolic.outerSylow FirstParabolic.card_l₁).mapSurjective fullAut.surjective

/-- Its underlying subgroup is the image of the fixed outer Sylow. -/
theorem fixedSylow_coe : (fixedSylow : Subgroup Model) = Seed.outerS.map fullAut.toMonoidHom := rfl

/-- The full fixed Sylow subgroup has order 256. -/
theorem fixedSylow_card : Nat.card fixedSylow = 256 := by
  change Nat.card (Seed.outerS.map fullAut.toMonoidHom) = 256
  rw [card_map_of_injective (f := fullAut.toMonoidHom) fullAut.injective, SecondParabolic.card_outerS]

/-- The two embeddings agree on the fixed inner Sylow subgroup. -/
theorem inner_s_map : (Seed.s.map intoExtension).map fullAut.toMonoidHom =
    Seed.s.map (MulAut.conj : Carrier →* Model) := by
  rw [map_map]
  congr 1

/-- The fixed full Sylow contains the fixed inner two-subgroup. -/
theorem inner_s_le_fixedSylow : Seed.s.map (MulAut.conj : Carrier →* Model) ≤ fixedSylow := by
  rw [← inner_s_map, fixedSylow_coe]
  exact map_mono le_sup_left

/-- The checked outer word preserves the fixed inner Sylow subgroup. -/
theorem fixedSylow_normalizes_s :
    (fixedSylow : Subgroup Model) ≤ normalizer (Seed.s.map MulAut.conj : Set Model) := by
  rw [← inner_s_map, fixedSylow_coe]
  apply (map_mono (show Seed.outerS ≤ normalizer (Seed.s.map intoExtension : Set Extension) from
    sup_le (Seed.s.map intoExtension).le_normalizer
      (zpowers_le.mpr SecondParabolic.outerElement_normalizes_s))).trans
  exact le_normalizer_map _

/-- Characteristicity of the inner radical retains the entire outer Sylow action. -/
theorem fixedSylow_le_secondNormalizer : (fixedSylow : Subgroup Model) ≤ secondNormalizer := by
  let _ := PairNormalizer.q₂_characteristic
  have h := normalizer_le_normalizer_characteristic_map
    (MulAut.conj : Carrier →* Model) conj_injective Seed.s (Seed.q₂.subgroupOf Seed.s)
  rw [map_subgroupOf_eq_of_le PairNormalizer.q₂_le_s] at h
  exact fixedSylow_normalizes_s.trans h

/-- The full normalizer restricts to the literal fixed normalizer in J₂. -/
theorem secondNormalizer_comap : secondNormalizer.comap (MulAut.conj : Carrier →* Model) = Seed.p₂ := by
  rw [secondNormalizer, secondRadical,
    comap_normalizer_eq_of_le_range (Seed.q₂.map_le_range _),
    comap_map_eq_self_of_injective conj_injective]
  rfl

/-- The intersection with the inner automorphisms is exactly the inner normalizer. -/
theorem secondNormalizer_inf_inner : secondNormalizer ⊓ inner =
    Seed.p₂.map (MulAut.conj : Carrier →* Model) := by
  rw [← secondNormalizer_comap, map_comap_eq, inf_comm]

/-- The index-two extension bounds the full normalizer order by 2304. -/
theorem secondNormalizer_card_le : Nat.card secondNormalizer ≤ 2304 := by
  let _ : inner.Normal := normal_of_index_eq_two inner_index
  have hi : inner.relIndex secondNormalizer ≤ 2 :=
    Nat.le_of_dvd (by decide) (inner_index ▸ relIndex_dvd_index_of_normal inner secondNormalizer)
  have hc := relIndex_mul_relIndex (⊥ : Subgroup Model) (secondNormalizer ⊓ inner)
    secondNormalizer bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left,
    secondNormalizer_inf_inner, card_map_of_injective conj_injective, PairNormalizer.card_p₂] at hc
  omega

/-- The fixed outer word belongs to the full Sylow subgroup. -/
theorem outer_mem_fixedSylow : fullAut Seed.outerElement ∈ fixedSylow :=
  mem_map_of_mem _ (mem_sup_right (mem_zpowers _))

/-- The checked odd outer word is not an inner automorphism. -/
theorem outer_not_mem_inner : fullAut Seed.outerElement ∉ inner := by
  rintro ⟨x, hx⟩
  apply SecondParabolic.outerElement_not_mem_range
  refine ⟨x, fullAut.injective ?_⟩
  exact (fullAut_inner x).trans hx

/-- The inner prime-five obstruction and outer action give full containment. -/
theorem fixed_overgroup_le_secondNormalizer (H : Subgroup Model)
    (hS : (fixedSylow : Subgroup Model) ≤ H) (h5 : ¬ 5 ∣ Nat.card H) :
    H ≤ secondNormalizer := by
  let K := H.comap (MulAut.conj : Carrier →* Model)
  have hs : Seed.s ≤ K := fun x hx => hS (inner_s_le_fixedSylow (mem_map_of_mem _ hx))
  have hK5 : ¬ 5 ∣ Nat.card K := by
    intro hd
    apply h5
    have hc := card_dvd_of_le (map_comap_le (MulAut.conj : Carrier →* Model) H)
    rw [card_map_of_injective conj_injective] at hc
    exact hd.trans hc
  have hp : K ≤ Seed.p₂ :=
    Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.overgroup_le_second_normalizer_of_certificates
      Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.covers
      Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.s_le_p₂
      Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.representative_mem_p₂_or_orderOf_obstruction
      K hs hK5
  have hinner : ∀ x ∈ H, x ∈ inner → x ∈ secondNormalizer := by
    rintro x hx ⟨y, rfl⟩
    have hy : y ∈ K := hx
    exact (le_normalizer_map (MulAut.conj : Carrier →* Model)) (mem_map_of_mem _ (hp hy))
  intro x hx
  by_cases hi : x ∈ inner
  · exact hinner x hx hi
  · have ht : fullAut Seed.outerElement ∈ H := hS outer_mem_fixedSylow
    have hxi : x * fullAut Seed.outerElement ∈ inner :=
      (inner.mul_mem_iff_of_index_two inner_index).mpr (iff_of_false hi outer_not_mem_inner)
    have hxn := hinner _ (H.mul_mem hx ht) hxi
    have htn := fixedSylow_le_secondNormalizer outer_mem_fixedSylow
    simpa only [mul_inv_cancel_right] using secondNormalizer.mul_mem hxn (secondNormalizer.inv_mem htn)

/-- Divisibility by nine forces a containing full Sylow overgroup to attain the bound. -/
theorem fixed_overgroup_eq_secondNormalizer (H : Subgroup Model)
    (hS : (fixedSylow : Subgroup Model) ≤ H) (h5 : ¬ 5 ∣ Nat.card H)
    (h9 : 9 ∣ Nat.card H) : H = secondNormalizer := by
  have hle := fixed_overgroup_le_secondNormalizer H hS h5
  have h256 : 256 ∣ Nat.card H := by
    have h := card_dvd_of_le hS
    rw [fixedSylow_card] at h
    exact h
  have h2304 : 2304 ∣ Nat.card H :=
    (by decide : Nat.Coprime 256 9).mul_dvd_of_dvd_of_dvd h256 h9
  exact eq_of_le_of_card_ge hle
    (secondNormalizer_card_le.trans (Nat.le_of_dvd Nat.card_pos h2304))

/-- A full Sylow subgroup and the two numerical conditions determine the conjugacy class. -/
theorem exists_conjugate_eq_secondNormalizer (H : Subgroup Model)
    (hS : ∃ P : Sylow 2 Model, (P : Subgroup Model) ≤ H)
    (h5 : ¬ 5 ∣ Nat.card H) (h9 : 9 ∣ Nat.card H) :
    ∃ g : Model, H.map (MulAut.conj g).toMonoidHom = secondNormalizer := by
  obtain ⟨P, hP⟩ := hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model P fixedSylow
  refine ⟨g, fixed_overgroup_eq_secondNormalizer _ ?_ ?_ ?_⟩
  · have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hP
    change ((g • P : Sylow 2 Model) : Subgroup Model) ≤ _ at hm
    rwa [hg] at hm
  · rwa [card_map_of_injective (MulAut.conj g).injective]
  · rwa [card_map_of_injective (MulAut.conj g).injective]
end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction.Placement
