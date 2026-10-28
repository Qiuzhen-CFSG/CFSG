module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.Representatives
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.OuterSylow
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Noninner

/-!
# A finite word cover of the full outer Held Sylow

The existing pure-pair collection certificate gives 1024 distinct words in
`pureTwo`. Its certified order makes this family surjective. The full stabilizer's
inner intersection is exactly their inner image, by self-normalization of the
pure Sylow in Held. The published pure actor has odd permutation sign, whereas
Held is perfect, so the actor leaves the inner image. The supplied realization
and quotient bound then give exactly two cosets and a cover by 2048 words.

In particular the generated subgroup used in the discovery calculation equals
the full stabilizer. No elementary subgroup enumeration is used here.
Source: Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p;
`Coverage/source/README.md`, the unchanged ATLAS carrier, and the checked
`Pair00Two` collection and `PureActors.Actor0` word certificates.
-/

@[expose] public section
open Subgroup Held Held.LocalPairs Held.LocalPairs.PairCoverage.LocalActions
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue

open Exhaustion.CandidateOrderCertificate.Factors RepresentativeImages
set_option maxRecDepth 4096

private theorem input_eq (k : Fin 4) : Pair00Two.input k = (generator k).val := by
  fin_cases k <;> rfl

private theorem pureTwo_eq_inputClosure : pureTwo = closure (Set.range Pair00Two.input) := by
  have he : Pair00Two.input = fun k => (generator k).val := funext input_eq
  rw [he]
  rfl

theorem normalForm_mem (n : Fin 1024) : Pair00Two.normalForm n ∈ pureTwo := by
  rw [pureTwo_eq_inputClosure]
  apply list_prod_mem
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  apply pow_mem
  exact Exhaustion.CandidateOrderCertificate.evalSigned_mem Pair00Two.input (Pair00Two.pcWord k) _
    (fun i => subset_closure (Set.mem_range_self i))

/-- The existing 1024 pure words, restricted to their actual subgroup. -/
def pureElement (n : Fin 1024) : pureTwo := ⟨Pair00Two.normalForm n, normalForm_mem n⟩

theorem pureElement_injective : Function.Injective pureElement := by
  intro m n h
  apply Fin.ext
  have he := congrArg (fun x : pureTwo => Pair00Two.decode (representation x.val)) h
  change Pair00Two.decode (representation (Pair00Two.normalForm m)) =
    Pair00Two.decode (representation (Pair00Two.normalForm n)) at he
  simpa only [← Pair00Two.normalTable_eq, Pair00Two.decode_normal] using he

theorem pureElement_surjective : Function.Surjective pureElement := by
  apply ((Nat.bijective_iff_injective_and_card pureElement).mpr ⟨pureElement_injective, ?_⟩).2
  simpa only [Nat.card_fin, pureTwo] using (Exhaustion.candidateFactorOrders false 0).1.symm

/-- The genuine inner embedding of the pure subgroup into its full stabilizer. -/
def inner : pureTwo →* outerRepresentative where
  toFun x := ⟨MulAut.conj x.val,
    pureTwo_map_conj_le_outerRepresentative (mem_map_of_mem MulAut.conj x.property)⟩
  map_one' := Subtype.ext (map_one MulAut.conj)
  map_mul' x y := Subtype.ext (map_mul MulAut.conj x.val y.val)

/-- The published pure actor, acting as an automorphism of Held. -/
def actor : outerRepresentative :=
  ⟨permutationGroup.normalizerMonoidHom (PureActors.actor false).val,
    (normalizerAction_mem_stabilizer_iff permutationGroup pureTwo _).mpr
      (PureActors.permutation_normalizes_two false)⟩

private theorem implementer_sign : Equiv.Perm.sign OuterInvolution.implementer = -1 := by
  have h := OuterInvolution.representative_sign
  change Equiv.Perm.sign (OuterInvolution.implementer ^ 5) = -1 at h
  rw [map_pow] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign OuterInvolution.implementer) with he | he
  · rw [he] at h
    norm_num at h
  · exact he

private theorem actor_sign : Equiv.Perm.sign (PureActors.actor false).val.val = -1 := by
  have ha : Equiv.Perm.sign atlasA = 1 := by
    have h := hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) a
    simpa only [MonoidHom.comp_apply, representation, Subgroup.subtype_apply, Held.a] using h
  have hb : Equiv.Perm.sign atlasB = 1 := by
    have h := hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) b
    simpa only [MonoidHom.comp_apply, representation, Subgroup.subtype_apply, Held.b] using h
  change Equiv.Perm.sign PureActors.Actor0.perm = -1
  rw [PureActors.Actor0.perm_eq_word]
  simp only [map_mul, map_zpow, ha, hb, implementer_sign, one_zpow, one_mul, mul_one]
  norm_num

/-- The selected actor really leaves the inner automorphism group. -/
theorem actor_not_inner : actor.val ∉ MulAut.innerSubgroup He := by
  intro h
  have hm := (normalizerAction_mem_inner_iff (PureActors.actor false).val).mp h
  have he : Equiv.Perm.sign (PureActors.actor false).val.val = 1 := by
    have h := hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) ⟨_, hm⟩
    simpa only [MonoidHom.comp_apply, representation, Subgroup.subtype_apply] using h
  rw [actor_sign] at he
  exact (by decide : (-1 : ℤˣ) ≠ 1) he

private theorem pureTwo_self_normalizing : normalizer (pureTwo : Set He) = pureTwo := by
  obtain ⟨S, hS⟩ := pureTwo_sylow
  rw [← hS]
  exact SylowGeometry.Calculations.inner_self_normalizing S

/-- The inner part of the full stabilizer is exactly the pure subgroup's image. -/
theorem inner_range : inner.range = (MulAut.innerSubgroup He).subgroupOf outerRepresentative := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.val, rfl⟩
  · rintro ⟨y, hy⟩
    change MulAut.conj y = x.val at hy
    have hn : y ∈ normalizer (pureTwo : Set He) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      have hx := x.property
      change pureTwo.map x.val.toMonoidHom = pureTwo at hx
      rwa [← hy] at hx
    rw [pureTwo_self_normalizing] at hn
    exact ⟨⟨y, hn⟩, Subtype.ext hy⟩

/-- The realized full stabilizer has precisely two cosets over the inner image. -/
theorem inner_index
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2) : inner.range.index = 2 := by
  have hi : (MulAut.innerSubgroup He).index ≤ 2 :=
    (Nat.card_le_card_of_surjective _
      (normalizerOuterAction_surjective permutationGroup hreal)).trans hbound
  have hb : inner.range.index ≤ 2 := by
    rw [inner_range]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite)
      ((MulAut.innerSubgroup He).relIndex_dvd_index_of_normal outerRepresentative)).trans hi
  have hne : inner.range.index ≠ 1 := by
    intro h
    have hm : actor ∈ inner.range := by rw [index_eq_one.mp h]; trivial
    rw [inner_range] at hm
    exact actor_not_inner hm
  have hpos : 0 < inner.range.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
  omega

/-- A fixed 2048-element word family in the full outer Sylow. -/
def element (n : Bool × Fin 1024) : outerRepresentative :=
  inner (pureElement n.2) * if n.1 then actor else 1

/-- The words cover the full stabilizer, not merely the displayed generated subgroup. -/
theorem element_surjective
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2) : Function.Surjective element := by
  intro x
  by_cases hx : x ∈ inner.range
  · obtain ⟨s, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := pureElement_surjective s
    exact ⟨(false, n), by simp [element]⟩
  · have ha : actor⁻¹ ∉ inner.range := by
      rw [inv_mem_iff, inner_range]
      exact actor_not_inner
    have hm : x * actor⁻¹ ∈ inner.range :=
      (mul_mem_iff_of_index_two (inner_index hreal hbound)).mpr (by simp [hx, ha])
    obtain ⟨s, hs⟩ := hm
    obtain ⟨n, rfl⟩ := pureElement_surjective s
    refine ⟨(true, n), ?_⟩
    simp only [element, ↓reduceIte, hs, inv_mul_cancel_right]

/-- The subgroup generated by the inner pure subgroup and the published actor is
exactly the full automorphism stabilizer. -/
theorem generated_eq_outerRepresentative
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2) :
    pureTwo.map MulAut.conj ⊔ zpowers actor.val = outerRepresentative := by
  apply le_antisymm
  · exact sup_le pureTwo_map_conj_le_outerRepresentative (zpowers_le.mpr actor.property)
  · intro x hx
    obtain ⟨⟨b, n⟩, hn⟩ := element_surjective hreal hbound ⟨x, hx⟩
    have he := congrArg Subtype.val hn
    change (element (b, n)).val = x at he
    rw [← he]
    have hm : MulAut.conj (pureElement n).val ∈
        pureTwo.map MulAut.conj ⊔ zpowers actor.val :=
      mem_sup_left (mem_map_of_mem _ (pureElement n).property)
    cases b
    · change MulAut.conj (pureElement n).val * 1 ∈ _
      simpa only [mul_one] using hm
    · exact mul_mem hm (mem_sup_right (mem_zpowers _))


end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue
