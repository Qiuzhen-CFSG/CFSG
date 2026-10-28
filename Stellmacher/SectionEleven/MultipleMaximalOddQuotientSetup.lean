module

public import Stellmacher.SectionEleven.MultipleMaximalOddQuotientCore
public import Stellmacher.SectionEleven.MultipleMaximalOddQuotientLocals
public import Stellmacher.SectionFiveToSeven.Defs

/-!
# Multiple-maximal hypotheses modulo the odd core

For a finite N2 group satisfying Hypothesis One at a Sylow two-subgroup,
with two distinct maximal two-locals containing that Sylow, the quotient by
its odd core satisfies the same hypotheses at the image Sylow. This is the
elementary quotient reduction for the multiple-maximal configuration in
Sections 5 and 11 of `refs/latex/stellmacher-n-group.tex`; it asserts no
Baumann stability or terminal classification.

Every quotient two-subgroup lifts from a Sylow of its inverse image. The
imported odd-kernel normalizer theorem therefore makes each quotient local
a surjective image of an ambient local, proving N2 descent. The imported
local-correspondence theorem transports characteristic two and distinct
maximal locals over the Sylow; the quotient-core theorem supplies the trivial
two-core. The cardinal product formula gives even order in the quotient.
Finally, a strongly embedded quotient subgroup would have strongly embedded
inverse image: Cauchy's theorem supplies an involution in that inverse image,
and no ambient involution can vanish in the odd kernel. These reductions
supply every field of the quotient Hypothesis One without extra assumptions.
-/

namespace Stellmacher.SectionEleven

private theorem exists_two_subgroup_lift
    {H K : Type*} [Group H] [Group K] [Finite H]
    (quotient : H →* K) (hsurj : Function.Surjective quotient)
    (Q : Subgroup K) (hQ : IsPGroup 2 Q) :
    ∃ T : Subgroup H, IsPGroup 2 T ∧ T.map quotient = Q := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let preimage := Q.comap quotient
  let restriction : preimage →* Q :=
    (quotient.comp preimage.subtype).codRestrict Q (fun element => element.property)
  have hrestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hlift⟩ := hsurj element
    refine ⟨⟨lift, ?_⟩, Subtype.ext hlift⟩
    change quotient lift ∈ Q
    rw [hlift]
    exact element.property
  let sylow : Sylow 2 preimage := Sylow.nonempty.some
  let mapped := sylow.mapSurjective hrestriction
  have htop : (mapped : Subgroup Q) = ⊤ :=
    (mapped.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  refine ⟨(sylow : Subgroup preimage).map preimage.subtype,
    sylow.isPGroup'.map preimage.subtype, ?_⟩
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr (Subgroup.map_subtype_le _)
  · intro element helement
    have hmem : (⟨element, helement⟩ : Q) ∈ (mapped : Subgroup Q) := by
      rw [htop]
      trivial
    obtain ⟨lift, hlift, heq⟩ := hmem
    exact ⟨lift, ⟨lift, hlift, rfl⟩, congrArg Subtype.val heq⟩

private theorem nTwo_oddCore_quotient
    {H : Type*} [Group H] [Finite H] (hN2 : Stellmacher.IsNTwoGroup H) :
    Stellmacher.IsNTwoGroup (H ⧸ pPrimeCore 2 H) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let quotient := QuotientGroup.mk' (pPrimeCore 2 H)
  intro overgroup hlocal
  obtain ⟨Q, hQne, hQ, rfl⟩ := hlocal
  obtain ⟨T, hT, hmap⟩ := exists_two_subgroup_lift quotient
    (QuotientGroup.mk'_surjective _) Q hQ
  have hTne : T ≠ ⊥ := by
    intro hbot
    apply hQne
    rw [← hmap, hbot, Subgroup.map_bot]
  let : Fact (IsPGroup 2 T) := ⟨hT⟩
  have hnormalizer : Subgroup.normalizer (Q : Set (H ⧸ pPrimeCore 2 H)) =
      (Subgroup.normalizer (T : Set H)).map quotient := by
    rw [← hmap]
    exact normalizer_map_quotient_eq_map_normalizer 2 T (pPrimeCore 2 H)
      inferInstance (pPrimeCore_coprime_card (p := 2) (G := H))
  rw [hnormalizer]
  let : Group.IsSolvable (Subgroup.normalizer (T : Set H)) :=
    hN2 _ ⟨T, hTne, hT, rfl⟩
  exact Group.isSolvable_of_surjective (quotient.subgroupMap_surjective _)

private theorem even_oddCore_quotient
    {H : Type*} [Group H] [Finite H] (heven : Even (Nat.card H)) :
    Even (Nat.card (H ⧸ pPrimeCore 2 H)) := by
  apply even_iff_two_dvd.mpr
  have hdiv := even_iff_two_dvd.mp heven
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 H)] at hdiv
  exact (pPrimeCore_coprime_card (p := 2) (G := H)).dvd_mul_right.mp hdiv

private theorem involution_oddCore_quotient
    {H : Type*} [Group H] [Finite H] {element : H}
    (helement : IsInvolution element) :
    IsInvolution (QuotientGroup.mk' (pPrimeCore 2 H) element) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, by simp only [← map_pow, helement.2, map_one]⟩
  intro hvanish
  have hmem := (QuotientGroup.eq_one_iff (N := pPrimeCore 2 H) element).mp hvanish
  have horder : orderOf element = 2 := orderOf_eq_prime helement.2 helement.1
  have hdiv : 2 ∣ Nat.card (pPrimeCore 2 H) := by
    simpa only [horder] using (pPrimeCore 2 H).orderOf_dvd_natCard hmem
  have hcop := Nat.Coprime.of_dvd_right hdiv
    (pPrimeCore_coprime_card (p := 2) (G := H))
  norm_num at hcop

private theorem stronglyEmbedded_oddCore_comap
    {H : Type*} [Group H] [Finite H]
    (M : Subgroup (H ⧸ pPrimeCore 2 H)) (hM : IsStronglyEmbedded M) :
    IsStronglyEmbedded (M.comap (QuotientGroup.mk' (pPrimeCore 2 H))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let quotient := QuotientGroup.mk' (pPrimeCore 2 H)
  let preimage := M.comap quotient
  let restriction : preimage →* M :=
    (quotient.comp preimage.subtype).codRestrict M (fun element => element.property)
  have hrestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hlift⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 H) element
    refine ⟨⟨lift, ?_⟩, Subtype.ext hlift⟩
    change quotient lift ∈ M
    rw [hlift]
    exact element.property
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply hM.1
    apply top_unique
    intro element _
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 H) element
    have hmem : lift ∈ M.comap quotient := by
      rw [htop]
      trivial
    exact hmem
  · obtain ⟨element, hmem, hinvolution⟩ := hM.2.1
    have hdiv : 2 ∣ Nat.card M := by
      simpa only [orderOf_eq_prime hinvolution.2 hinvolution.1] using
        M.orderOf_dvd_natCard hmem
    obtain ⟨lift, hlift⟩ := exists_prime_orderOf_dvd_card' (G := preimage) 2
      (hdiv.trans (Subgroup.card_dvd_of_surjective restriction hrestriction))
    have hliftH : orderOf (lift : H) = 2 := by simpa using hlift
    have hinvolution := (orderOf_eq_prime_iff.mp hliftH)
    exact ⟨lift, lift.property, hinvolution.2, hinvolution.1⟩
  · intro actor hactor element helement hinvolution
    apply hM.2.2 (quotient actor) hactor (quotient element) ?_
      (involution_oddCore_quotient hinvolution)
    refine ⟨helement.1, ?_⟩
    obtain ⟨preconjugate, hpreconjugate, heq⟩ := helement.2
    change actor * preconjugate * actor⁻¹ = element at heq
    refine ⟨quotient preconjugate, hpreconjugate, ?_⟩
    change quotient actor * quotient preconjugate * (quotient actor)⁻¹ = quotient element
    simpa only [map_mul, map_inv] using congrArg quotient heq

/-- The N2 condition, Hypothesis One, and two distinct maximal locals over the
Sylow descend through the odd-core quotient. -/
public theorem multiple_maximal_oddCore_quotient_setup
    {H : Type*} [Group H] [Finite H] (S0 : Sylow 2 H)
    (hN2 : Stellmacher.IsNTwoGroup H)
    (hyp : Stellmacher.SectionsFiveToSeven.HypothesisOne H S0)
    (hmultiple : ∃ M1 M2 : Subgroup H, M1 ≠ M2 ∧ IsMaximalTwoLocal M1 ∧
      IsMaximalTwoLocal M2 ∧ (S0 : Subgroup H) ≤ M1 ∧ (S0 : Subgroup H) ≤ M2) :
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let Sbar := S0.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 H))
    Stellmacher.IsNTwoGroup (H ⧸ pPrimeCore 2 H) ∧
    Stellmacher.SectionsFiveToSeven.HypothesisOne (H ⧸ pPrimeCore 2 H) Sbar ∧
    ∃ M1 M2 : Subgroup (H ⧸ pPrimeCore 2 H),
      M1 ≠ M2 ∧ IsMaximalTwoLocal M1 ∧ IsMaximalTwoLocal M2 ∧
      (Sbar : Subgroup (H ⧸ pPrimeCore 2 H)) ≤ M1 ∧
      (Sbar : Subgroup (H ⧸ pPrimeCore 2 H)) ≤ M2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlocal : ∀ U : Subgroup H, IsTwoLocal U → (S0 : Subgroup H) ≤ U →
      Stellmacher.IsCharacteristicTwoType U := fun U hU hSU =>
    (hyp.local_solvable_characteristicTwo U hU hSU).2
  obtain ⟨hlocalq, hmultipleq⟩ :=
    multiple_maximal_oddCore_quotient_local_setup S0 hlocal hmultiple
  have hnTwo := nTwo_oddCore_quotient hN2
  refine ⟨hnTwo, ?_, hmultipleq⟩
  refine ⟨even_oddCore_quotient hyp.even_order, ?_, ?_, ?_⟩
  · intro overgroup hlocal hSylow
    exact ⟨hnTwo overgroup hlocal, hlocalq overgroup hlocal hSylow⟩
  · exact twoCore_oddCore_quotient_eq_bot_of_multiple_maximal S0 hlocal hmultiple
  · rintro ⟨overgroup, hstrong⟩
    exact hyp.no_strongly_embedded
      ⟨overgroup.comap (QuotientGroup.mk' (pPrimeCore 2 H)),
        stronglyEmbedded_oddCore_comap overgroup hstrong⟩

end Stellmacher.SectionEleven
