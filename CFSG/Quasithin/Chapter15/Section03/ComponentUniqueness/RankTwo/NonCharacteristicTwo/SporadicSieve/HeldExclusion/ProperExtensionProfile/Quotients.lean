module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Candidates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients.OuterCore
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients.PureInnerCore
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Core quotient calculations for the two full Held local normalizers

Both full automorphism normalizers have F*=O₂. The max5 normalizer's order is
not divisible by nine. The pure-pair normalizer has order 18432 and two-core
of order 256, hence quotient order 72. The marked odd-factor centralizer and
coprime action exclude outer elements from its core; restriction to the normal
inner part then identifies that core with the certified intrinsic pure core.
Its self-centralization also passes to the full normalizer.

The final assembly discharges the inner core premises of the retained conditional
reductions. Only realization by the permutation normalizer and its outer quotient
bound remain as independent inputs. Coverage by these two normalizers belongs
to the separate proper-extension profile assembly. Source: the model inspection
in Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p.
-/

public section
open Subgroup Theory.GroupTheory Held.LocalPairs
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile

/-- Restriction to the relatively normal inner part transfers the intrinsic
core order once outer elements have been excluded from the full core. -/
theorem candidate_true_core_card_of_inner_containment
    (hcard : Nat.card (pCore 2 (innerLocal true)) = 256)
    (hinner : pCore 2 (candidate true) ≤
      (MulAut.innerSubgroup Held.He).subgroupOf (candidate true)) :
    Nat.card (pCore 2 (candidate true)) = 256 := by
  let I := (MulAut.innerSubgroup Held.He).subgroupOf (candidate true)
  let e : innerLocal true ≃* I := normalizerInnerEquiv (innerLocal true) (innerLocal_self_normalizing true)
  have hc : (pCore 2 I).map I.subtype = pCore 2 (candidate true) := by
    rw [pCore_eq_comap_of_normal]
    exact map_subgroupOf_eq_of_le hinner
  rw [← hc, card_map_of_injective I.subtype_injective,
    ← pCore_map_iso 2 e, card_map_of_injective e.injective]
  exact hcard

/-- The checked full order and the two remaining core facts give quotient order 72. -/
theorem candidate_true_quotient_card_of_inner_containment
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (hcard : Nat.card (pCore 2 (innerLocal true)) = 256)
    (hinner : pCore 2 (candidate true) ≤
      (MulAut.innerSubgroup Held.He).subgroupOf (candidate true)) :
    Nat.card (candidate true ⧸ pCore 2 (candidate true)) = 72 := by
  have hc := (pCore 2 (candidate true)).card_mul_index
  rw [candidate_true_core_card_of_inner_containment hcard hinner, candidate_true_card hreal hbound] at hc
  change 256 * Nat.card (candidate true ⧸ pCore 2 (candidate true)) = 18432 at hc
  omega

/-- Once the intrinsic inner core order is proved, no further outer-core
calculation is required for the quotient order. -/
theorem candidate_true_quotient_card_of_inner_core
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (hcard : Nat.card (pCore 2 (innerLocal true)) = 256) :
    Nat.card (candidate true ⧸ pCore 2 (candidate true)) = 72 :=
  candidate_true_quotient_card_of_inner_containment hreal hbound hcard
    (candidate_true_core_le_inner hreal hbound)

/-- Conditional assembly. Only the pure inner core order and its intrinsic
self-centralization remain explicit obligations. The full normalizer order,
absence of outer core elements, and max5 branch have all been discharged. -/
theorem normalizer_calculations_of_pure_core
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (hc : centralizer (pCore 2 (innerLocal true) : Set (innerLocal true)) ≤
      pCore 2 (innerLocal true))
    (hcard : Nat.card (pCore 2 (innerLocal true)) = 256) :
    (∀ i : Bool, generalizedFitting (candidate i) = pCore 2 (candidate i)) ∧
      (¬ 9 ∣ Nat.card (candidate false)) ∧
      Nat.card (candidate true ⧸ pCore 2 (candidate true)) = 72 := by
  refine ⟨?_, candidate_false_not_nine_dvd hreal hbound,
    candidate_true_quotient_card_of_inner_core hreal hbound hcard⟩
  intro i
  cases i
  · exact candidate_false_characteristic_two hreal hbound
  · exact automorphismNormalizer_characteristic_two (innerLocal true) (innerLocal_self_normalizing true) hc hreal hbound

/-- The full pure-pair normalizer has the same core order as its normal inner part. -/
theorem candidate_true_core_card
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    Nat.card (pCore 2 (candidate true)) = 256 :=
  candidate_true_core_card_of_inner_containment pure_inner_core_card
    (candidate_true_core_le_inner hreal hbound)

/-- The actual pure-pair normalizer modulo its intrinsic two-core has order 72. -/
theorem candidate_true_quotient_card
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    Nat.card (candidate true ⧸ pCore 2 (candidate true)) = 72 :=
  candidate_true_quotient_card_of_inner_core hreal hbound pure_inner_core_card

/-- Self-centralization of the certified inner core gives F*=O₂ in the full
pure-pair normalizer. -/
theorem candidate_true_characteristic_two
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    generalizedFitting (candidate true) = pCore 2 (candidate true) :=
  automorphismNormalizer_characteristic_two (innerLocal true)
    (innerLocal_self_normalizing true) pure_inner_core_selfCentralizing hreal hbound

/-- The three local calculations required by the proper-extension profile,
with every inner-core premise discharged on the literal candidates. The profile
assembly supplies realization, the outer bound and the independent local cover. -/
theorem normalizer_calculations
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    (∀ i : Bool, generalizedFitting (candidate i) = pCore 2 (candidate i)) ∧
      (¬ 9 ∣ Nat.card (candidate false)) ∧
      Nat.card (candidate true ⧸ pCore 2 (candidate true)) = 72 :=
  normalizer_calculations_of_pure_core hreal hbound
    pure_inner_core_selfCentralizing pure_inner_core_card

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
