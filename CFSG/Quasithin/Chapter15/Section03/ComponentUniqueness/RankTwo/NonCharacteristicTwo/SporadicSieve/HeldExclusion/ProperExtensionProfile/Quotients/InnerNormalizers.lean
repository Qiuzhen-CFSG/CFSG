module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Candidates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients.NormalizerReduction
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Transport
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders

/-!
# Inner normalizers and the max5 branch

The certified Sylow conjugacies and the Frattini argument show that both literal
inner candidates are self-normalizing in Held. Their checked orders therefore
bound the corresponding full automorphism normalizer orders. The max5 word core
is a normal self-centralizing two-group, so the normalizer extension has F*=O₂.
The first order bound excludes nine without an exact automorphism-normalizer count.

Source: GLS3 Table 5.3p and Aschbacher--Smith 15.3.41--42, printed p.1138.
The pure-pair core calculation is separate from the max5 argument.
-/

public section
open Subgroup Theory.GroupTheory Held.LocalPairs
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile

open Held.TwoLocalCandidates Held.LocalPairs.SylowGeometry.Calculations
open Held.LocalPairs.PairCoverage.LocalActions

/-- Both literal inner candidates contain a self-normalizing Held Sylow subgroup. -/
theorem innerLocal_self_normalizing (i : Bool) :
    normalizer (innerLocal i : Set Held.He) = innerLocal i := by
  cases i
  · exact normalizer_eq_of_representative representative_isPGroup InnerNormalizer.normalizer_eq 2
  · obtain ⟨P, hP⟩ := exists_representative_sylow representative_isPGroup InnerNormalizer.normalizer_eq
    let T := P.mapSurjective (f := (MulAut.conj (RepresentativeImages.InnerImages.transporter false 0)).toMonoidHom)
      (MulAut.conj _).surjective
    have hT : (T : Subgroup Held.He) = candidateTwo false 0 := by
      change (P : Subgroup Held.He).map _ = _
      rw [hP]
      exact RepresentativeImages.InnerImages.representative_map false 0
    apply normalizer_eq_of_self_normalizing_sylow T (inner_self_normalizing T)
    rw [hT]
    exact le_sup_right

/-- The checked max5 word core already forces its intrinsic two-core to be
self-centralizing; equality with that word core is unnecessary. -/
theorem innerLocal_false_core_selfCentralizing :
    centralizer (pCore 2 (innerLocal false) : Set (innerLocal false)) ≤ pCore 2 (innerLocal false) := by
  have hcore : Cores.core 2 ≤ pCore 2 (subgroup 2) :=
    le_sSup ⟨Cores.core_normal 2, Cores.core_isPGroup 2⟩
  exact (centralizer_le hcore).trans (Cores.max5_selfCentralizing.trans hcore)

/-- The full max5 automorphism normalizer has characteristic two. -/
theorem candidate_false_characteristic_two
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    generalizedFitting (candidate false) = pCore 2 (candidate false) :=
  automorphismNormalizer_characteristic_two (innerLocal false) (innerLocal_self_normalizing false)
    innerLocal_false_core_selfCentralizing hreal hbound

/-- The full normalizer orders divide twice the checked inner orders. -/
theorem candidate_card_dvd (i : Bool)
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    Nat.card (candidate i) ∣ (if i then 18432 else 43008) := by
  have h := automorphismNormalizer_card_dvd_twice (innerLocal i) (innerLocal_self_normalizing i) hreal hbound
  cases i
  · change Nat.card (candidate false) ∣ Nat.card max5 * 2 at h
    simpa [Held.InvolutionFixedData.TwoB.max5_card] using h
  · change Nat.card (candidate true) ∣ Nat.card (Exhaustion.candidateProduct false 0) * 2 at h
    simpa [(Exhaustion.candidateOrders false 0).2.2] using h

/-- The first full automorphism normalizer has no factor of nine in its order. -/
theorem candidate_false_not_nine_dvd
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2) :
    ¬ 9 ∣ Nat.card (candidate false) :=
  fun h => (by decide : ¬ 9 ∣ 43008) (h.trans (candidate_card_dvd false hreal hbound))
end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
