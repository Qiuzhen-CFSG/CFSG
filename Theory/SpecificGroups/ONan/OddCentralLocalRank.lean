module
public import Theory.SpecificGroups.ONan.E9A4.Inverters
public import Theory.SpecificGroups.ONan.E9A4.Embedding
public import Theory.SpecificGroups.Alternating.E9A4CentralLift.OddKernel
public import Theory.SpecificGroups.Alternating.E9A4LocalRank
public import Theory.GroupTheory.CentralThreeInvertedPlane
public import Theory.GroupTheory.CentralExtensionPartialInversion
public import Theory.Quasithin.CentralThreeLocalRank.DivisibleCenter
public import Theory.Quasithin.CoprimeLocalRank

/-!
# The O'Nan obstruction in every odd central extension

The actual partial inverter forces arbitrary lifts of the marked commuting
cubics to commute. Each cubic has an actual cubic lift, constructed as a
commutator with a lift of its inverter. The normal four-group lifts through
an odd central kernel, yielding an elementary nine faithful modulo the center
inside a genuine two-local. If three divides the center, a central cubic
raises its rank to three. Otherwise coprime local-rank transport applies to
the actual E₉ × A₄ subgroup of the quotient.

This proves the odd-cover O'Nan case of Aschbacher–Smith A.2.19, printed p.41,
without a universal-cover presentation or a multiplier hypothesis.
-/
namespace ONan.OddCentralLocalRank
open Subgroup
open scoped commutatorElement
open Theory.SpecificGroups.E9A4 (Source Coord next homOfTransitions)

private theorem hom_generators (i : Fin 4) :
    homOfTransitions E9A4.generators E9A4.normalForm_next
      (Theory.SpecificGroups.E9A4.generators i) = E9A4.generators i := by
  have hs : Theory.SpecificGroups.E9A4.generators i =
      Theory.SpecificGroups.E9A4.sourceForm (next ((0, 0), 0) i) := by
    simpa only [show Theory.SpecificGroups.E9A4.sourceForm ((0, 0), 0) = 1 from rfl,
      one_mul] using (Theory.SpecificGroups.E9A4.next_spec ((0, 0), 0) i).symm
  change Theory.SpecificGroups.E9A4.candidate E9A4.generators _ = _
  rw [hs, Theory.SpecificGroups.E9A4.candidate_sourceForm]
  exact (E9A4.normalForm_next ((0, 0), 0) i).trans (one_mul _)

/-- The two actual inverter words construct commuting cubic lifts in every
central extension of the O'Nan model. -/
public theorem exists_commuting_cubic_lifts
    {G : Type*} [Group G] (π : G →* Model) (hπ : Function.Surjective π)
    (hk : π.ker ≤ center G) :
    ∃ x t : G, x ^ 3 = 1 ∧ t ^ 3 = 1 ∧ Commute x t ∧
      π x = E9A4.generators 0 ∧ π t = E9A4.generators 3 := by
  let j := homOfTransitions E9A4.generators E9A4.normalForm_next
  have hx : E9A4.generators 0 ^ 3 = 1 := by
    rw [← hom_generators, ← map_pow]
    rw [show Theory.SpecificGroups.E9A4.generators 0 ^ 3 = 1 by decide +kernel, map_one]
  have ht : E9A4.generators 3 ^ 3 = 1 := by
    rw [← hom_generators, ← map_pow]
    rw [show Theory.SpecificGroups.E9A4.generators 3 ^ 3 = 1 by decide +kernel, map_one]
  have hxt : Commute (E9A4.generators 0) (E9A4.generators 3) := by
    rw [← hom_generators 0, ← hom_generators 3]
    exact (show Commute (Theory.SpecificGroups.E9A4.generators 0)
      (Theory.SpecificGroups.E9A4.generators 3) by change _ * _ = _ * _; decide +kernel).map j
  obtain ⟨X, hX⟩ := hπ (E9A4.generators 0)
  obtain ⟨T, hT⟩ := hπ (E9A4.generators 3)
  obtain ⟨S, hS⟩ := hπ E9A4.Inverters.partialInverter
  obtain ⟨R, hR⟩ := hπ E9A4.Inverters.cubicInverter
  have hxc := π.inverted_cubic_commutator_lift hk X S ((congrArg (fun a : Model => a ^ 3) hX).trans hx)
    (by rw [hS, hX]; exact E9A4.Inverters.partial_inverts)
  have htc := π.inverted_cubic_commutator_lift hk T R ((congrArg (fun a : Model => a ^ 3) hT).trans ht)
    (by rw [hR, hT]; exact E9A4.Inverters.cubic_inverts)
  have hxπ : π ⁅S, X⁆ = E9A4.generators 0 := hxc.1.trans hX
  have htπ : π ⁅R, T⁆ = E9A4.generators 3 := htc.1.trans hT
  refine ⟨⁅S, X⁆, ⁅R, T⁆, hxc.2, htc.2, ?_, hxπ, htπ⟩
  exact CentralExtension.commute_lifts_of_partial_inversion π hπ hk _ _
    E9A4.Inverters.partialInverter (by decide : Nat.Coprime 3 2) hx hxt
    E9A4.Inverters.partial_inverts E9A4.Inverters.partial_commutes _ _ hxπ htπ

/-- An odd center and the literal O'Nan quotient give a faithful elementary
nine in a nontrivial two-subgroup normalizer. -/
public theorem exists_two_local_lift
    {G : Type*} [Group G] [Finite G]
    (ho : Odd (Nat.card (center G))) (e : G ⧸ center G ≃* Model) :
    ∃ (Q : Subgroup G) (f : Multiplicative (ZMod 3 × ZMod 3) →* G),
      Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
        Function.Injective ((QuotientGroup.mk' (center G)).comp f) ∧
        ∀ a, f a ∈ normalizer (Q : Set G) := by
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = center G := by
    ext a
    change e (QuotientGroup.mk' (center G) a) = 1 ↔ a ∈ center G
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff a
  obtain ⟨x, t, hx, ht, hxt, hpx, hpt⟩ :=
    exists_commuting_cubic_lifts π hπ (by rw [hker])
  let j := homOfTransitions E9A4.generators E9A4.normalForm_next
  have hj : Function.Injective j := Theory.SpecificGroups.E9A4.homOfTransitions_injective
    E9A4.generators E9A4.normalForm_next E9A4.normalForm_injective
  obtain ⟨Q, f, hQ, hQp, hf, hn⟩ :=
    Theory.SpecificGroups.E9A4.local_lift_of_commuting_cubic_lifts_of_odd_kernel
      π hπ (by rw [hker]) (by rwa [hker]) j hj x t hx ht hxt
      (hpx.trans (hom_generators 0).symm) (hpt.trans (hom_generators 3).symm)
  refine ⟨Q, f, hQ, hQp, ?_, hn⟩
  intro a b hab
  apply hf
  exact congrArg e hab

/-- Every finite odd central extension of the actual O'Nan model has
three-rank at least three in a genuine two-local subgroup. -/
public theorem three_le_twoLocalPrimeRank
    {G : Type*} [Group G] [Finite G]
    (ho : Odd (Nat.card (center G))) (e : G ⧸ center G ≃* Model) :
    3 ≤ twoLocalPrimeRank 3 G := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  by_cases hd : 3 ∣ Nat.card (center G)
  · obtain ⟨Q, f, hQ, hp, hf, hn⟩ := exists_two_local_lift ho e
    apply Theory.Quasithin.three_le_twoLocalPrimeRank_of_three_dvd_center hd Q hp hQ f hf hn
    · decide +kernel
    · rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod]
      norm_num [Nat.card_zmod]
  · let π := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
    have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = center G := by
      ext a
      change e (QuotientGroup.mk' (center G) a) = 1 ↔ a ∈ center G
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff a
    have hc : Nat.Coprime 3 (Nat.card π.ker) := by
      rw [hker]
      exact (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hd
    exact (Theory.Quasithin.three_le_twoLocalPrimeRank_of_e9_prod_a4_embedding
      E9A4.embedding E9A4.embedding_injective).trans
      (twoLocalPrimeRank_le_of_surjective_of_coprime 3 π hπ hc)

/-- The literal O'Nan quotient is incompatible with quasithinness when the
ambient finite group has odd center. -/
public theorem not_quasithin
    {G : Type*} [Group G] [Finite G]
    (ho : Odd (Nat.card (center G))) (e : G ⧸ center G ≃* Model) :
    ¬ IsQuasithin G := by
  intro h
  have hl := isQuasithin_iff_twoLocalPrimeRank.mp h 3 (by decide) (by decide)
  have hg := three_le_twoLocalPrimeRank ho e
  omega
end ONan.OddCentralLocalRank
