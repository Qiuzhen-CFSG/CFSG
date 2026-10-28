module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Inputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.OddExponent
public import Theory.Representation.CharacteristicTwoIrreducibleRank
public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.SpecificGroups.Triality.StandardTwoRank.RankTable

/-!
# Triality F-module reduction through involution displacement

Every elementary two-subgroup embeds by conjugation in the automorphisms
of the irreducibly acting component, over any characteristic-two field.
Faithful descent through a perfect group's center and the genuine triality
rank table bound its rank by `5*n`. A nonidentity element of that subgroup
then suffices to exclude an offender if its binary displacement exceeds
`5*n`.

This proves the rank and fixed-space transfer, including central covers
and outer actors. Odd-exponent outer involutions are eliminated without a
representation estimate. Component displacement and even-exponent outer
displacement remain explicit inputs; the unconditional triality exclusion
is not asserted here.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Table 13 and
Lemma 8.6, internal pp.53, 56--57. The F inequality uses one copy of the
subgroup rank, rather than the two copies in the source's 2F inequality.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality

universe u v

/-- An even genuine triality parameter is a positive power of two. -/
theorem exists_binary_exponent {R : Type*} [Group R] {q : ℕ}
    (heven : Even q) (hmodel : _root_.Triality.Standard.IsTrialityGroupAt q R) :
    ∃ n : ℕ, 0 < n ∧ q = 2 ^ n := by
  obtain ⟨p, n, hp, hn, hq⟩ := (isPrimePow_nat_iff q).mp hmodel.isPrimePow
  have htwo : 2 = p := Nat.prime_eq_prime_of_dvd_pow Nat.prime_two hp
    (hq ▸ even_iff_two_dvd.mp heven)
  subst p
  exact ⟨n, hn, hq.symm⟩

variable {H : Type u} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
  [Group.IsPerfect N]

/-- The sharp rank bound applies to the actual elementary subgroup of the
ambient group, over the given field and through every perfect central cover. -/
theorem elementary_rank_le_five_mul {E W : Type v} [Field E] [CharP E 2]
    [AddCommGroup W] [Module E W] (σ : Representation E H W)
    [IsIrreducible (σ.comp N.subtype)] (hσ : Function.Injective σ)
    (n : ℕ) (hn : 0 < n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) (N ⧸ center N))
    (A : Subgroup H) (hA : IsElementaryTwo A) : rank A ≤ 5 * n := by
  have hH := CharacteristicTwoIrreducible.primeRank_le_automorphisms σ N hσ
  have hN := automorphism_primeRank_le_quotient_center (E := N) 2
  have hQ := _root_.Triality.Standard.TwoRank.automorphism_twoRank_eq_five_mul_of_model
    n hn hmodel
  have hb : primeRank 2 H ≤ 5 * n := hH.trans (hN.trans hQ.le)
  have hc := (primeRank_le_iff_elementary_card_le H).mp hb A hA.2
  have hl := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hl

/-- The component and outer involution estimates imply the exact absolute
fixed-space inequality, for the original subgroup and coefficient field. -/
theorem absoluteGap_of_involution_bounds (n : ℕ) (hn : 0 < n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) (N ⧸ center N))
    (hinner : ComponentInvolutionBound.{u, v} N n)
    (houter : OuterInvolutionBound.{u, v} H N n) : AbsoluteGap.{u, v} H N := by
  intro E W _ _ _ _ _ _ _ σ habs hirr hσ A hA
  let : IsIrreducible (σ.comp N.subtype) := hirr
  have hr := elementary_rank_le_five_mul N σ hσ n hn hmodel A hA
  obtain ⟨t, htA, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let : IsElementaryAbelian 2 A := hA.2
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
  have hd : 5 * n < Module.finrank (ZMod 2) E *
      Module.finrank E (LinearMap.range (σ t - LinearMap.id)) := by
    by_cases htN : t ∈ N
    · have hi : Function.Injective (σ.comp N.subtype) := hσ.comp Subtype.val_injective
      exact hinner E W (σ.comp N.subtype) hirr hi ⟨t, htN⟩
        (fun h => ht1 (congrArg Subtype.val h)) (Subtype.ext ht2)
    · exact houter E W σ habs hirr hσ t htN ht2
  exact hr.trans_lt (hd.trans_le (Nat.mul_le_mul_left _
    (displacement_finrank_le_fixedSpace_codim σ A htA)))

/-- Apply the shared endomorphism-field reduction to the two outstanding
involution bounds. This is the binary consumer of the conditional estimate. -/
theorem not_ff_of_involution_bounds
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) H V)
    [ρ.IsIrreducible] [IsIrreducible (ρ.comp N.subtype)] (hρ : Function.Injective ρ)
    (n : ℕ) (hn : 0 < n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) (N ⧸ center N))
    (hinner : ComponentInvolutionBound.{u, v} N n)
    (houter : OuterInvolutionBound.{u, v} H N n) : ¬ IsFFModule ρ :=
  not_ff_of_absoluteGap N ρ hρ
    (absoluteGap_of_involution_bounds N n hn hmodel hinner houter)

/-- Only even exponents require a proper-extension displacement estimate.
The odd case, including field order two, uses the proved placement theorem. -/
theorem absoluteGap_of_component_and_even_outer_bounds (n : ℕ) (hn : 0 < n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) (N ⧸ center N))
    (hinner : ComponentInvolutionBound.{u, v} N n)
    (houter : Even n → OuterInvolutionBound.{u, v} H N n) : AbsoluteGap.{u, v} H N := by
  apply absoluteGap_of_involution_bounds N n hn hmodel hinner
  rcases Nat.even_or_odd n with heven | hodd
  · exact houter heven
  · exact outerInvolutionBound_of_odd N n hn hodd hmodel

/-- Binary application after discharging all odd-exponent outer cases. The
component and even-exponent estimates are the two remaining source inputs. -/
theorem not_ff_of_component_and_even_outer_bounds
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) H V)
    [ρ.IsIrreducible] [IsIrreducible (ρ.comp N.subtype)] (hρ : Function.Injective ρ)
    (n : ℕ) (hn : 0 < n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) (N ⧸ center N))
    (hinner : ComponentInvolutionBound.{u, v} N n)
    (houter : Even n → OuterInvolutionBound.{u, v} H N n) : ¬ IsFFModule ρ :=
  not_ff_of_absoluteGap N ρ hρ
    (absoluteGap_of_component_and_even_outer_bounds N n hn hmodel hinner houter)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality
