module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.UnitaryRemainder
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.UnitaryFourExclusion

/-!
# The nonnormal odd-kernel normalizer theorem

Covering uniqueness disposes of a nontrivial normalizer two-core. Otherwise
its normal escaping component lies in Theorem B. The complete model sieve
leaves PSU₄ over a Mersenne prime, now excluded by the projective rank-five
bound. Thus every elementary odd section-kernel actor fixing the full module
has its entire ambient normalizer in M. No model or normalizer callback remains.
Source: the nonnormal case of Aschbacher--Smith4.4.3, printed pp.619--623,
as consumed by10.2.3(2), printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original nonnormal odd section-kernel normalizer is contained in M. -/
theorem source_nonnormal_oddKernel_normalizer
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hA : IsElementaryAbelian p A)
    (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hAV : A ≤ centralizer (D.fullModule : Set G))
    (hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G)) :
    normalizer (A : Set G) ≤ D.maximalLocal := by
  let := hA
  have hP := IsElementaryAbelian.isPGroup p A
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := hP.exists_card_eq
    rw [he]
    exact hp.pow
  have hu := source_nonnormal_oddPrimeActor_covering_uniqueness D hn hp A hP hAC hAV hAT
  by_cases hc : pCore 2 (normalizer (A : Set G)) = ⊥
  · obtain ⟨K,hK,hKn,_,hout,hcore,hmodel⟩ :=
      source_nonnormal_oddNormalizer_normal_component_of_twoCore D hn A hne hAC hodd hAV hc
    let := hKn
    have hr := source_nonnormal_oddNormalizer_remaining_models
      D hn A hAC hodd hAV hu K hK hout hcore hmodel
    have hr' := source_nonnormal_oddNormalizer_remaining_classical_models
      D hn hp A hP hAC hAV hAT K hK hout hcore hr
    obtain ⟨⟨s,hs,hpow,hm⟩,hFK,_⟩ :=
      source_nonnormal_oddNormalizer_unitary_four_models
        D hn hp A hP hAC hAV hAT K hK hout hcore hr'
    have ho : Odd s := by
      obtain ⟨b,hb⟩ := hpow
      have hb0 : b ≠ 0 := by
        intro he
        simp only [he,pow_zero] at hb
        have := hs.two_le
        omega
      exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp
        (show Even (s+1) from hb.symm ▸ even_two.pow_of_ne_zero hb0))
    exact (source_nonnormal_oddNormalizer_no_placed_odd_unitary_four_component
      D hn A hAC hodd hAV K hcore hFK ho hm).elim
  · obtain ⟨_,hIN,_,_⟩ := source_oddActor_normalizerJoin_input D A hAC hodd hAV
    obtain ⟨N,hN,hAN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
      (normalizer (A : Set G)) hc
    exact (hu.2.2 N hN (hIN.trans hAN)) ▸ hAN

omit D in
/-- The exact normalizer contract is proved, including all full covering components. -/
theorem source_nonnormalOddKernelNormalizer : SourceNonnormalOddKernelNormalizerAt T := by
  intro _ L E hn _ p hp ho A hne hA hAC hAV hAT
  let : Fact p.Prime := ⟨hp⟩
  exact source_nonnormal_oddKernel_normalizer E hn ho A hne hA hAC hAV hAT

end CFSG.Quasithin.Chapter10
