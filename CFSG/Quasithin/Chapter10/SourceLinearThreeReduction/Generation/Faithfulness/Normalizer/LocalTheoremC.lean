module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalFiniteExclusions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalBinaryExclusions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalUnitaryThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalRankOneClosure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalTits
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalHeldNormalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalJankoFour
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalRee

/-!
# The shared Theorem C catalogue under local fixation

The fixed local orbit supplies the same literal perfect residual and moved
quotient geometry as the full-module proof. Its doubled automorphism ranks
also supply the size obstructions. The actual model markings now exclude
every shared C row, with no fixation of the full M-orbit. All covering
centers and relative normality are retained.
Source: Aschbacher--Smith 4.4.10--14 and 10.2.3(2), pp.621--625,745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
  (hVX : V = ⁅V,localOrbit T L⁆)
  (hNV : localJoin T L ≤ normalizer (V : Set G))

include hn hVV hne hVX hNV

/-- Every placed shared sporadic component contradicts the fixed local module. -/
theorem source_no_shared_sporadic_of_placed
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (B : Set G))) (hc : pCore 2 K = ⊥)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (K ⧸ center K)) : False := by
  rcases hm with ⟨name,hnot,⟨e⟩⟩ | ⟨e⟩
  · cases name with
    | m11 => exact source_nonnormal_oddNormalizer_no_placed_m11_component D hn V hVV hne hVX hNV B hBC hodd hBV K hFK e
    | m12 => exact source_nonnormal_oddNormalizer_no_placed_m12_component D hn V hVV hne hVX hNV B hBC hodd hBV K hFK e
    | m22 => exact source_nonnormal_oddNormalizer_no_placed_m22_component D hn V hVV hne hVX hNV B hBC hodd hBV K hFK e
    | m23 => exact source_nonnormal_oddNormalizer_no_placed_m23_component D hn V hVV hne hVX hNV B hBC hodd hBV K hFK e
    | m24 => exact source_nonnormal_oddNormalizer_no_placed_m24_component D hn V hVV hne hVX hNV B hBC hodd hBV K hFK e
    | j4 => exact source_nonnormal_oddNormalizer_no_placed_jankoFour_component D hn V hVV hne hVX hNV B hBC hodd hBV K hc hFK e
    | j3 => exact hnot rfl
    | he => exact source_nonnormal_oddNormalizer_no_placed_held_component D hn V hVV hne hVX hNV B hBC hodd hBV K hc hFK e
    | j2 =>
      change K ⧸ center K ≃* Sporadic.LeechRelated.J2.Carrier at e
      apply source_nonnormal_oddNormalizer_no_placed_small_rank_component D hn V hVV hne hVX hNV B hBC hodd hBV K hc hFK
      · rw [primeRank_congr 2 e]
        exact Sporadic.LeechRelated.J2.primeRank_two_le_seven
      · let : Fact (Nat.Prime 7) := ⟨by decide⟩
        rw [primeRank_congr 7 e]
        apply primeRank_le_one_of_square_not_dvd
        rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
        decide
    | hs =>
      change K ⧸ center K ≃* Sporadic.LeechRelated.HS.Carrier at e
      apply source_nonnormal_oddNormalizer_no_placed_small_rank_component D hn V hVV hne hVX hNV B hBC hodd hBV K hc hFK
      · rw [primeRank_congr 2 e]
        exact Sporadic.LeechRelated.HS.twoRank_le_four.trans (by decide)
      · let : Fact (Nat.Prime 7) := ⟨by decide⟩
        rw [primeRank_congr 7 e]
        apply primeRank_le_one_of_square_not_dvd
        rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
        decide
    | ru =>
      change K ⧸ center K ≃* Rudvalis.Model at e
      apply source_nonnormal_oddNormalizer_no_placed_small_rank_component D hn V hVV hne hVX hNV B hBC hodd hBV K hc hFK
      · rw [primeRank_congr 2 e]
        exact Rudvalis.primeRank_le_six.trans (by decide)
      · let : Fact (Nat.Prime 7) := ⟨by decide⟩
        rw [primeRank_congr 7 e]
        apply primeRank_le_one_of_square_not_dvd
        rw [Rudvalis.model_card]
        decide
  · exact source_nonnormal_oddNormalizer_no_placed_jankoOne_component D hn V hVV hne hVX hNV B hBC hodd hBV K hFK e.some

variable {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
  (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hBV : B ≤ centralizer (V : Set G))
  (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
  (K : Subgroup (normalizer (B : Set G)))
  (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
  (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
include hn hVV hne hVX hNV hp hB hBC hBV hperm hK hout

/-- Every shared C component is excluded from the actual locally fixed normalizer. -/
theorem source_nonnormal_oddNormalizer_no_theoremC_component
    (hc : pCore 2 K = ⊥)
    (hm : ChapterA.Section02.IsTheoremCModel (K ⧸ center K)) : False := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hFK := source_local_oddPrimeActor_residual_le_of_theoremC
    D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout hm
  cases hm with
  | alternating n hn9 e =>
    exact source_nonnormal_oddNormalizer_no_placed_alternating_component
      D hn V hVV hne hVX hNV B hBC hodd hBV K hFK (by omega) e.some
  | odd hm =>
    have hlo := source_local_oddActor_quotient_twoRank_ge_three
      D hn V hVV hne hVX hNV B hBC hodd hBV K hFK
    have hup := hm.twoRank_le_two
    omega
  | bender hm =>
    cases hm with
    | linear f hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact source_nonnormal_oddNormalizer_no_placed_binary_sl2_component
        D hn V hVV hne hVX hNV B hBC hodd hBV K hFK
        (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
    | unitary f hf hm =>
      exact source_nonnormal_oddNormalizer_no_placed_binary_unitary_three_component
        D hn V hVV hne hVX hNV B hBC hodd hBV K hFK (by omega) hm
    | suzuki m hm e =>
      exact source_nonnormal_oddNormalizer_no_placed_suzuki_component
        D hn V hVV hne hVX hNV B hBC hodd hBV K hFK (by omega) e.some
  | rank_two f hm =>
    cases hm with
    | linear hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact source_nonnormal_oddNormalizer_no_placed_psl3_component
        D hn V hVV hne hVX hNV B hBC hodd hBV K hFK e
    | symplectic hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact source_nonnormal_oddNormalizer_no_placed_sp4_component
        D hn V hVV hne hVX hNV B hBC hodd hBV K hFK
        (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
    | g2 hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      have hlarge : 2 < Nat.card F := by
        rw [hF]
        exact lt_of_lt_of_le (by decide : 2 < 2^2)
          (Nat.pow_le_pow_right (by decide) hf)
      exact source_nonnormal_oddNormalizer_no_placed_g2_component
        D hn V hVV hne hVX hNV B hBC hodd hBV K hFK hlarge e
    | triality hf hm =>
      obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f (by omega)).mp hm
      exact source_nonnormal_oddNormalizer_no_placed_triality_component
        D hn V hVV hne hVX hNV B hBC hodd hBV K hFK f (by omega) e
    | ree_f4 m hm _ e =>
      exact source_nonnormal_oddNormalizer_no_placed_ree_component
        D hn V hVV hne hVX hNV B hBC hodd hBV K hFK hm e.some
    | symplectic_derived _ e =>
      exact source_nonnormal_oddNormalizer_no_placed_alternating_component
        D hn V hVV hne hVX hNV B hBC hodd hBV K hFK (by decide : 6 ≤ 9)
        (e.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
    | g2_derived _ e =>
      exact source_nonnormal_oddNormalizer_no_placed_g2_derived_component
        D hn V hVV hne hVX hNV B hBC hodd hBV K hFK e.some
    | tits _ e =>
      exact source_nonnormal_oddNormalizer_no_placed_tits_component
        D hn V hVV hne hVX hNV B hBC hodd hBV K hFK e.some
  | linear_binary n hn45 hm =>
    exact source_nonnormal_oddNormalizer_no_placed_binary_linear_component
      D hn V hVV hne hVX hNV B hBC hodd hBV K hFK hn45 hm
  | sporadic hm =>
    exact source_no_shared_sporadic_of_placed
      D hn V hVV hne hVX hNV B hBC hodd hBV K hc hFK hm


end CFSG.Quasithin.Chapter10.LocalFixed
