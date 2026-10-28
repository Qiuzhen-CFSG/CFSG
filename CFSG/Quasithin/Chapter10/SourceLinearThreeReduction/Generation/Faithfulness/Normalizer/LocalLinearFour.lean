module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalBounds
public import CFSG.Quasithin.ChapterA.Section02.OddBModelTwoRank
public import Theory.SpecificGroups.PSL4.OddFrattiniSixteen
public import Theory.SpecificGroups.PSL4.FermatSeven

/-!
# Excluding Fermat-field PSL₄ normalizer components

The Sylow Frattini bound places the original residual in the full covering
component. The projective two-rank bound and absence of seven from the model
order then contradict the doubled odd ranks on the fixed local module.
All quotient maps and the full covering center remain unchanged.

Source: the PSL₄ row of Aschbacher--Smith Theorem B in the 4.4.3 argument,
printed p.622, as used in 10.2.3(2), printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Fermat PSL₄ is excluded using its actual projective order and Sylow Frattini bound. -/
theorem source_nonnormal_oddNormalizer_no_fermat_linear_four_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (V : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hc : pCore 2 K = ⊥) {r : ℕ} (hf : ∃ k : ℕ, r = 2 ^ (2 ^ k) + 1)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 4 r) : False := by
  have ho : Odd r := by
    obtain ⟨k,rfl⟩ := hf
    exact (even_two.pow_of_ne_zero (by positivity)).add_one
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hbound : ∃ P : Sylow 2 (K ⧸ center K), Nat.card (P ⧸ frattini P) ≤ 32 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    refine ⟨P,?_⟩
    rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup _))]
    exact (Theory.SpecificGroups.PSL4.OddFrattiniSixteen.projective_frattini_le
      (hF.symm ▸ ho) (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card
        (k := 1) ho (by simpa only [pow_one] using hF)) Q).trans (by decide)
  obtain ⟨P,hP⟩ := hbound
  apply source_nonnormal_oddNormalizer_no_placed_small_rank_component D hn V hVV hne hVX hNV B hBC hodd hBV K hc
    (source_local_oddPrimeActor_residual_le_of_smallFrattini
      D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout P hP)
  · exact (ChapterA.Section02.odd_psl_four_twoRank_le_six ho hm).trans (by decide)
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    have hseven : ¬ 7 ∣ Nat.card (K ⧸ center K) := by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.PSL4.fermat_seven_not_dvd hf hF
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hseven
    omega

end CFSG.Quasithin.Chapter10.LocalFixed
