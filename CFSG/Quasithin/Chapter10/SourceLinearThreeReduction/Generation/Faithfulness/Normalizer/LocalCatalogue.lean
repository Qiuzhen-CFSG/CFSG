module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalTheoremC
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalOddThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalOddG2
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalSymplecticFour
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalLinearFour
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalUnitaryFour
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalUnitaryFive
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalUnitaryClosure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalSmallFrattini

/-!
# Complete component exclusion from local fixation

Every Theorem B row of an escaping normal component is excluded using only
a nonzero fully moved local submodule fixed by the odd actor. The original
pair, actual model equivalences, whole covering center, and literal Sylow
normalizer action are retained. The previously completed full-module sieve
is not invoked with a weaker fixation premise.

Source: Aschbacher--Smith 4.4.3, 4.4.10--14 and 10.2.3(2), pp.619--625,745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- No actual Theorem B component survives the literal fixed local module. -/
theorem source_no_theoremB_component
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
    (hc : pCore 2 K = ⊥)
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) : False := by
  have hC := source_nonnormal_oddNormalizer_no_theoremC_component
    D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout hc
  cases hm with
  | alternating n hn9 e =>
    exact source_local_oddPrimeActor_no_alternating_component
      D hn V hVV hne hVX hNV B hBC hBV K hp hB hperm hK hout hn9 e.some
  | odd hm =>
    cases hm with
    | linear_two q ho h =>
      exact source_local_oddPrimeActor_no_odd_linear_two_component
        D hn V hVV hne hVX hNV B hBC hBV K hp hB hperm hK hout ho h
    | linear_three r e hr ho _ h =>
      exact source_nonnormal_oddNormalizer_no_odd_linear_three_component
        D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout ho.pow h
    | unitary_three r e hr ho _ h =>
      exact source_nonnormal_oddNormalizer_no_odd_unitary_three_component
        D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout ho.pow h
    | symplectic r hr ho h =>
      let : Fact r.Prime := ⟨hr⟩
      exact source_nonnormal_oddNormalizer_no_odd_symplectic_four_component
        D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout hc ho h
    | g2 r hr ho h =>
      let : Fact r.Prime := ⟨hr⟩
      exact source_nonnormal_oddNormalizer_no_odd_g2_component
        D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout hc ho h
    | linear_four r hr hf h =>
      exact source_nonnormal_oddNormalizer_no_fermat_linear_four_component
        D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout hc hf h
    | unitary_four s hs hpow h =>
      let : Fact s.Prime := ⟨hs⟩
      have ho : Odd s := by
        obtain ⟨b,hb⟩ := hpow
        have hb0 : b ≠ 0 := by
          intro he
          simp only [he,pow_zero] at hb
          have := hs.two_le
          omega
        exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp
          (show Even (s+1) from hb.symm ▸ even_two.pow_of_ne_zero hb0))
      exact source_nonnormal_oddNormalizer_no_odd_unitary_four_component
        D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout hc ho h
  | bender h => exact hC (.bender h)
  | rank_two f h =>
    cases h with
    | linear hf h => exact hC (.rank_two f (.linear hf h))
    | unitary_four hf h =>
      by_cases hf1 : f = 1
      · apply source_nonnormal_oddNormalizer_no_binary_unitary_four_two_component
          D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout
        simpa only [hf1,pow_one] using h
      · exact source_nonnormal_oddNormalizer_no_large_unitary_four_component
          D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout (by omega) h
    | unitary_five hf h =>
      apply source_nonnormal_oddNormalizer_no_unitary_five_component
        D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout
      simpa [hf] using h
    | symplectic hf h => exact hC (.rank_two f (.symplectic hf h))
    | g2 hf h => exact hC (.rank_two f (.g2 hf h))
    | triality hf h => exact hC (.rank_two f (.triality hf h))
    | ree_f4 m hm hf h => exact hC (.rank_two f (.ree_f4 m hm hf h))
    | symplectic_derived hf h => exact hC (.rank_two f (.symplectic_derived hf h))
    | g2_derived hf h => exact hC (.rank_two f (.g2_derived hf h))
    | tits hf h => exact hC (.rank_two f (.tits hf h))
  | linear_binary n hn45 h => exact hC (.linear_binary n hn45 h)
  | symplectic_binary h =>
    exact source_nonnormal_oddNormalizer_no_binary_symplectic_component
      D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout h
  | sporadic h =>
    rcases h with ⟨name,⟨e⟩⟩ | ⟨e⟩ | ⟨e⟩
    · by_cases hj : name = .j3
      · subst name
        exact source_nonnormal_oddNormalizer_no_jankoThree_component
          D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout hc e
      · exact hC (.sporadic (Or.inl ⟨name,hj,⟨e⟩⟩))
    · exact hC (.sporadic (Or.inr e))
    · exact source_nonnormal_oddNormalizer_no_mcl_component
        D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout hc e.some

end CFSG.Quasithin.Chapter10.LocalFixed
