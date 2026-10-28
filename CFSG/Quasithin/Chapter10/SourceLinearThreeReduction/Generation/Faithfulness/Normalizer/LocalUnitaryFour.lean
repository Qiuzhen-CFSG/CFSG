module
public import Theory.SpecificGroups.ClassicalUnitary.OddFourProjectiveRank
public import Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalBounds
public import CFSG.Quasithin.ChapterA.Section02.OddBModelTwoRank

/-!
# Residual placement and exclusion for odd PSU₄ components

The native Sylow Frattini bound places the original residual inside an
escaping odd-prime PSU₄ covering component. The refined projective two-rank bound is five, contradicting the
local module order divisible by 64. Full-module fixation is unnecessary.

Source: the PSU₄ row of Aschbacher--Smith Theorem B in the 4.4.3 argument,
printed p.622, as used in 10.2.3(2), printed p.745. The full covering center is retained.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual residual lies in every escaping odd prime-field PSU₄ covering component. -/
theorem source_nonnormal_oddNormalizer_unitary_four_residual_le
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
    {r : ℕ} [Fact r.Prime] (ho : Odd r)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 r) :
    ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  apply source_local_oddPrimeActor_residual_le_of_smallFrattini
    D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout P
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup _))]
  exact (Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.projective_frattini_le
    J ho hF hconj (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hF) Q).trans
    (by decide)

/-- The actual odd PSU₄ component is excluded by the local rank-five obstruction. -/
theorem source_nonnormal_oddNormalizer_no_odd_unitary_four_component
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
    (hc : pCore 2 K = ⊥) {r : ℕ} [Fact r.Prime] (ho : Odd r)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 r) : False := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  apply source_no_component_of_rank_five D hn V hVV hne hVX hNV B hBC hodd hBV K hc
    (source_nonnormal_oddNormalizer_unitary_four_residual_le D hn V hVV hne hVX hNV
      hp B hB hBC hBV hperm K hK hout ho hm)
  obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
  rw [primeRank_congr 2 e]
  exact Theory.SpecificGroups.ClassicalUnitary.odd_four_projective_twoRank_le_five J
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hF)

end CFSG.Quasithin.Chapter10.LocalFixed
