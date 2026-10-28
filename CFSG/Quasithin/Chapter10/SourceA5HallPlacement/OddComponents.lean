module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.CentralQuotientRank
public import CFSG.Quasithin.ChapterA.Section02.OddBModelTwoRank

/-!
# Odd-model exclusions for the actual placed component

The original residual placement gives two-rank at least eight in the literal
central quotient. The complete odd Theorem B family has two-rank at most seven, so it is
excluded. The proof retains the exact field parameters, matrix models and
original residual placement, with no added normality premise.

Source: Aschbacher–Smith 4.4.3 and 4.4.12, printed p.622.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterA.Section02 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Eliminate all odd rows other than the three degree-four families, using the
literal original residual inside the selected normalizer component. -/
theorem source_a5_oddNormalizer_component_odd_four_dimensional
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    (hmodel : IsTheoremBOddModel (K ⧸ center K)) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSp (K ⧸ center K) 2 p) ∨
    (∃ r : ℕ, r.Prime ∧ (∃ k : ℕ, r = 2 ^ (2 ^ k) + 1) ∧
      ClassicalGroup.IsPSL (K ⧸ center K) 4 r) ∨
    (∃ s : ℕ, s.Prime ∧ (∃ b : ℕ, s + 1 = 2 ^ b) ∧
      ClassicalGroup.IsPSU (K ⧸ center K) 4 s) := by
  exact hmodel.four_dimensional_of_twoRank_ge_eight
    (source_a5_oddNormalizer_component_centralQuotient_twoRank_ge_eight
      D e hn hp B hB hBC hBV hperm K hK houtK hFK)

/-- The complete odd Theorem B family is impossible for the literal quotient
of a component containing the original residual. No normality premise is added. -/
theorem source_a5_oddNormalizer_component_no_odd_model
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    : ¬ IsTheoremBOddModel (K ⧸ center K) := by
  exact no_theoremB_odd_model_of_twoRank_ge_eight
    (source_a5_oddNormalizer_component_centralQuotient_twoRank_ge_eight
      D e hn hp B hB hBC hBV hperm K hK houtK hFK)

end CFSG.Quasithin.Chapter10
