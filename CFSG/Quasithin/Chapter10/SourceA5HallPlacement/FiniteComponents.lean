module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.CentralQuotientRank
public import CFSG.Quasithin.ChapterA.Section02.FiniteModelRankExclusions

/-!
# Finite-model exclusions for the actual odd normalizer component

The original nonnormal A₅ pair forces two-rank at least eight in K/Z(K).
The certified finite-model bounds exclude alternating degrees at most nine,
binary linear degrees four and five, and every sporadic Theorem B row except
J₄. The literal quotient equivalences are retained. The binary symplectic
six-space and J₄ remain explicit alternatives for further source arguments.
No component-normality or ambient strongly-quasithin premise is added.

Source: Aschbacher--Smith 4.4.12 and 10.2.3, printed pp.622 and745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterA.Section02 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual component quotient excludes all the finite rows controlled
by rank eight; the sporadic conclusion preserves the surviving J₄ equivalence. -/
theorem source_a5_oddNormalizer_component_finite_model_exclusions
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
          (normalizer (B : Set G)) ≤ K) :
    (∀ n : ℕ, n ≤ 9 → ¬ Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin n))) ∧
    (∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL (K ⧸ center K) n 2) ∧
    (IsTheoremBSporadicModel (K ⧸ center K) → Nonempty ((K ⧸ center K) ≃* Janko4.Model)) := by
  have hr := source_a5_oddNormalizer_component_centralQuotient_twoRank_ge_eight
    D e hn hp B hB hBC hBV hperm K hK houtK hFK
  exact ⟨fun _ hn => no_small_alternating_of_twoRank_ge_eight hr hn,
    fun _ hn => no_binary_linear_of_twoRank_ge_eight hr hn,
    theoremBSporadic_j4_of_twoRank_ge_eight hr⟩

/-- Apply the finite exclusions to the complete Theorem B output list for
the literal component central quotient, with all remaining families displayed. -/
theorem source_a5_oddNormalizer_component_remaining_theoremB_models
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
    (hmodel : IsTheoremBModel (K ⧸ center K)) :
    IsTheoremBOddModel (K ⧸ center K) ∨ IsBenderModel (K ⧸ center K) ∨
      (∃ f, IsRankTwoModel (K ⧸ center K) f) ∨
      ClassicalGroup.IsPSp (K ⧸ center K) 3 2 ∨
      Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  exact hmodel.remaining_of_twoRank_ge_eight
    (source_a5_oddNormalizer_component_centralQuotient_twoRank_ge_eight
      D e hn hp B hB hBC hBV hperm K hK houtK hFK)

end CFSG.Quasithin.Chapter10
