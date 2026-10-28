module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.FiniteComponents
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentQuotientMarking
public import CFSG.Quasithin.ChapterA.Section02.PlacedFiniteModelExclusions

/-!
# The placed A₅ pair excludes the last finite exceptional rows

The literal residual image in K/Z(K) has five-rank two. Its binary normalizer
witness already bounds local five-rank below by two, hence ordinary five-rank
as well. The certified orders of J₄ and Sp₆(2) forbid this. Combining these
exclusions with the source two-rank-eight result removes all finite exceptional
rows of the complete Theorem B list, leaving its odd, Bender and rank-two
families with the original quotient and model equivalences.

Source: Aschbacher--Smith 4.4.10--12 and 10.2.3, printed pp.621--622 and745.
No component-normality or ambient strongly-quasithin premise is introduced.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterA.Section02 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original placed residual forces ordinary five-rank two in the literal central quotient. -/
theorem source_a5_oddNormalizer_component_quotient_fiveRank_ge_two_of_residual_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    2 ≤ primeRank 5 (K ⧸ center K) := by
  exact (source_a5_oddNormalizer_component_quotient_local_ranks_of_residual_le
    D e hn B hBC hodd hBV K hFK).2.trans (twoLocalPrimeRank_le_primeRank 5)

/-- The actual residual placement excludes both J₄ and binary projective symplectic six-space. -/
theorem source_a5_oddNormalizer_component_no_j4_or_binary_symplectic_six_of_residual_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    (¬ Nonempty ((K ⧸ center K) ≃* Janko4.Model)) ∧
      ¬ ClassicalGroup.IsPSp (K ⧸ center K) 3 2 := by
  have hr := source_a5_oddNormalizer_component_quotient_fiveRank_ge_two_of_residual_le
    D e hn B hBC hodd hBV K hFK
  exact ⟨no_j4_of_fiveRank_ge_two hr, no_binary_symplectic_six_of_fiveRank_ge_two hr⟩

/-- The original escaping component has only the three field-parameter families of Theorem B. -/
theorem source_a5_oddNormalizer_component_infinite_theoremB_families
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
      (∃ f, IsRankTwoModel (K ⧸ center K) f) := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n, he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  exact hmodel.infinite_families_of_twoRank_ge_eight_fiveRank_ge_two
    (source_a5_oddNormalizer_component_centralQuotient_twoRank_ge_eight
      D e hn hp B hB hBC hBV hperm K hK houtK hFK)
    (source_a5_oddNormalizer_component_quotient_fiveRank_ge_two_of_residual_le
      D e hn B hBC hodd hBV K hFK)

end CFSG.Quasithin.Chapter10
