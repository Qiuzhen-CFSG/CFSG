module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCore64OppositeComparison
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCore64Parameters
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCongruence

/-!
# Full normalizer closure in the abelian order-64 branch

The actual Baumann parabolic and its opposite source parabolic generate the
literal original join.  If the stabilizer normalizer preserves both literal
two-residuals, the source generation theorem gives the full normalizer bound.
If one residual is not preserved, the genuine collapsed odd-prime
configuration is recovered and the full order-64 parameter theorem forces its
prime to be 11 or 13.  All residuals, radicals, and the rank-twelve core are
kept as the original subgroups; no action on a Frattini quotient is promoted
to an action of `N_G(T₁)` on the full core.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding ChapterC.BinaryMS
namespace Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- In the genuine abelian order-64 branch, either both actual parabolic
residuals are normalized and the full source normalizer lies in the maximal
local, or a literal collapsed odd-prime obstruction remains, with its actual
prime forced to 11 or 13. -/
theorem normalizerEscape_fullCore64_full_normalizer_or_prime
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : IsMulCommutative (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))))
    (hcard : Nat.card ((commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype) = 64) :
    let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
    let J := localJoin T L
    let H := J ⊓ normalizer (ChapterB.baumann T₁ : Set G)
    ∃ K : Subgroup G, Data D K ∧ K ≠ H ∧ H ⊔ K = J ∧
      ⁅J.pCoreIn 2,localOrbit T L⁆ ≤
        (normalizer (T₁ : Set G) ⊔ H).pCoreIn 2 ∧
      (normalizer (T₁ : Set G) ≤ D.maximalLocal ∨
        ∃ H' P I : Subgroup G, ∃ p : ℕ,
          Data D H' ∧
          SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
            (residual H') P (enlargement T L H') I ∧
          enlargedResidual T L H' = componentOrbit I (T : Subgroup G) ∧
          p.Prime ∧ Odd p ∧
          ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
          (p % 8 = 3 ∨ p % 8 = 5) ∧
          (p % 24 = 11 ∨ p % 24 = 13) ∧
          (p = 11 ∨ p = 13) ∧
          (enlargement T L H').pCoreIn 2 ≠ ⊥ ∧
          residual H' < enlargedResidual T L H' ∧
          stabilizerIntersection T L H' =
            (T : Subgroup G) ⊓ enlargedResidual T L H' ∧
          (residual H').pCoreIn 2 ≤ (enlargedResidual T L H').pCoreIn 2) := by
  let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let J := localJoin T L
  let H := J ⊓ normalizer (ChapterB.baumann T₁ : Set G)
  obtain ⟨hH,hU⟩ := normalizerEscape_fullCore64_baumann_parabolic D s hout hc hcard
  obtain ⟨K,hK,hKH,hgen,_,_⟩ :=
    normalizerEscape_fullCore64_baumann_opposite_comparison D s hout hc hcard
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    selected_nonnormal s
  let f := originalLift s s.fixed_zero
  have obstruction (Q : Subgroup G) (hQ : Data D Q)
      (hN : ¬ normalizer (T₁ : Set G) ≤ normalizer (residual Q : Set G)) :
      ∃ H' P I : Subgroup G, ∃ p : ℕ,
        Data D H' ∧
        SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
          (residual H') P (enlargement T L H') I ∧
        enlargedResidual T L H' = componentOrbit I (T : Subgroup G) ∧
        p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧
        (p % 24 = 11 ∨ p % 24 = 13) ∧
        (p = 11 ∨ p = 13) ∧
        (enlargement T L H').pCoreIn 2 ≠ ⊥ ∧
        residual H' < enlargedResidual T L H' ∧
        stabilizerIntersection T L H' =
          (T : Subgroup G) ⊓ enlargedResidual T L H' ∧
        (residual H').pCoreIn 2 ≤ (enlargedResidual T L H').pCoreIn 2 := by
    obtain ⟨H',P,I,p,h',hs',hK',hp,ho,hm,hmod,hcore,hlt,hR,hc'⟩ :=
      CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.collapsedSmallOddPrimeEnlargement_of_not_normalizes
        hQ hn hN
    have hmod24 := h'.collapsed_small_prime_mod24 hn hs' hK' hp ho hm hmod hc'
    have hpEq := h'.collapsed_fullCore64_prime f hn hs' hK' hp ho hm hmod24 hc' hout hcard
    exact ⟨H',P,I,p,h',hs',hK',hp,ho,hm,hmod,hmod24,hpEq,hcore,hlt,hR,hc'⟩
  by_cases hNH : normalizer (T₁ : Set G) ≤ normalizer (residual H : Set G)
  · by_cases hNK : normalizer (T₁ : Set G) ≤ normalizer (residual K : Set G)
    · refine ⟨K,hK,hKH,hgen,hU,Or.inl ?_⟩
      exact normalizer_le_of_normalizes_pair hH hK hgen hNH hNK
    · obtain ⟨H',P,I,p,h',hs',hK',hp,ho,hm,hmod,hmod24,hpEq,hcore,hlt,hR,hc'⟩ :=
        obstruction K hK hNK
      exact ⟨K,hK,hKH,hgen,hU,Or.inr ⟨H',P,I,p,h',hs',hK',hp,ho,hm,hmod,
        hmod24,hpEq,hcore,hlt,hR,hc'⟩⟩
  · obtain ⟨H',P,I,p,h',hs',hK',hp,ho,hm,hmod,hmod24,hpEq,hcore,hlt,hR,hc'⟩ :=
      obstruction H hH hNH
    exact ⟨K,hK,hKH,hgen,hU,Or.inr ⟨H',P,I,p,h',hs',hK',hp,ho,hm,hmod,
      hmod24,hpEq,hcore,hlt,hR,hc'⟩⟩

end Parabolics
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
