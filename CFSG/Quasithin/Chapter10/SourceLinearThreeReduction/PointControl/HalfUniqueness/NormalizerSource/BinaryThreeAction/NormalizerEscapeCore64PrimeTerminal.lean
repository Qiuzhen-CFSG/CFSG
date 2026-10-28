module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCore64FullNormalizer
public import Theory.Representation.BinaryPrimeDegree

/-!
# Terminal arithmetic for the retained 11/13 obstruction

The full-normalizer source theorem leaves only the literal collapsed
odd-prime rows with p equal to 11 or 13.  The native binary arithmetic fixes
the corresponding order of 2, while every original parabolic, radical, and
rank-twelve containment remains unchanged.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding ChapterC.BinaryMS
namespace Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The retained prime obstruction is terminally reduced to its exact
binary order: ten for p=11 and twelve for p=13. -/
theorem normalizerEscape_fullCore64_prime_terminal
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
          ((p = 11 ∧ orderOf (2 : ZMod p) = 10) ∨
            (p = 13 ∧ orderOf (2 : ZMod p) = 12)) ∧
          (enlargement T L H').pCoreIn 2 ≠ ⊥ ∧
          residual H' < enlargedResidual T L H' ∧
          stabilizerIntersection T L H' =
            (T : Subgroup G) ⊓ enlargedResidual T L H' ∧
          (residual H').pCoreIn 2 ≤ (enlargedResidual T L H').pCoreIn 2) := by
  obtain ⟨K,hK,hKH,hgen,hU,hmain⟩ :=
    normalizerEscape_fullCore64_full_normalizer_or_prime D s hout hc hcard
  rcases hmain with hmain | ⟨H',P,I,p,h',hs',hK',hp,ho,hm,hmod,hmod24,hpEq,
      hcore,hlt,hR,hc'⟩
  · exact ⟨K,hK,hKH,hgen,hU,Or.inl hmain⟩
  · have horder : (p = 11 ∧ orderOf (2 : ZMod p) = 10) ∨
        (p = 13 ∧ orderOf (2 : ZMod p) = 12) := by
      rcases hpEq with rfl | rfl
      · exact Or.inl ⟨rfl,Representation.BinaryPrimeDegree.orderOf_two_mod_eleven⟩
      · exact Or.inr ⟨rfl,Representation.BinaryPrimeDegree.orderOf_two_mod_thirteen⟩
    exact ⟨K,hK,hKH,hgen,hU,Or.inr ⟨H',P,I,p,h',hs',hK',hp,ho,hm,hmod,
      hmod24,hpEq,horder,hcore,hlt,hR,hc'⟩⟩

end Parabolics
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
