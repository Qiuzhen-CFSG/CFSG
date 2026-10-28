module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddRanks
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryOddWreath

/-!
# Excluding every odd model from the placed binary-three component

The original whole doubled orbit embeds in the component central quotient
with elementary rank six. The quaternion coordinate of the odd-index G₂
subgroup gives rank at most four. The actual determinant-one projective
four-space kernels give rank at most five in the symplectic, linear and
unitary rows. Together with the degree-two and degree-three bounds, these
exclude the complete odd Theorem B catalogue in the placed branch.

The selected H-star actor, full orbit, component, two-core, movement and
original residual section are retained. No source premise is added.
The three odd outer families and the pushing-up branch remain explicit.
Source: Aschbacher--Smith 4.4.12, 7.3.4 and 7.6.1,
printed pp.622,699,702, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open BinaryLinearThree
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The same component and original residual, with every odd model excluded
from the rank-six placed branch. -/
@[expose] def BinaryOddRanksReducedCase (A : Subgroup G) : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q) ∧
    (∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 p) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 p)) ∧
    (∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 (p^2)) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 (p^2))) ∧
    ((K.Normal ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
      6 ≤ primeRank 2 (K ⧸ center K) ∧
      ¬ ChapterA.Section02.IsTheoremBOddModel (K ⧸ center K) ∧
      (∀ p : ℕ, (∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) →
        ¬ ClassicalGroup.IsPSL (K ⧸ center K) 4 p) ∧
      ∃ j : oddActorResidual L A →* K ⧸ center K, IsPGroup 2 j.ker ∧
        ∃ f : j.range →* BinaryLinearThree.Group, Function.Surjective f) ∨
     ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
        Function.Surjective f) ∧
       DoubledBinaryOddWreath.RemainingOuterModel (K ⧸ center K)))

private theorem binary_odd_ranks_reduction {A : Subgroup G}
    (hc : D.BinaryOddWreathReducedCase A) : D.BinaryOddRanksReducedCase A := by
  obtain ⟨K,hK,hm,hout,hcore,hmodel,h2,h3,hsquare,hcase⟩ := hc
  refine ⟨K,hK,hm,hout,hcore,hmodel,h2,h3,hsquare,?_⟩
  rcases hcase with ⟨hn,hW,hR,hC,hr,hfour,j,hj,f,hf⟩ | ho
  · exact Or.inl ⟨hn,hW,hR,hC,hr,
      DoubledBinaryOddRanks.no_odd_model_of_rank_six hr,hfour,j,hj,f,hf⟩
  · exact Or.inr ho

/-- The same whole-orbit placement excludes every odd Theorem B model
from the original component, with its residual section and central kernel retained. -/
theorem sourceOrbit_binary_oddNormalizer_ranks_reduced
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    D.BinaryOddRanksReducedCase A := by
  exact D.binary_odd_ranks_reduction
    (D.sourceOrbit_binary_oddNormalizer_wreath_reduced h hd F hF hmodel A hne hAC ho hu hout)

/-- Actual H-star application: the placed component has no odd model.
The original odd actor and pushing-up alternative retain all their hypotheses. -/
theorem sourceOrbit_binary_globalW_or_ranks_reduced_oddLocal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ChapterE.globalW D.sourceOrbit T ≤ 1 ∨
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
        A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        ((∃ J P : Subgroup G,
          J ∈ muStar (normalizer (L : Set G)) L
            (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
          PushLE L (oddActorResidual L A) J ∧
          IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
          IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
          J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
        D.BinaryOddRanksReducedCase A) := by
  rcases D.sourceOrbit_binary_globalW_or_wreath_reduced_oddLocal h hd hmany hnon F hF hmodel with hw | hx
  · exact Or.inl hw
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hcase⟩ := hx
  refine Or.inr ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  exact hcase.imp_right (D.binary_odd_ranks_reduction)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
