module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedModels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryOddRanks

/-!
# Remaining models for the original placed binary-three component

The whole doubled orbit has elementary rank six in the original component
central quotient. Short fourth-power witnesses exclude J₂, J₃ and McL;
the established Mathieu and HS ranks leave only M₂₄, J₄, He and Ru from
the sporadic list. Alternating groups through degree nine and binary PSL₄
are also excluded. The literal residual section excludes binary PSL₂ by
its abelian Sylow subgroups, and Suzuki by its order prime to three.

This applies the source model inspection of 4.4.12 and the following
paragraph on printed p.622 to the same H-star witness. The original
prime-order actor, component, whole orbit, residual map, full central
quotient and two-group kernel are retained. No extra hypothesis is added.
The remaining Lie and four sporadic rows, three outer families and pushing-up
alternative still require their original geometric exclusions.
Source: Aschbacher--Smith 4.4.10--12, 7.3.4 and 7.6.1,
printed pp.621--623,699,702, refs/quasithin.pdf.
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

/-- The same component and residual map, with the placed model inspection
applied to the whole rank-six orbit and actual binary-three section. -/
@[expose] def BinaryPlacedModelsReducedCase (A : Subgroup G) : Prop :=
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
      DoubledBinaryPlacedModels.RemainingPlacedModel (K ⧸ center K) ∧
      (∀ p : ℕ, (∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) →
        ¬ ClassicalGroup.IsPSL (K ⧸ center K) 4 p) ∧
      ∃ j : oddActorResidual L A →* K ⧸ center K, IsPGroup 2 j.ker ∧
        ∃ f : j.range →* BinaryLinearThree.Group, Function.Surjective f) ∨
     ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
        Function.Surjective f) ∧
       DoubledBinaryOddWreath.RemainingOuterModel (K ⧸ center K)))

private theorem binary_placed_models_reduction {A : Subgroup G}
    (hc : D.BinaryOddRanksReducedCase A) : D.BinaryPlacedModelsReducedCase A := by
  obtain ⟨K,hK,hm,hout,hcore,hmodel,h2,h3,hsquare,hcase⟩ := hc
  refine ⟨K,hK,hm,hout,hcore,hmodel,h2,h3,hsquare,?_⟩
  rcases hcase with ⟨hn,hW,hR,hC,hr,hodd,hfour,j,hj,f,hf⟩ | ho
  · exact Or.inl ⟨hn,hW,hR,hC,hr,hodd,
      DoubledBinaryPlacedModels.remaining_placed_models hr hmodel ⟨j.range,f,hf⟩,
      hfour,j,hj,f,hf⟩
  · exact Or.inr ho

/-- Original odd-normalizer application of the finite and rank-one exclusions;
the chosen component and full central-quotient residual map are retained. -/
theorem sourceOrbit_binary_oddNormalizer_placed_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    D.BinaryPlacedModelsReducedCase A := by
  exact D.binary_placed_models_reduction
    (D.sourceOrbit_binary_oddNormalizer_ranks_reduced h hd F hF hmodel A hne hAC ho hu hout)

/-- The actual H-star witness has the restricted placed-model list.
The original actor, outer-section and pushing-up alternatives remain literal. -/
theorem sourceOrbit_binary_globalW_or_placed_models_oddLocal
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
        D.BinaryPlacedModelsReducedCase A) := by
  rcases D.sourceOrbit_binary_globalW_or_ranks_reduced_oddLocal h hd hmany hnon F hF hmodel with hw | hx
  · exact Or.inl hw
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hcase⟩ := hx
  refine Or.inr ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  exact hcase.imp_right (D.binary_placed_models_reduction)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
