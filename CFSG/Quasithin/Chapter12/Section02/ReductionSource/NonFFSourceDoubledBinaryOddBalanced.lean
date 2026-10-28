module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddBalanced
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedLocals

/-!
# The two degree-four outer exclusions on the original binary-three witness

The determinant-one wreath calculation rules out a binary-three outer
section for every Fermat PSL₄ and Mersenne PSU₄ model. Descent retains the full center of
the same original component. The chosen-module application keeps the
H-star prime-order actor, whole orbit, residual inclusion and quotient
maps, and the original maximal pushing-up alternative.

The outer branch now retains only odd-prime G₂. The
six surviving placed models and pushing-up still require their source
geometry; odd-normalizer control is not concluded here.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, as used by
7.3.4 and 7.6.1, printed pp.699,702, refs/quasithin.pdf.
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

/-- The exact original placed and outer alternatives after all rank-two local
exclusions. The earlier central-quotient residual map is retained. -/
@[expose] def BinaryBalancedReducedCase (A : Subgroup G) : Prop :=
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
      DoubledBinaryPlacedLocals.LocalData (K ⧸ center K) ∧
      DoubledBinaryPlacedLocals.RemainingPlacedModel (K ⧸ center K) ∧
      (∀ p : ℕ, (∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) →
        ¬ ClassicalGroup.IsPSL (K ⧸ center K) 4 p) ∧
      ∃ j : oddActorResidual L A →* K ⧸ center K, IsPGroup 2 j.ker ∧
        ∃ f : j.range →* BinaryLinearThree.Group, Function.Surjective f) ∨
     ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
        Function.Surjective f) ∧
       DoubledBinaryOddBalanced.RemainingOuterModel (K ⧸ center K)))

private theorem binary_balanced_reduction
    (A : Subgroup G) (hc : D.BinaryPlacedLocalsReducedCase A) :
    D.BinaryBalancedReducedCase A := by
  obtain ⟨K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,hcase⟩ := hc
  refine ⟨K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,?_⟩
  rcases hcase with hplaced | ⟨ho,_⟩
  · exact Or.inl hplaced
  · let : IsQuasisimple K := hK.2
    exact Or.inr ⟨ho,DoubledBinaryOddBalanced.remaining_outer_models hmodels ho⟩

/-- The two degree-four outer exclusions apply to the original odd-normalizer
witness without a new local premise. -/
theorem sourceOrbit_binary_oddNormalizer_balanced
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    D.BinaryBalancedReducedCase A := by
  exact D.binary_balanced_reduction A
    (D.sourceOrbit_binary_oddNormalizer_placed_locals h hd F hF hmodel A hne hAC ho hu hout)

/-- Apply the degree-four outer exclusions to the same H-star actor and
component, retaining the literal maximal pushing-up pair. -/
theorem sourceOrbit_binary_globalW_or_balanced_oddLocal
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
        D.BinaryBalancedReducedCase A) := by
  rcases D.sourceOrbit_binary_globalW_or_placed_locals_oddLocal h hd hmany hnon F hF hmodel with hw | hx
  · exact Or.inl hw
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hcase⟩ := hx
  refine Or.inr ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  exact hcase.imp_right (D.binary_balanced_reduction A)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
