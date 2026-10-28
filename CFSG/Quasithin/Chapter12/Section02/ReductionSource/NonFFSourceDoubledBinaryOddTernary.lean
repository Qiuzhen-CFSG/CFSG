module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddTernary
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryOddUnitary

/-!
# Odd ternary exclusion on the original binary odd-normalizer witness

The actual Sylow two-generator calculations exclude both odd prime-square
ternary families from the selected component's outer automorphism group.
In the inner branch, its rank-six central quotient also excludes these
families. The original H-star witness retains the same prime-order actor,
whole orbit, component, full center and residual section, with seven outer
families remaining. No additional callback is added.

The pushing-up alternative, placed component and remaining outer families
still require exclusion before odd-normalizer control follows.
Source: Aschbacher–Smith 4.4.10–12 and 7.3.4, 7.6.1,
printed pp.621–622,699,702, refs/quasithin.pdf.
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

/-- The same original component, with prime-field and prime-square ternary exclusions. -/
@[expose] def BinaryOddTernaryReducedCase (A : Subgroup G) : Prop :=
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
      ∃ j : oddActorResidual L A →* K ⧸ center K, IsPGroup 2 j.ker ∧
        ∃ f : j.range →* BinaryLinearThree.Group, Function.Surjective f) ∨
     ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
        Function.Surjective f) ∧
       DoubledBinaryOddTernary.RemainingOuterModel (K ⧸ center K)))

private theorem binary_odd_ternary_reduction {A : Subgroup G}
    (hc : D.BinaryOddUnitaryReducedCase A) : D.BinaryOddTernaryReducedCase A := by
  obtain ⟨K,hK,hm,hout,hcore,hmodel,h2,h3,hcase⟩ := hc
  let : IsQuasisimple K := hK.2
  have hx : 6 ≤ primeRank 2 (K ⧸ center K) ∨
      ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
        Function.Surjective f := by
    rcases hcase with hi | ⟨ho,_⟩
    · exact Or.inl hi.2.2.2.2.1
    · exact Or.inr ho
  refine ⟨K,hK,hm,hout,hcore,hmodel,h2,h3,DoubledBinaryOddTernary.square_model_exclusions hx,?_⟩
  rcases hcase with hi | ⟨ho,_⟩
  · exact Or.inl hi
  · exact Or.inr ⟨ho,DoubledBinaryOddTernary.remaining_outer_models hmodel ho⟩

/-- The selected component has the full original inner placement or one of
seven remaining outer families; the ternary square-field rows are excluded. -/
theorem sourceOrbit_binary_oddNormalizer_ternary_reduced
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    D.BinaryOddTernaryReducedCase A := by
  exact D.binary_odd_ternary_reduction
    (D.sourceOrbit_binary_oddNormalizer_unitary_reduced h hd F hF hmodel A hne hAC ho hu hout)

/-- Actual H-star application of both ternary square-field exclusions. The prime-order
odd actor, whole-orbit centralization and escaping normalizer are retained. -/
theorem sourceOrbit_binary_globalW_or_ternary_reduced_oddLocal
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
        D.BinaryOddTernaryReducedCase A) := by
  rcases D.sourceOrbit_binary_globalW_or_unitary_reduced_oddLocal h hd hmany hnon F hF hmodel with hw | hx
  · exact Or.inl hw
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hcase⟩ := hx
  refine Or.inr ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  exact hcase.imp_right (D.binary_odd_ternary_reduction)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
