module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedLocals
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedModels

/-!
# Two-local exclusions on the original placed binary-three component

The whole original orbit W is a nontrivial two-subgroup moved by the odd
fixed residual R. After the actual inclusion of R in the chosen component
and passage through its full center, the image of W remains nontrivial:
a central image would contradict W = [W,R]. Its perfect normalizer still
has the original SL₃(2) quotient. The actual rank-one and rank-two parabolic
calculations therefore exclude every Bender and binary rank-two model.

The same H-star witness now leaves only PSL₅(2), PSp₆(2), M₂₄, J₄, He
and Ru in the placed branch. All original component, whole-orbit, residual,
centralizer and map markings are retained. The three outer families and
the pushing-up alternative remain explicit. This is the rank-two portion
of source 4.4.12, not the full odd-normalizer or binary weak-closure theorem.
Source: Aschbacher--Smith, printed pp.621--623,699,702, refs/quasithin.pdf.
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

/-- The actual residual inclusion and entire orbit supply the two-local
configuration through the original component's full central quotient. -/
theorem sourceOrbit_binary_oddNormalizer_component_local
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    DoubledBinaryPlacedLocals.LocalData (K ⧸ center K) := by
  let R := oddActorResidual L A
  let N := normalizer (A : Set G)
  let a : K.map N.subtype ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let i : R →* K := a.toMonoidHom.comp (inclusion hr)
  have hi : Function.Injective i := a.injective.comp (inclusion_injective hr)
  obtain ⟨_,hm,hWR,t,ht,hnt,q,hq,hker,e,he,E,hE,hV,hVt⟩ :=
    D.sourceOrbit_binary_odd_residual_coordinates h hd F hF hmodel A hAC ho
  let : _root_.Group.IsPerfect R := oddActorResidual_isPerfect L A
  exact DoubledBinaryPlacedLocals.localData_of_moved_subgroup R D.sourceOrbit
    (IsElementaryAbelian.isPGroup 2 D.sourceOrbit) D.sourceOrbit_weakClosure_setup.nontrivial
    (hWR.trans (pCoreIn_le 2 R))
    (((oddActorResidual_le L A).trans inf_le_left).trans D.sourceOrbit_component_normalizes)
    hm i hi e

/-- The exact original placed and outer alternatives after all rank-two local
exclusions. The earlier central-quotient residual map is retained. -/
@[expose] def BinaryPlacedLocalsReducedCase (A : Subgroup G) : Prop :=
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
       DoubledBinaryOddWreath.RemainingOuterModel (K ⧸ center K)))

private theorem binary_placed_locals_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (hc : D.BinaryPlacedModelsReducedCase A) :
    D.BinaryPlacedLocalsReducedCase A := by
  obtain ⟨K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,hcase⟩ := hc
  refine ⟨K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,?_⟩
  rcases hcase with ⟨hn,hW,hR,hC,hr,hodd,_,hfour,j,hj,f,hf⟩ | ho
  · have hl := D.sourceOrbit_binary_oddNormalizer_component_local h hd F hF hmodel A hAC ho K hR
    exact Or.inl ⟨hn,hW,hR,hC,hr,hodd,hl,hl.remaining_placed_models hr hmodels,hfour,j,hj,f,hf⟩
  · exact Or.inr ho

/-- All Bender and rank-two placed models are excluded on the original
odd-normalizer witness, without a new local premise. -/
theorem sourceOrbit_binary_oddNormalizer_placed_locals
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    D.BinaryPlacedLocalsReducedCase A := by
  exact D.binary_placed_locals_reduction h hd F hF hmodel A hAC ho
    (D.sourceOrbit_binary_oddNormalizer_placed_models h hd F hF hmodel A hne hAC ho hu hout)

/-- Apply the complete rank-two exclusion to the same H-star actor and
component. The original maximal pushing-up pair remains literal. -/
theorem sourceOrbit_binary_globalW_or_placed_locals_oddLocal
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
        D.BinaryPlacedLocalsReducedCase A) := by
  rcases D.sourceOrbit_binary_globalW_or_placed_models_oddLocal h hd hmany hnon F hF hmodel with hw | hx
  · exact Or.inl hw
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hcase⟩ := hx
  refine Or.inr ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  exact hcase.imp_right (D.binary_placed_locals_reduction h hd F hF hmodel A hAC (hcard.symm ▸ hpo))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
