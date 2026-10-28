module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLinearFour
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLinearGeometry

/-!
# Complete source prime-pair selection in the chosen-module argument

The original non-PSL₃(4) assumption rules out diagram movement by the
overlap two-core in the remaining scalar-cover row. Both linear factors
therefore supply every local clause, and all original source alternatives
now construct the literal pair (DS,R). The result retains its genuine
F.1.1 zero-core branch and its index-two moving-factor branch.

The model exclusions, field reduction and changed-Sylow argument remain
with qt-d-1222-rankone-cartan-local-to-global. Source: Aschbacher–Smith
5.1.11, 5.2.1–2 and 12.2.2, printed pp.635,646–649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- Both original linear factors supply the literal prime pair at every source
field, retaining the scalar cover and the genuine core alternatives. -/
theorem rankOne_cartan_linear_prime_pair_of_nonprojective_four
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e
      (pointParabolic F) (lineParabolic F)) :
    ∃ R : Bool → Subgroup G, ∀ i,
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) ∧
      LocalData T L H B D (R i) ∧
      (((generated L H D (R i)).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R i] (Global.sourceS L H)) ∨
       ((generated L H D (R i)).pCoreIn 2 ≠ ⊥ ∧ ¬ D ≤ normalizer (R i : Set G) ∧
        (normalizingSylow T (R i)).relIndex (T : Subgroup G) = 2)) :=
  linear_source_prime_pair_of_nonprojective_four (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hpar hthree c hd hC hqs hc hf hF e he hmove

/-- Every original chosen-module source row now supplies a genuine local pair,
with its exact zero-core or moving-factor alternative. -/
theorem rankOne_cartan_source_prime_pair
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧ ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2)) :=
  source_prime_pair_core_alternatives (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hpar hthree c hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
