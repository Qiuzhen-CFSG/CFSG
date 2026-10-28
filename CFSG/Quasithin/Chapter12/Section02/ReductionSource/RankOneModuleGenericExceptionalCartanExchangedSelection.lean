module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeExchangedSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanUnitarySelection

/-!
# The exchanged prime pair in the original chosen-module argument

The source E.2.2 exchanged component now constructs the literal (DS,R)
pair without a right-factor geometry callback. The original quotient,
Sylow intersection and Hall subgroup are retained. Its two-core separates
the genuine F.1.1 branch from the moving-component branch. The complete
rank-one source dispatcher leaves only the diagram row for pair selection.

The zero-core model exclusions, remaining field and changed-Sylow branches,
and final conditional normalization remain with the Cartan local-to-global
owner. Source: Aschbacher–Smith 5.2.2 and 12.2.2,
printed pp.646–649,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- The original exchanged component supplies the local pair and its two exact core branches. -/
theorem rankOne_cartan_exchanged_prime_pair
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf H = ⊤)
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f) :
    let R := C.map H.subtype
    LocalData T L H B D R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧ ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2)) :=
  exchanged_source_prime_pair (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hpar c hd hC hgen hc hm

/-- All original rank-one source rows now construct the pair; only diagram selection remains. -/
theorem rankOne_cartan_prime_pair_or_diagram
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    (∃ R : Subgroup G, LocalData T L H B D R) ∨ Global.RightDiagramSource T L H :=
  source_prime_pair_or_diagram (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hpar c hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
