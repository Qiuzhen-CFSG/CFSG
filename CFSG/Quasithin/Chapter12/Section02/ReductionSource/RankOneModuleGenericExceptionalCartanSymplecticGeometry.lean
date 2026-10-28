module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSymplecticGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanSymplecticSelection

/-!
# The complete symplectic prime pair in the chosen-module argument

Both canonical symplectic parabolic factors now satisfy every clause of
LocalData, including the literal Borel product and the relative normalizer
index. Their generated two-core gives either genuine F.1.1 or the moving
factor at index two. The original E.2.2 dispatcher now leaves only the
linear diagram row for factor selection, retaining both central covers.

The zero-core exclusions, remaining field and changed-Sylow branches, and
the conditional normalization theorem remain with the Cartan local-to-global
owner. Source: Aschbacher--Smith5.2.1--2 and12.2.2, pp.646--649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- Both original symplectic factors supply the literal prime pair with
its genuine zero-core and changed-Sylow alternatives. -/
theorem rankOne_cartan_symplectic_prime_pair
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e
      ((pointParabolic (F := F)).subgroupOf (Sp4Derived F))
      ((planeParabolic (F := F)).subgroupOf (Sp4Derived F))) :
    ∃ R : Bool → Subgroup G, ∀ i,
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) ∧
      LocalData T L H B D (R i) ∧
      (((generated L H D (R i)).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R i] (Global.sourceS L H)) ∨
       ((generated L H D (R i)).pCoreIn 2 ≠ ⊥ ∧ ¬ D ≤ normalizer (R i : Set G) ∧
        (normalizingSylow T (R i)).relIndex (T : Subgroup G) = 2)) :=
  symplectic_source_prime_pair (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hpar c hd hC hqs hc hf hF e he hmove

/-- The actual chosen-module input leaves only the marked linear diagram
row for prime-pair selection, preserving its projective and special-linear covers. -/
theorem rankOne_cartan_prime_pair_or_linear_diagram
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    (∃ R : Subgroup G, LocalData T L H B D R) ∨ Global.RightLinearDiagramSource T L H :=
  source_prime_pair_or_linear_diagram (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hpar c hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
