module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSymplecticSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Canonical symplectic right factors for the chosen Cartan pair

The actual symplectic diagram marking constructs both perfect parabolic
factors inside O²(H). They generate H with the original Sylow, have the
literal PSL₂(2ᶠ) two-core quotient, and are relative C-components at their
Sylow normalizers. Both the source S and the original Hall subgroup B
normalize them, and S meets each in a full Sylow two-subgroup.

The source field f is kept distinct from the original degree n. The
remaining normalizer-index and Borel clauses of LocalData, the linear
covering diagram rows, and the zero-core and changed-Sylow exclusions
remain with qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith 5.1.11(3),5.2.1–2 and12.2.2, pp.635,646–649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (M : ChosenModule T L V)
include M

/-- The original chosen-module input supplies the actual source factor selection
without identifying a parabolic factor with an H-component. -/
theorem rankOne_cartan_symplectic_source_factors
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
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
      R i ≤ residual H ∧ ¬ R i ≤ normalizer (L : Set G) ∧
      R i ⊔ (T : Subgroup G) = H ∧
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) ∧
      ((R i).subgroupOf (R i ⊔ normalizingSylow T (R i))).IsCComponent ∧
      Global.sourceS L H ≤ normalizer (R i : Set G) ∧
      B ≤ normalizer (R i : Set G) ∧
      ∃ P : Sylow 2 (R i), (P : Subgroup (R i)).map (R i).subtype =
        Global.sourceS L H ⊓ R i :=
  symplectic_source_original_factors
    (M.rankOne_generic_input_of_many h hmany hn hpsl).sylow_normalizes
    hH hpar c hC hqs hc hf hF e he hmove

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
