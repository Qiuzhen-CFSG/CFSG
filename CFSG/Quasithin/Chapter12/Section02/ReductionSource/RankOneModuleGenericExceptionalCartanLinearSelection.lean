module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLinearSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Linear parabolic factors for the original chosen Cartan pair

The original marked linear diagram row constructs both rank-one factors
inside O²(H), including the special-linear scalar cover. Each escapes
N_G(L), generates H with T, has the literal PSL₂ quotient over the source
field, and is a relative C-component at its Sylow normalizer. The original
Hall subgroup B normalizes both, and S meets each in a full Sylow subgroup.

The action of S on the whole factors, the remaining RightData clauses,
and the zero-core and changed-Sylow normalization branches remain with
qt-d-1222-rankone-cartan-local-to-global. No identification of the original
rank-one degree with the source residual degree is assumed here.
Source: Aschbacher–Smith5.1.10–11,5.2.1–2,12.2.2, pp.634–635,646–649,795.
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
  {T : Sylow 2 G} {L V H A B : Subgroup G} (M : ChosenModule T L V)
include M

/-- Both factors are constructed from the actual chosen-module source marking,
with the scalar cover and the original Hall and Sylow subgroups retained. -/
theorem rankOne_cartan_linear_source_factors
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
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e (pointParabolic F) (lineParabolic F)) :
    ∃ R : Bool → Subgroup G, ∀ i,
      R i ≤ residual H ∧ ¬ R i ≤ normalizer (L : Set G) ∧
      R i ⊔ (T : Subgroup G) = H ∧
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) ∧
      ((R i).subgroupOf (R i ⊔ normalizingSylow T (R i))).IsCComponent ∧
      B ≤ normalizer (R i : Set G) ∧
      ∃ P : Sylow 2 (R i), (P : Subgroup (R i)).map (R i).subtype =
        Global.sourceS L H ⊓ R i :=
  linear_source_original_factors
    (M.rankOne_generic_input_of_many h hmany hn hpsl).sylow_normalizes
    hH hpar c hC hqs hc hf hF e he hmove

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
