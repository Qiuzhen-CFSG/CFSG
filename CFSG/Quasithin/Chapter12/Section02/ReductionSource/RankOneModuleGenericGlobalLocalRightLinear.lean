module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightLinear
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalRight

/-!
# The marked linear diagram row in the original Chapter 12 setup

The canonical point and line parabolic residuals have the literal rank-one
quotients and full S-intersections. The odd left Cartan fixes both factors;
their Borels are the full overlaps with N_G(L), with the exact Hall product.
Thus source 5.2.1's S-action is the only remaining right-factor premise in
this marked linear row. The last theorem applies the construction to the
original local preparation, retaining the independent uniqueness-over-L
implication. No completion or global model is inferred from preparation.

The generic/global owner retains the remaining diagram rows and completion
recognition; qt-d-1222-rankone-global-uniqueness produces uniqueness. The
Cartan local-to-global owner is also constructing the linear S-action.
Source: Aschbacher--Smith 5.1.10--11 and 5.2.1,4--5, pp.634--635,646,649--650;
the Chapter 12 application is on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The marked linear row supplies all right-factor clauses once its source
S-action is known. The original scalar covering center is retained. -/
theorem rankOne_rightFactor_of_linear_source
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    {A B : Subgroup G} (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    {C : Subgroup H} {f : ℕ} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e (pointParabolic F) (lineParabolic F)) (i : Bool)
    (hS : Global.sourceS L H ≤ normalizer (((Prime.linearSourceFactor
      ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype) : Set G)) :
    Global.RightFactor T L H A B ((Prime.linearSourceFactor
      ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype) :=
  Global.linear_source_rightFactor_of_sourceS D.sylow_normalizes_component hH hpar c hN
    hC hqs hc hf hF e he hmove i hS

/-- Apply the exact linear factor and Borel product to local preparation.
Only the original uniqueness implication and the source S-action remain. -/
theorem rankOne_global_preparation_of_linear_source
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    {C : Subgroup H} {f : ℕ} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e (pointParabolic F) (lineParabolic F)) (i : Bool)
    (hS : Global.sourceS L H ≤ normalizer (((Prime.linearSourceFactor
      ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype) : Set G)) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R :=
  D.rankOne_global_preparation_of_rightFactor h hmany hn hpsl hH hpar hN hunique
    (fun _ _ c => ⟨_,D.rankOne_rightFactor_of_linear_source hH hpar c hN
      hC hqs hc hf hF e he hmove i hS⟩)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
