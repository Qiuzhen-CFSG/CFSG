module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The Chapter 12 consumer of the genuine generic local amalgam

The original chosen-module hypotheses supply the earlier rank-one input.
The prepared local pair then supplies all six F.1.1 conditions and the
faithful triple in its literal generated subgroup. No ambient generation
claim or identification with a model is inferred from local faithfulness.

The final assembly remains conditional on two independent source inputs:
construction of the local data (5.1.9--11, 5.2.4--5), and recognition of
that pair (5.2.6--5.3.7, including the M23 branch and q > 2). These belong
to `qt-d-1222-rankone-global-local` and
`qt-d-1222-rankone-global-recognition`, respectively. The parent task
`qt-d-1222-rankone-generic-global` retains their final discharge.

Source: Aschbacher--Smith, printed pp.634--635,649--661,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
include D

/-- The genuine source pair and its faithful inclusion triple, on the same
L, H and S = O₂(N_G(L)∩H) as the original Chapter 12 application. -/
theorem rankOne_global_local_pair_of_preparation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B L₂ : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B L₂) :
    ChapterF.Source.HypothesisF11 ![L, L₂] (Global.sourceS L H) ∧
    ChapterF.Source.LocallyRankOneTriple
      (fun i => (ChapterF.Source.parabolic ![L, L₂] (Global.sourceS L H) i).subgroupOf
        (ChapterF.Source.generated ![L, L₂] (Global.sourceS L H)))
      ((ChapterF.Source.commonBorel ![L, L₂] (Global.sourceS L H)).subgroupOf
        (ChapterF.Source.generated ![L, L₂] (Global.sourceS L H))) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.hypothesisF11 hi hH.1.1.2, d.faithfulTriple hi hH.1.1.2⟩

/-- Conditional assembly for the normalized branch of the original source.
The first implication constructs the local pair; the second must prove the
Green Book alternatives and completion recognition, retaining the strict
rank-two exponent in `GlobalExit`. Neither input is discharged here. -/
theorem rankOne_globalExit_of_local_sources_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G))
    (hprepare : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      localBorel T L ≤ normalizer (residual H : Set G) →
      ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂)
    (hrecognize : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      localBorel T L ≤ normalizer (residual H : Set G) →
      ∀ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ →
      ChapterF.Source.HypothesisF11 ![L, L₂] (Global.sourceS L H) →
      RankOneModule.GlobalExit G) : RankOneModule.GlobalExit G := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  have hBorel : localBorel T L ≤ normalizer (residual H : Set G) := by
    simpa only [localBorel_eq_map] using hN
  obtain ⟨A, B, L₂, d⟩ := hprepare hi hH hgen hthree hBorel
  have hpair := D.rankOne_global_local_pair_of_preparation
    h.toHypothesis1221 hmany hn hpsl hH d
  exact hrecognize hi hH hgen hthree hBorel A B L₂ d hpair.1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
