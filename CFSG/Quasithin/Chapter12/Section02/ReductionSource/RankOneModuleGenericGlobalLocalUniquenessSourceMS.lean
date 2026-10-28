module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSourceMSAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalUniquenessRightComplete

/-!
# Original MS inputs for the Chapter 12 normalized source consumer

The action-only nonblock contradiction now discharges the nonblock callback in
the actual Chapter 12 uniqueness and preparation argument. The constructed
right factor yields the literal F.1.1 pair and both parabolic residual identities.
No SecondarySourceData or strict secondary-core enlargement is required.

Only the original full-quotient/MS selection remains from the nonblock branch:
its quotient selection stays with qt-d-1222-rankone-uniqueness-nonblock, and its
genuine C.1.34 alternatives with qt-c134-nonbinary-linear-three-source. The
ambient completion-recognition premise in the final application remains with
its independent producer. All original generation, normalization, multiplicity
and intrinsic PSL₃(4)-exclusion hypotheses are retained. These specialized
applications preserve the older nonblock-callback APIs.

Source: Aschbacher–Smith 4.3.2–16, pp.613–619; 5.2.4–6, pp.649–651;
the Chapter 12 application, p.795.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual normalized preparation, with the nonblock contradiction and
right factor constructed from the original MS selection. -/
theorem rankOne_global_preparation_perfect_of_originalMSAlternatives
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hms : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K →
        Nonblock.OriginalMSAlternatives c) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R ∧ Group.IsPerfect R :=
  rankOne_global_preparation_perfect_of_uniqueness D h.toHypothesis1221 hmany hn hpsl
    hH hpar hthree hN (uniqueness_of_originalMSAlternatives D h hmany hn hpsl hms)

/-- The literal source pair, retaining both original parabolic residuals.
The only nonblock premise is the original marked whole-core MS selection. -/
theorem rankOne_global_local_source_of_originalMSAlternatives
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hms : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K →
        Nonblock.OriginalMSAlternatives c) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R ∧
      ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H) ∧
      ChapterF.Source.borel R (Global.sourceS L H) ≤ normalizer (Global.sourceS L H : Set G) ∧
      (∀ i : Fin 2, (solvableResidual (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i)).map
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i).subtype = ![L,R] i) ∧
      (∀ i : Fin 2, ¬ Group.IsSolvable (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i)) :=
  rankOne_global_local_source_of_nonblock_exclusion D h hmany hn hpsl hH hpar hthree hN
    (fun c hf hb => Nonblock.false_of_originalMSAlternatives D h hf hb (hms c hf hb))

/-- The genuine Chapter 12 global exit from original MS alternatives and
the independent ambient recognition implication. -/
theorem rankOne_globalExit_of_originalMSAlternatives_and_recognition
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G))
    (hms : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K →
        Nonblock.OriginalMSAlternatives c)
    (hrecognize : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      localBorel T L ≤ normalizer (residual H : Set G) →
      ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H) →
      RankOneModule.GlobalExit G) : RankOneModule.GlobalExit G :=
  rankOne_globalExit_of_uniqueness_and_recognition D h hmany hn hpsl hH hpar hthree hN
    (uniqueness_of_originalMSAlternatives D h hmany hn hpsl hms) hrecognize

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
