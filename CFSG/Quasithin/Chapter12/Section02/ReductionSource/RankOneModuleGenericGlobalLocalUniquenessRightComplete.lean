module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalUniquenessComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalRightComplete

/-!
# Original nonblock exclusion and the constructed right factor

The completed source selection and ordinary/block exclusions give uniqueness
over the original L from the genuine nonblock exclusion. Combining this with
the constructed right factor supplies a perfect local preparation and the
literal F.1.1 pair, including both parabolic residual identities. No right-factor
callback remains in these applications.

The original generation parameter, intrinsic PSL3(4) exclusion, normalizer
containment and multiplicity hypotheses are retained. The nonblock argument,
including its nonbinary C.1.34 input, remains with its existing producers.
The final application also retains genuine ambient completion recognition;
neither this conditional application nor a faithful local pair proves it.

Source: Aschbacher–Smith 4.3.2–16, printed pp.613–618; 5.2.4–6,
printed pp.649–651; the Chapter 12 application, printed p.795.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Construct the same normalized pair with a perfect right factor once the
original nonblock exclusion is supplied. Its factor is proved, not an input. -/
theorem rankOne_global_preparation_perfect_of_nonblock_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R ∧ Group.IsPerfect R :=
  rankOne_global_preparation_perfect_of_uniqueness D h.toHypothesis1221 hmany hn hpsl
    hH hpar hthree hN (uniqueness_of_nonblock_exclusion D h hmany hn hpsl hnonblock)

/-- The actual pair meets F.1.1 and both literal parabolics have exactly the
original factors as their solvable residuals. Only the nonblock exclusion
remains from the independent local-selection arguments. -/
theorem rankOne_global_local_source_of_nonblock_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R ∧
      ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H) ∧
      ChapterF.Source.borel R (Global.sourceS L H) ≤ normalizer (Global.sourceS L H : Set G) ∧
      (∀ i : Fin 2, (solvableResidual (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i)).map
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i).subtype = ![L,R] i) ∧
      (∀ i : Fin 2, ¬ Group.IsSolvable (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i)) := by
  obtain ⟨A,B,R,d,hR⟩ := rankOne_global_preparation_perfect_of_nonblock_exclusion D
    h hmany hn hpsl hH hpar hthree hN hnonblock
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact ⟨A,B,R,d,d.hypothesisF11 hi hH.1.1.2,d.right_borel_normalizes_sourceS,
    d.parabolic_residuals hi hH.1.1.2 hR,d.parabolics_not_solvable hi hR⟩

/-- Apply original nonblock exclusion and the proved right factor to the
global endpoint. The full source recognition implication remains explicit. -/
theorem rankOne_globalExit_of_nonblock_exclusion_and_recognition
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hrecognize : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      localBorel T L ≤ normalizer (residual H : Set G) →
      ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H) →
      RankOneModule.GlobalExit G) : RankOneModule.GlobalExit G :=
  rankOne_globalExit_of_uniqueness_and_recognition D h hmany hn hpsl hH hpar hthree hN
    (uniqueness_of_nonblock_exclusion D h hmany hn hpsl hnonblock) hrecognize

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
