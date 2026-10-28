module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionExceptional
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalRightComplete

/-!
# Exceptional-model exclusions for the actual Chapter12 pair

The source-selected perfect factors make both full parabolics nonsolvable,
excluding every fixed exceptional Green Book row in either orientation.
This applies to parabolic equivalence, hence respects the weaker J₂ and
Aut(J₂) conclusions. The overlap retains both original odd Cartans.

The construction uses the original uniqueness-over-L implication but no
F.1.12 core bound or amalgam classification premise. Exhaustive classification
and ambient completion recognition remain with qt-d-1222-rankone-generic-global;
uniqueness has its independent producer, with final discharge retained by
qt-d-1222-rankone-generic and qt-d-1361-source.

Source: Aschbacher–Smith 5.2.6, pp.650–651, F.1.12(I)(8–13), pp.262–264,
and the Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- All eight concrete exceptional rows are excluded for the same source
pair, at the parabolic equivalence required by the Hall–Janko alternatives. -/
theorem rankOne_global_preparation_exceptional_exclusions_of_uniqueness
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G)) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R ∧ Group.IsPerfect R ∧
      ∀ c : ExceptionalModels.Case,
        let α := Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)
        ¬ ExceptionalModels.ParabolicModel c α ∧
          ¬ ExceptionalModels.ParabolicModel c α.reverse := by
  obtain ⟨A,B,R,d,hp⟩ := D.rankOne_global_preparation_perfect_of_uniqueness
    h hmany hn hpsl hH hpar hthree hN hunique
  exact ⟨A,B,R,d,hp,fun c => d.not_exceptional_parabolic_models
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hp c⟩

/-- On any actual prepared pair, this excludes the source's exact model
predicates, with compatible isomorphisms except for the Hall–Janko rows. -/
theorem rankOne_global_not_exceptional_models
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (c : ExceptionalModels.Case) :
    let α := Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)
    ¬ ExceptionalModels.IsModel c α ∧ ¬ ExceptionalModels.IsModel c α.reverse :=
  d.not_exceptional_models (D.rankOne_generic_input_of_many h hmany hn hpsl) hp c

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
