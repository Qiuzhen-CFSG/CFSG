module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.TrialityNativeApplication
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalTrialityExtension

/-!
# Reduced triality restoration for the Chapter 12 chosen module

The literal chosen-module hypotheses supply the normalized-Borel input to
native restoration. Its constructed original marking replaces the original
marking premise of the existing Chapter 12 consumer. The same preparation,
perfect selected R and original S are retained, together with both
orientations and every nonbinary field degree. Exhaustive reduced recognition
is still an independent source obligation.

Source: DGS, *Groups and Graphs* (1985), (15.2), printed pp.226–228;
Aschbacher–Smith F.1.12, pp.263–264, and its Chapter 12 application, p.795.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.DGS85.OriginalExtension
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Apply the existing original triality consumer to a genuine reduced
marking, discharging its original-marking premise by native restoration. -/
theorem rankOne_global_comparison_of_reduced_triality
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 0 < m) (hm2 : 1 < m) (i : Bool)
    (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H))
      (TrialityNative.amalgam m hm i)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  obtain ⟨f⟩ := exists_original_triality_marking_of_reduced_iso d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 m hm hm2 i e hp
  exact D.rankOne_global_comparison_of_original_triality h hmany hn hpsl hH
    d hp m hm (TrialityNative.side i) f

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
