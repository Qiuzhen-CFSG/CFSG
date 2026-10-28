module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.G2NativeApplication
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalG2Extension

/-!
# Original G₂ restoration in the Chapter 12 chosen-module argument

The literal reduced comparison constructs both original endpoint maps and the
full Borel marking. The existing original extension theorem then gives the
concrete comparison, right-core equality, and containment of the same S in the
arbitrary perfect selected R. No separate original marking or lifting premise
remains. Reduced recognition and its exhaustive source assembly remain inputs.

Source: DGS (1985), (15.2), pp.226–228; Aschbacher–Smith F.1.12,
pp.263–264, and the chosen-module application, p.795.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.DGS85.OriginalExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
include D h hmany hn hpsl hH

/-- The actual Chapter 12 selected-factor comparison, from a reduced marking
in either orientation over every finite field of characteristic two. -/
theorem rankOne_global_comparison_of_reduced_g2
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) (F : Type) [Field F] [Finite F] [CharP F 2]
    (short : Bool)
    (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H))
      (G2Native.amalgam F short)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  concreteComparison_of_reduced_g2 d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp F short e

/-- The reduced source row discharges the original-core and containment
premises on the same arbitrary perfect selected R. -/
theorem rankOne_global_core_and_containment_of_reduced_g2
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) (F : Type) [Field F] [Finite F] [CharP F 2]
    (short : Bool)
    (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H))
      (G2Native.amalgam F short)) :
    (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R :=
  g2_original_core_and_containment_of_reduced_iso d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp F short e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
