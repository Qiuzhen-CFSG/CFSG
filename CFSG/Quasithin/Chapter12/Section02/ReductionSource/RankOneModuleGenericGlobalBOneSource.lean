module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.BOneSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalCatalogue

/-!
# The noncommuting critical-distance-one branch of the original generic exit

The actual prepared pair supplies F.1.1 to intrinsic DGS recognition. Its
linear or symplectic reduced comparison is restored through the original
normalized Borel, for every selected perfect R. The full original comparison
then feeds the existing strict ambient recognizers at the whole residual.

No field coordinates, split quotient, model comparison or extension marking
are assumed. The critical pair, its noncommuting centers and b=1 are the
remaining branch hypotheses. Exhaustive critical-branch selection and
original uniqueness retain their separate producers and final discharge.

Source: DGS, *Groups and Graphs* (1985), (7.1), (10.5), and Theorem D;
Aschbacher--Smith 5.2.6, pp.650--651, and Chapter 12, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source.DGS85
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
include D h hmany hn hpsl hH

/-- The original selected-R comparison follows from the literal DGS branch,
including both endpoint squares and the full odd Borel. -/
theorem rankOne_global_comparison_of_critical_bOne
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R)
    {v w : Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.concreteComparison_of_critical_bOne
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne hb

/-- Once the original whole-residual pair is prepared, the noncommuting b=1
source branch gives the strict global model exit without a recognition premise. -/
theorem rankOne_globalExit_of_prepared_critical_bOne
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    {v w : Vertex (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H))}
    (hc : IsCriticalPair
      (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) = 1) :
    RankOneModule.GlobalExit G :=
  D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp
    (D.rankOne_global_comparison_of_critical_bOne h hmany hn hpsl hH d hp hc hne hb)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
