module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneQuadrangular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneTriangularConsumers

/-!
# Both original natural b=1 branches in the Chapter 12 consumer

The four-edge midpoint descent and Borel-sign proof construct the marked
split quotient internally. Existing native restoration gives the original
symplectic comparison, both natural blocks, the full right-core equality
and containment of the original S. The whole Borel and both endpoint
inclusion squares are retained by the marked comparison.

Together with the triangular branch, this discharges every recognition
premise in the original nonsolvable b=1 noncommuting case. The literal
Chapter 12 application retains b=2; its whole-residual specialization feeds
GlobalExit in both recognized rows. The commuting branches, remaining
noncommuting source cases and general Chapter 15 restoration stay open.

Source: DGS (1985), (10.5), Theorem D and (15.2), pp.156--157,224,226--228;
Aschbacher--Smith F.1.12 and 12.2.2, pp.263--264,795--796.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.Assembly
open ChapterF.Source.DGS85.OriginalExtension
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- Restore the original r=4 pair with full Borel, both endpoint squares,
both natural blocks, original right-core equality and original S containment. -/
theorem comparison_and_core_of_critical_bOne_rFour
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
    (hr : HasSourcePathParameters
      (P := fun i => (P₀ ![L,R] (sourceS L H) i).subgroupOf (G₀ ![L,R] (sourceS L H))) 4 5) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R := by
  let hf := d.hypothesisF11 h hTH
  obtain ⟨ds⟩ := BOneSource.full_cartan_profiles_of_critical_bOne hf
    (d.parabolics_not_solvable h hp) hc hne hb (chosenCartans hf)
  exact d.comparison_and_core_of_critical_bOne h hTH hp hc hne hb
    (BOneSource.fullCartanRFourFiniteQuotient ds hr)
    (BOneSource.fullCartanRFourFiniteMarkedIso ds hr)
    (BOneSource.fullCartanRFourFiniteSplitData ds hr)

/-- Both original b=1 branches are recognized without geometric or split inputs. -/
theorem comparison_and_core_of_critical_bOne_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R := by
  rcases d.comparison_or_central_of_critical_bOne h hTH hp hc hne hb with hh | ⟨ds,hh⟩
  · exact hh
  · exact d.comparison_and_core_of_critical_bOne_rFour h hTH hp hc hne hb hh.2.1

/-- Only b=2 remains in the original nonsolvable noncommuting source branch. -/
theorem comparison_or_bTwo_of_noncommuting_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (sourceS L H)) w⁆ ≠ ⊥) :
    (ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R) ∨
    b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 2 := by
  rcases d.comparison_or_bTwo_or_central_of_noncommuting h hTH hp hc hne with hh | hb | ⟨ds,hh⟩
  · exact Or.inl hh
  · exact Or.inr hb
  · exact Or.inl (d.comparison_and_core_of_critical_bOne_rFour h hTH hp hc hne hh.1 hh.2.1)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.DGS85.Assembly
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))

include D h hmany hn hpsl hH

/-- Literal Chapter 12 application with all b=1 recognition premises discharged. -/
theorem rankOne_comparison_and_core_of_critical_bOne_source
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R :=
  d.comparison_and_core_of_critical_bOne_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne hb

/-- The actual original noncommuting pair now retains only its b=2 alternative. -/
theorem rankOne_comparison_or_bTwo_of_noncommuting_source
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) w⁆ ≠ ⊥) :
    (Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R) ∨
    b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 2 :=
  d.comparison_or_bTwo_of_noncommuting_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne

/-- The full residual specialization consumes both recognized b=1 rows. -/
theorem rankOne_globalExit_or_bTwo_of_noncommuting_source
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) w⁆ ≠ ⊥) :
    RankOneModule.GlobalExit G ∨
    b (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) = 2 := by
  rcases D.rankOne_comparison_or_bTwo_of_noncommuting_source
    h hmany hn hpsl hH d hp hc hne with hh | hb
  · exact Or.inl (D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp hh.1)
  · exact Or.inr hb

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
