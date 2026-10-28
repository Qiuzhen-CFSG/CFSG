module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneTriangular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneQuotientMidpointConsumers

/-!
# The original triangular comparison and the remaining source branches

The constructed r=3 marked split quotient now gives the original selected
pair's PSL₃ amalgam. Native extension restoration preserves the full Borel
and both endpoint maps, and yields both natural blocks, equality of the
right cores and containment of the original S. For the whole residual this
feeds the existing Chapter 12 GlobalExit consumer.

The noncommuting source alternatives retain the distance-two branch and the
entire central four-edge branch, including the actual actor centers, natural
Q/Z actions, universal and quotient midpoint geometry, marked finite
completion, exchange and exact root fusion. No quotient or split hypothesis
is left in the triangular branch. The other source branches and general
Chapter 15 extension restoration remain required for full classification.
Source: DGS, Groups and Graphs (1985), (10.5), pp.156--157, Theorem D and
(15.2), pp.224,226--228; Aschbacher--Smith F.1.12 and 12.2.2, pp.263--264,795.
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
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- Restore the original triangular pair, its full Borel, both blocks and
right core; all geometric quotient and split premises are discharged. -/
theorem comparison_and_core_of_critical_bOne_rThree
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
    (hr : HasSourcePathParameters
      (P := fun i => (P₀ ![L,R] (sourceS L H) i).subgroupOf (G₀ ![L,R] (sourceS L H))) 3 4) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R := by
  obtain ⟨F,_,_,_,m,hm,hF,point,⟨f⟩⟩ := BOneSource.small_linear_comparison_of_critical_bOne_rThree
    (d.hypothesisF11 h hTH) (d.parabolics_not_solvable h hp) hc hne hb hr
  have hm' := d.linear_reduced_parameter h hTH hp F hm hF point f
  have hcomp := d.originalLinearComparisonOfReduced h hTH hp F hm hF point f
  have hiso : Nonempty (Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse) := by
    cases point
    · exact Or.inl ⟨hcomp⟩
    · exact Or.inr ⟨hcomp⟩
  obtain ⟨_,hL,hR⟩ := d.linear_amalgam_blocks h hTH hp F hm hF hiso
  exact ⟨.linear F m hm hF hiso,hL,hR,
    linear_original_core_and_containment_of_reduced_iso d h hTH F hm' hF point f hp⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation


namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.OriginalExtension
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))

include D h hmany hn hpsl hH

/-- The original Chapter 12 triangular branch supplies the full comparison,
both natural blocks, right-core equality and containment of the original S. -/
theorem rankOne_comparison_and_core_of_critical_bOne_rThree
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1)
    (hr : HasSourcePathParameters
      (P := fun i => (P₀ ![L,R] (Global.sourceS L H) i).subgroupOf
        (G₀ ![L,R] (Global.sourceS L H))) 3 4) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R :=
  d.comparison_and_core_of_critical_bOne_rThree
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne hb hr

/-- The same completed triangular branch feeds GlobalExit when the whole
original residual is selected. No quotient or split witness is assumed. -/
theorem rankOne_globalExit_of_critical_bOne_rThree
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) = 1)
    (hr : HasSourcePathParameters
      (P := fun i => (P₀ ![L,residual H] (Global.sourceS L H) i).subgroupOf
        (G₀ ![L,residual H] (Global.sourceS L H))) 3 4) :
    RankOneModule.GlobalExit G :=
  D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp
    (D.rankOne_comparison_and_core_of_critical_bOne_rThree h hmany hn hpsl hH d hp hc hne hb hr).1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule


namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)

/-- The still unrecognized central branch, retaining every constructed
source premise, the full actor centers and all literal geometric quotient maps. -/
def HasCentralSourceBranch : Prop :=
  b (reducedFamily L S)=1 ∧
  HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5 ∧
  HasCentralRootGeometry ds ∧ HasMidpointRootGeometry ds ∧ HasQuotientMidpointGeometry ds ∧
  HasMarkedGeometricQuotient ds ∧
  ChosenApartmentExchange (X := (reducedAmalgam L S).Universal) (sourceGraph (reducedAmalgam L S))
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (fullCartanPathRoots ds)))
    (fullCartanPathLength ds) ∧
  ∀ j, ∃ x∈(fullCartanPathRoots ds j).root, orderOf x=2 ∧
    ∃ g∈universalBOneActor h j (ds j).data, g*x*g⁻¹=fullCartanReflections ds j

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.Assembly
open ChapterF.Source.DGS85.OriginalExtension
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- Recognize the triangular source branch and retain the full central
branch with its original profiles, centers, cover, exchange and finite completion. -/
theorem comparison_or_central_of_critical_bOne
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1) :
    (ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R) ∨
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} (d.hypothesisF11 h hTH)
      (chosenCartans (d.hypothesisF11 h hTH)) j, BOneSource.HasCentralSourceBranch ds := by
  obtain ⟨ds,hparams,hmid,hqmid,hmarked,hexchange,hfusion⟩ :=
    BOneSource.quotient_midpoint_geometry_of_critical_bOne
      (d.hypothesisF11 h hTH) (d.parabolics_not_solvable h hp) hc hne hb
      (chosenCartans (d.hypothesisF11 h hTH))
  rcases hparams with hr | ⟨hr,hcentral⟩
  · exact Or.inl (d.comparison_and_core_of_critical_bOne_rThree h hTH hp hc hne hb hr)
  · exact Or.inr ⟨ds,hb,hr,hcentral,hmid,hqmid,hmarked,hexchange,hfusion⟩

/-- For the original noncommuting pair, only the distance-two source branch
or the fully constructed central four-edge branch remains to be recognized. -/
theorem comparison_or_bTwo_or_central_of_noncommuting
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (sourceS L H)) w⁆ ≠ ⊥) :
    (ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R) ∨
    b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 2 ∨
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} (d.hypothesisF11 h hTH)
      (chosenCartans (d.hypothesisF11 h hTH)) j, BOneSource.HasCentralSourceBranch ds := by
  let hf := d.hypothesisF11 h hTH
  have hsmall := Reduction.no_small_unitary_of_nonsolvable_parabolics hf
    (d.parabolics_not_solvable h hp)
  rcases (Reduction.reduced_noncommuting_distance_bound_without_small_unitary
    hf hsmall hc hne).1 with hb | hb
  · rcases d.comparison_or_central_of_critical_bOne h hTH hp hc hne hb with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inr hh)
  · exact Or.inr (Or.inl hb)

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

/-- The literal original Chapter 12 pair has no outstanding triangular
recognition input. The two other source branches retain their exact hypotheses. -/
theorem rankOne_comparison_or_bTwo_or_central_of_noncommuting
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) w⁆ ≠ ⊥) :
    (Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R) ∨
    b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 2 ∨
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} hf (chosenCartans hf) j,
      BOneSource.HasCentralSourceBranch ds :=
  d.comparison_or_bTwo_or_central_of_noncommuting
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne

/-- With the entire residual selected, triangular recognition reaches the
existing GlobalExit conclusion. All other noncommuting branches stay explicit. -/
theorem rankOne_globalExit_or_bTwo_or_central_of_noncommuting
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    {v w : RankTwo.Vertex (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) w⁆ ≠ ⊥) :
    RankOneModule.GlobalExit G ∨
    b (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) = 2 ∨
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
    ∃ ds : ∀ j : Bool, FullCartanReflectionProfile.{u} hf (chosenCartans hf) j,
      BOneSource.HasCentralSourceBranch ds := by
  rcases D.rankOne_comparison_or_bTwo_or_central_of_noncommuting
    h hmany hn hpsl hH d hp hc hne with hcomp | hrest
  · exact Or.inl (D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp hcomp.1)
  · exact Or.inr hrest

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
