module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneConsumers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.MixedGraphApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.LinearFlagTransport
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Data.Fintype.Shrink

/-!
# Original regular comparisons from the noncommuting critical source branch

The source critical-pair construction supplies both natural actions, their
literal actors and both natural-module equivalences. Transport the resulting
A₂ or C₂ flag comparison along a field equivalence to a small carrier, keeping
the whole Borel and both inclusion squares. The original Chapter 15 restoration
then gives the prepared pair's full comparison, both natural blocks, right-core
equality and containment of its original S.

The prepared nonsolvable endpoints supply all enlarged actor models and both
adjacent-core obstructions. Chapter 7 therefore selects b=1 or b=2 internally;
the first branch is recognized here and the second remains explicit. The
chosen-module application retains the original KnownSimple/proper-K scope and
has no natural-action, actor-identity, module-equivalence, row-order or
centerfreeness premise. The same result feeds GlobalExit when R is the whole
residual. The actual marked split quotient, commuting branches and recognition
of the remaining b=2 branch still require source assembly.

Source: DGS, Groups and Graphs (1985), (7.1)--(7.5), pp.126--131,
(10.5), pp.156--157, Theorem D and (15.2), pp.224,226--228;
Aschbacher--Smith F.1.12, 5.2.6 and 12.2.2, pp.263--264,650--651,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
open Reduction OriginalExtension FongSeitzBinary Subgroup.CosetGeometry.RankTwo

private def linearFieldIso {F K : Type*} [Field F] [Finite F] [Field K] [Finite K]
    (e : F ≃+* K) (point : Bool) :
    Iso (LinearNative.amalgam F point) (LinearNative.amalgam K point) := by
  cases point
  · exact Matrix.PSL3.RootPresentationRecognition.flagFieldIso e 0
  · exact Matrix.PSL3.RootPresentationRecognition.flagFieldIso e 1

private def symplecticFieldIso {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) (point : Bool) :
    Iso (SymplecticNative.amalgam F point) (SymplecticNative.amalgam K point) := by
  cases point
  · exact {
      left := Theory.SpecificGroups.SymplecticFour.Binary.planeParabolicFieldEquiv e
      middle := Theory.SpecificGroups.SymplecticFour.Binary.borelFieldEquiv e
      right := Theory.SpecificGroups.SymplecticFour.Binary.pointParabolicFieldEquiv e
      left_commutes _ := Subtype.ext rfl
      right_commutes _ := Subtype.ext rfl }
  · exact {
      left := Theory.SpecificGroups.SymplecticFour.Binary.pointParabolicFieldEquiv e
      middle := Theory.SpecificGroups.SymplecticFour.Binary.borelFieldEquiv e
      right := Theory.SpecificGroups.SymplecticFour.Binary.planeParabolicFieldEquiv e
      left_commutes _ := Subtype.ext rfl
      right_commutes _ := Subtype.ext rfl }

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The constructed natural fields give actual small-carrier model comparisons,
with the full Borel and both inclusions transported by the same field map. -/
theorem small_comparison_of_critical_bOne
    (h : HypothesisF11 L S)
    (hm : ∀ x : Vertex (reducedFamily L S), IsRankOneModel
      (graphLocalGroup (reducedFamily L S) x ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) x)))
    {v w : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1)
    (Q : MarkedQuotient P) (e : Iso (reducedAmalgam L S) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (m : ℕ), 0 < m ∧ Nat.card F = 2^m ∧
      ((rotationOrder Q = 3 ∧ ∃ point : Bool,
        Nonempty (Iso (reducedAmalgam L S) (LinearNative.amalgam F point))) ∨
      (rotationOrder Q = 4 ∧ ∃ point : Bool,
        Nonempty (Iso (reducedAmalgam L S) (SymplecticNative.amalgam F point)))) := by
  obtain ⟨k₀,f₀,n₀,ch₀,k₁,f₁,n₁,ch₁,he⟩ :=
    comparison_of_critical_bOne h hm hc hne hb Q e split
  rcases he with ⟨hrot,point,⟨f⟩⟩ | ⟨hrot,point,⟨f⟩⟩
  · let a : k₁ ≃+* Shrink.{0} k₁ := (Shrink.ringEquiv.{0,_} k₁).symm
    let F := Shrink.{0} k₁
    let : CharP F 2 := (a.toRingHom.charP_iff_charP 2).mp inferInstance
    let := Fintype.ofFinite F
    obtain ⟨m,_,hF⟩ := FiniteField.card F 2
    exact ⟨F,inferInstance,inferInstance,inferInstance,m,m.property,
      by simpa only [Nat.card_eq_fintype_card] using hF,
      Or.inl ⟨hrot,point,⟨f.trans (linearFieldIso a point)⟩⟩⟩
  · let a : k₀ ≃+* Shrink.{0} k₀ := (Shrink.ringEquiv.{0,_} k₀).symm
    let F := Shrink.{0} k₀
    let : CharP F 2 := (a.toRingHom.charP_iff_charP 2).mp inferInstance
    let := Fintype.ofFinite F
    obtain ⟨m,_,hF⟩ := FiniteField.card F 2
    exact ⟨F,inferInstance,inferInstance,inferInstance,m,m.property,
      by simpa only [Nat.card_eq_fintype_card] using hF,
      Or.inr ⟨hrot,point,⟨f.trans (symplecticFieldIso a point)⟩⟩⟩

/-- Discharge the natural-profile, actor-identity and module-equivalence
premises of the b=1 reduced catalogue application. -/
theorem reduced_alternatives_of_critical_bOne {L R : Subgroup G}
    (h : HypothesisF11 ![L,R] S)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic ![L,R] S i))
    {v w : Vertex (reducedFamily ![L,R] S)}
    (hc : IsCriticalPair (reducedFamily ![L,R] S) v w)
    (hne : ⁅Z (reducedFamily ![L,R] S) v, Z (reducedFamily ![L,R] S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily ![L,R] S) = 1)
    (Q : MarkedQuotient P) (e : Iso (reducedAmalgam ![L,R] S) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives L R S := by
  obtain ⟨F,_,_,_,m,hm,hF,he⟩ := small_comparison_of_critical_bOne h
    (reduced_actor_models_of_nonsolvable_parabolics h hns) hc hne hb Q e split
  rcases he with ⟨_,point,hf⟩ | ⟨_,point,hf⟩
  · exact .linear F m hm hF point hf
  · exact .symplectic F m hm hF point hf

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.Assembly
open ChapterF.Source.DGS85.OriginalExtension
open Subgroup.CosetGeometry.RankTwo
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- The original prepared pair supplies its own rank-one actor models and
natural actions. Only the selected critical branch and marked split quotient remain. -/
theorem comparison_and_core_of_critical_bOne
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {v w : Vertex (Reduction.reducedFamily ![L,R] (sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
    (Q : MarkedQuotient P)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R := by
  let hf := d.hypothesisF11 h hTH
  obtain ⟨F,_,_,_,m,hm,hF,he⟩ := BOneSource.small_comparison_of_critical_bOne hf
    (Reduction.reduced_actor_models_of_nonsolvable_parabolics hf
      (d.parabolics_not_solvable h hp)) hc hne hb Q e split
  rcases he with ⟨_,point,⟨f⟩⟩ | ⟨_,point,⟨f⟩⟩
  · have hm' := d.linear_reduced_parameter h hTH hp F hm hF point f
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
  · obtain ⟨hcomp,_,_,hL,hR⟩ := symplectic_original_comparison_of_reduced_iso
      d h hTH hp F hm hF point f
    refine ⟨?_,hL,hR,
      symplectic_original_core_and_containment_of_reduced_iso d h hTH hp F hm hF point f⟩
    apply ConcreteAmalgamComparison.symplectic F m hm hF
    cases point
    · exact Or.inr hcomp
    · exact Or.inl hcomp

/-- The actual nonsolvable prepared endpoints discharge all Chapter 6
model and obstruction premises. The noncommuting branch therefore gives the
original comparison or the precise remaining distance-two source branch. -/
theorem comparison_or_bTwo_of_noncommuting
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {v w : Vertex (Reduction.reducedFamily ![L,R] (sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (sourceS L H)) w⁆ ≠ ⊥)
    (Q : MarkedQuotient P)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    (ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R) ∨
      b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 2 := by
  let hf := d.hypothesisF11 h hTH
  have hsmall := Reduction.no_small_unitary_of_nonsolvable_parabolics hf
    (d.parabolics_not_solvable h hp)
  rcases (Reduction.reduced_noncommuting_distance_bound_without_small_unitary
    hf hsmall hc hne).1 with hb | hb
  · exact Or.inl (d.comparison_and_core_of_critical_bOne h hTH hp hc hne hb Q e split)
  · exact Or.inr hb

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.OriginalExtension
open Subgroup.CosetGeometry.RankTwo
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
  {v w : Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
  (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v w)
  (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v,
    Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) w⁆ ≠ ⊥)
  (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1)
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits)

include D h hmany hn hpsl hH d hp hc hne hb e split in
/-- The actual Chapter 12 hypotheses construct the actor models, both natural
actions and the original A₂/C₂ comparison on the same selected perfect R. -/
theorem rankOne_comparison_and_core_of_critical_bOne :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R :=
  d.comparison_and_core_of_critical_bOne
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne hb Q e split

omit hb in
include D h hmany hn hpsl hH d hp hc hne e split in
/-- On the literal chosen-module pair, all noncommuting distances other than
two now give the original regular comparison and its core consequences. -/
theorem rankOne_comparison_or_bTwo_of_noncommuting :
    (Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R) ∨
      b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 2 :=
  d.comparison_or_bTwo_of_noncommuting
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne Q e split

omit d hp hc hne hb e in
include D h hmany hn hpsl hH split in
/-- With the whole residual selected, the constructed original comparison
feeds the existing strict GlobalExit consumer. -/
theorem rankOne_globalExit_of_critical_bOne
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    {v w : Vertex (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) w⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) = 1)
    (e : Iso (reducedAmalgam ![L,residual H] (Global.sourceS L H)) Q.standardAmalgam) :
    RankOneModule.GlobalExit G :=
  D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp
    (D.rankOne_comparison_and_core_of_critical_bOne
      h hmany hn hpsl hH d hp hc hne hb Q e split).1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
