module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.G2Consumers
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi

/-!+# The linear hexagon consumer with constructed finite root reflections

For every marked split quotient, the canonical root-generated rank-one
actors contain involutory representatives of their marked simple Weyl
classes. Apply that general Fong--Seitz (5C) construction to the original
linear hexagon consumer. It removes the finite `RootReflection` premise
while retaining the full reduced Borel and both endpoint maps.

The literal Chapter 6 and Chapter 12 applications retain the original
selected perfect factor. The marked split quotient, rotation order six
and common-field linear markings remain the independent source inputs.
In particular these results do not construct the earlier universal-tree
reflections used to build that quotient.

Source: Fong--Seitz I (5C), printed pp.25--26; DGS, *Groups and Graphs*
(1985), Theorem D, printed p.224; Aschbacher--Smith F.1.12, printed p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.G2Source
open FongSeitzBinary OriginalExtension SuzukiContainment

variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The split quotient constructs its finite reflections and hence the
marked reduced G₂ comparison, with all three original maps retained. -/
theorem reduced_linear_recognition_of_split
    (h : HypothesisF11 L S) (Q : MarkedQuotient P)
    (e : Iso
      (ofSubgroups (parabolic L (reducedSylow L S) 0)
        (parabolic L (reducedSylow L S) 0 ⊓ parabolic L (reducedSylow L S) 1)
        (parabolic L (reducedSylow L S) 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 6)
    (μ : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    ∃ short : Bool, ∃ c : Iso (reducedAmalgam L S) (G2Native.amalgam F short),
      (∀ x : parabolic L (reducedSylow L S) 0,
        (c.left x : Atlas.G2.Model F) =
          linearModelEquiv Q e (reduced_hypothesis h) split hm μ
            (UnitarySource.actorReflection Q split) (MarkedLocal.endpointMap Q e 0 x)) ∧
      (∀ x : parabolic L (reducedSylow L S) 1,
        (c.right x : Atlas.G2.Model F) =
          linearModelEquiv Q e (reduced_hypothesis h) split hm μ
            (UnitarySource.actorReflection Q split) (MarkedLocal.endpointMap Q e 1 x)) ∧
      (∀ b : commonBorel L (reducedSylow L S),
        (c.middle b : Atlas.G2.Model F) =
          linearModelEquiv Q e (reduced_hypothesis h) split hm μ
            (UnitarySource.actorReflection Q split)
            (MarkedLocal.borelMap Q e (reduced_hypothesis h) b)) :=
  reduced_linear_recognition h Q e split hm μ (UnitarySource.actorReflection Q split)

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.G2Source

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.FongSeitzBinary
open OriginalExtension SuzukiContainment
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- The original selected pair needs no supplied finite root reflections. -/
theorem comparison_and_core_of_reduced_split_linear_hexagon
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (Q : MarkedQuotient P)
    (e : Iso
      (sourceParabolicAmalgam ![L,R] (reducedSylow ![L,R] (sourceS L H)))
      Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 6)
    (μ : ∀ i, (![L,R] i ⧸ pCore 2 (![L,R] i)) ≃* PSL(2,F)) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R :=
  d.comparison_and_core_of_reduced_linear_hexagon h hTH hp F Q e split hm μ
    (UnitarySource.actorReflection Q split)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.SuzukiContainment
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The actual chosen-module application discharges its finite reflection
input using only the same marked quotient and split structure. -/
theorem rankOne_global_comparison_and_core_of_split_linear_hexagon
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (Q : MarkedQuotient P)
    (e : Iso
      (Global.sourceParabolicAmalgam ![L,R]
        (reducedSylow ![L,R] (Global.sourceS L H))) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 6)
    (μ : ∀ i, (![L,R] i ⧸ pCore 2 (![L,R] i)) ≃* PSL(2,F)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R :=
  d.comparison_and_core_of_reduced_split_linear_hexagon
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp F Q e split hm μ

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
