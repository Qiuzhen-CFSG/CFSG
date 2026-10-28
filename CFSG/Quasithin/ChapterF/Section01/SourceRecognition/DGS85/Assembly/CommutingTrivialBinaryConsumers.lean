module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.BinaryTransport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.ChapterThirteenConsumers

/-!
# Field-two source conclusions on the original quasithin consumers

The adjacent intrinsic markings and their actual equal field orders are
transported to both original starred quotients. The existing original
nonsolvable endpoint then excludes this branch for the selected generic
pair and its chosen-module application. The quintic application retains
the actual index [K:S]=5, rather than an index in a larger parabolic.

The numerical field-two premise is the output of DGS 9.10. Its producer
and final discharge remain with the commuting-trivial source assembly;
no action, contradiction or recognition callback is introduced here.

Source: DGS, *Groups and Graphs* (1985), 9.10 and 13.1, pp.147--150,191;
Aschbacher--Smith F.1.9--12 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Subgroup.CosetGeometry.RankTwo

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {K R S : Subgroup G}

/-- The original quintic endpoint excludes the intrinsic field-two
conclusion, without an extra hypothesis on the full parabolic index. -/
theorem no_adjacent_field_two_of_local_quintic
    (h : HypothesisF11 ![K,R] S) (hfive : S.relIndex K = 5)
    {a beta : Vertex (Reduction.reducedFamily ![K,R] S)}
    (hab : (graph (Reduction.reducedFamily ![K,R] S)).Adj a beta)
    {E F : Type*} [Field E] [Finite E] [CharP E 2] [Field F] [Finite F] [CharP F 2]
    (ea : (graphLocalGroup (Reduction.reducedFamily ![K,R] S) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily ![K,R] S) a)) ≃* SL(2,E))
    (eb : (graphLocalGroup (Reduction.reducedFamily ![K,R] S) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily ![K,R] S) beta)) ≃* SL(2,F))
    (hEF : Nat.card E = Nat.card F) (hF : Nat.card F = 2) : False :=
  CommutingThreeProfile.no_source_binary_of_local_quintic h hfive
    (Classical.choice (adjacent_field_two_starred_quotients h hab ea eb hEF hF false))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- The selected original generic pair excludes 9.10's numerical field-two
conclusion using its already-proved nonsolvable endpoint. -/
theorem no_commuting_trivial_binary_fields
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {a beta : Vertex (ChapterF.Source.DGS85.Reduction.reducedFamily ![L,R] (sourceS L H))}
    (hab : (graph (ChapterF.Source.DGS85.Reduction.reducedFamily ![L,R] (sourceS L H))).Adj a beta)
    {K F : Type*} [Field K] [Finite K] [CharP K 2] [Field F] [Finite F] [CharP F 2]
    (ea : (graphLocalGroup (ChapterF.Source.DGS85.Reduction.reducedFamily ![L,R] (sourceS L H)) a ⧸
      pCore 2 (graphLocalGroup (ChapterF.Source.DGS85.Reduction.reducedFamily ![L,R] (sourceS L H)) a)) ≃* SL(2,K))
    (eb : (graphLocalGroup (ChapterF.Source.DGS85.Reduction.reducedFamily ![L,R] (sourceS L H)) beta ⧸
      pCore 2 (graphLocalGroup (ChapterF.Source.DGS85.Reduction.reducedFamily ![L,R] (sourceS L H)) beta)) ≃* SL(2,F))
    (hKF : Nat.card K = Nat.card F) (hF : Nat.card F = 2) : False := by
  let e i := Classical.choice
    (adjacent_field_two_starred_quotients (d.hypothesisF11 h hTH) hab ea eb hKF hF i)
  exact d.no_chapter_thirteen_binary h hTH hp e

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] [Finite G]

/-- The chosen-module consumer keeps its same selected perfect R when
excluding the actual commuting-trivial field-two output. -/
theorem rankOne_no_commuting_trivial_binary_fields
    {T : Sylow 2 G} {L V H A B R : Subgroup G} (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    {a beta : Vertex (ChapterF.Source.DGS85.Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hab : (graph (ChapterF.Source.DGS85.Reduction.reducedFamily ![L,R] (Global.sourceS L H))).Adj a beta)
    {K F : Type*} [Field K] [Finite K] [CharP K 2] [Field F] [Finite F] [CharP F 2]
    (ea : (graphLocalGroup (ChapterF.Source.DGS85.Reduction.reducedFamily ![L,R] (Global.sourceS L H)) a ⧸
      pCore 2 (graphLocalGroup (ChapterF.Source.DGS85.Reduction.reducedFamily ![L,R] (Global.sourceS L H)) a)) ≃* SL(2,K))
    (eb : (graphLocalGroup (ChapterF.Source.DGS85.Reduction.reducedFamily ![L,R] (Global.sourceS L H)) beta ⧸
      pCore 2 (graphLocalGroup (ChapterF.Source.DGS85.Reduction.reducedFamily ![L,R] (Global.sourceS L H)) beta)) ≃* SL(2,F))
    (hKF : Nat.card K = Nat.card F) (hF : Nat.card F = 2) : False :=
  d.no_commuting_trivial_binary_fields (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp hab ea eb hKF hF

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
