module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.CombinedSource

/-!
# Original Chapter 12 consumers of the combined unitary source branches

At the selected earlier unitary row, the quadratic profile constructs U₄
recognition and the independent U₅ source theorem supplies the other branch.
The reduced comparison feeds the existing restoration theorem. Its conclusion
concerns the original S and full Borel, including the U₄ graph extension and
the U₅ field sieve. Neither reduced/original Sylow equality nor a restriction
to field four is an input.

These are conditional consumer applications. `FiveSourceTheorem` still needs
the independent U₅ source producer, and `Row` still needs actual earlier
selection. The final owner is `qt-dgs85-source-assembly`.
Source: DGS (15.2), pp.226--228; Aschbacher--Smith F.1.12 and 12.2.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85.OriginalExtension
open ChapterF.Source.FongSeitzBinary.UnitarySource.Combined
universe u v w z
variable {G : Type u} {X : Type v} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (Q : MarkedQuotient P)
  (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hrot : rotationOrder Q = 4)
  (hfive : FiveSourceTheorem.{u,v,w,z} Q e split)
  (row : Row.{u,v,w,z} ![L,R] (sourceS L H) Q split)

include d h hTH hp e split hrot hfive row in
/-- Restore either selected unitary source row to the entire original
amalgam for the same arbitrary perfect selected R. -/
theorem comparison_of_unitary_source_rows :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) :=
  d.concreteComparison_of_reduced_alternatives h hTH hp
    (reduced_alternative_of_five_source (d.hypothesisF11 h hTH)
      Q e split hrot hfive row)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85.OriginalExtension
open ChapterF.Source.FongSeitzBinary.UnitarySource.Combined
universe u v w z
variable {G : Type u} {X : Type v} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hrot : rotationOrder Q = 4)
  (hfive : FiveSourceTheorem.{u,v,w,z} Q e split)
  (row : Row.{u,v,w,z} ![L,R] (Global.sourceS L H) Q split)

include D h hmany hn hpsl hH d hp e split hrot hfive row in
/-- Full KnownSimple/proper-K Chapter 12 specialization of the conditional
unitary source assembly, without an extra F.1.1 or restoration premise. -/
theorem rankOne_comparison_of_unitary_source_rows :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.comparison_of_unitary_source_rows
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp
    Q e split hrot hfive row

omit d hp e hfive row in
include D h hmany hn hpsl hH split hrot in
/-- At the residual preparation the same comparison supplies the strict
ambient exit. Earlier selection and the U₅ source theorem remain explicit. -/
theorem rankOne_globalExit_of_unitary_source_rows
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (e : Iso (reducedAmalgam ![L,residual H] (Global.sourceS L H)) Q.standardAmalgam)
    (hfive : FiveSourceTheorem.{u,v,w,z} Q e split)
    (row : Row.{u,v,w,z} ![L,residual H] (Global.sourceS L H) Q split) :
    RankOneModule.GlobalExit G :=
  D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp
    (D.rankOne_comparison_of_unitary_source_rows h hmany hn hpsl hH d hp
      Q e split hrot hfive row)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
