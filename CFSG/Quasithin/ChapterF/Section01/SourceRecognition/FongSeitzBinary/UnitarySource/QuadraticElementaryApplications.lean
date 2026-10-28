module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.QuadraticElementaryRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The elementary quadratic U₄ branch for the Chapter 12 pair

The proper-K/full KnownSimple preparation supplies genuine F.1.1 for the
literal pair ![L,R]. Its quadratic PSL₂ factor markings and elementary
larger-endpoint core now give a full U₄ amalgam comparison: the opposite
core's nonabelianity is proved, together with every actor, kernel, index,
root-relation and generation premise of the selected recognition theorem.
Both orientations and the binary opposite factor are retained.

The same marked split quotient, rotation four, quadratic factor profile
and elementary-core clause remain earlier source inputs. This application
does not select the profile or finish the seven-row source classification.
Source: Aschbacher--Smith 12.2.2 and F.1.1--3; DGS (11.7), pp.174--175,
Theorem D, p.224; Fong--Seitz I (6A)(b), II (8B).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source
open ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X F k : Type*} [Group G] [Finite G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The original preparation supplies F.1.1; only the earlier quadratic
factor profile and its elementary larger core remain for this U₄ branch. -/
theorem rankOne_unitaryFour_elementary_quadratic_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (μi : ((![L,R] i) ⧸ pCore 2 (![L,R] i)) ≃* PSL(2,F))
    (μj : ((![L,R] j) ⧸ pCore 2 (![L,R] j)) ≃* PSL(2,k))
    (hfields : Nat.card F = Nat.card k ^ 2)
    (helem : IsElementaryAbelian 2
      ((parabolic ![L,R] (Global.sourceS L H) i).pCoreIn 2)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact marked_elementary_quadratic_unitaryFour_catalogue Q mark hf split hm i j hij μi μj
    hfields helem

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
