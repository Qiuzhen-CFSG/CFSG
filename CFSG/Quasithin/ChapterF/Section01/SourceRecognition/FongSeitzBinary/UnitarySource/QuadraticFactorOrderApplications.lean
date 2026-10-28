module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.QuadraticFactorOrderRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The quadratic factor-order U₄ branch for the Chapter 12 pair

The proper-K/full KnownSimple preparation supplies F.1.1 for the literal
pair ![L,R]. Its quadratic PSL₂ factor orders now force the elementary
larger core and the nonabelian opposite core. Applying the marked U₄
recognition retains the whole Borel and both endpoint inclusion squares,
including a binary smaller factor and either endpoint orientation.

The same marked split quotient, rotation four and actual factor markings
with quadratic orders remain earlier source inputs. No original endpoint
perfectness or core-structure premise is added. The remaining branches and
exhaustive seven-row assembly are still separate obligations.

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

/-- The original preparation and quadratic factor orders give the full U₄
comparison, with both core-structure premises discharged. -/
theorem rankOne_unitaryFour_quadratic_factor_order_comparison
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
    (hfields : Nat.card F = Nat.card k ^ 2) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact marked_quadratic_factor_order_unitaryFour_catalogue Q mark hf split hm i j hij μi μj
    hfields

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
