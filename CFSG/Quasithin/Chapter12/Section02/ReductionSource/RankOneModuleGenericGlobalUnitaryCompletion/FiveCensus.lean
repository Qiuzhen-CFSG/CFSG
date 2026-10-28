module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.FiveCensus
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion

/-!
# The Chapter 12 exceptional unitary completion census

The original chosen-module input uses W = wholeReduced T L. Its prepared
PSU₅(4) comparison fixes the local exponent n = 4, retaining both possible
markings. The compatible full-normalizer extension and ambient order bound
supply the 65/17 degrees, numerical coset bounds and four-walk collisions
in the literal generated normalizer subgroup. Native five-path geometry
and projective unitary recognition are still required for GlobalExit.

Source: Aschbacher–Smith 5.3.1–4,F.4.24 and the Chapter 12 application,
printed pp.658–659,287 and795. The target unitary parameter is 4, with
matrix field of order 16 and projective scalar kernel of order five.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory SimpleGraph
open Subgroup.CosetGeometry.RankTwo
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
open ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The exceptional unitary census on the literal Chapter 12 normalizers,
with W equal to the whole reduced module and both comparison markings. -/
theorem rankOne_unitaryFive_completion_census (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : FiveLocalComparison L (residual H) (Global.sourceS L H) U)
    (E : FiveExtension U) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    n = 4 ∧ ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
        (G := NormalizerJoin L (residual H)),
      c.left.range ⊓ c.right.range = c.middle.range ∧
      (∀ i : Bool, Nat.card (NormalizerJoin L (residual H) ⧸ c.cosetFamily i) ≤ fiveCosetCount i) ∧
      (∀ v : Vertex c.cosetFamily,
        Nat.card ((graph c.cosetFamily).neighborSet v) = fiveDegree v.type) ∧
      ∀ i : Bool, ∃ p q : BasedWalk (graph c.cosetFamily) 4 (base c.cosetFamily i),
        p.Nonbacktracking ∧ q.Nonbacktracking ∧ p.endpoint = q.endpoint ∧ p ≠ q := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_completion_census hi hH hp U hc E he horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
