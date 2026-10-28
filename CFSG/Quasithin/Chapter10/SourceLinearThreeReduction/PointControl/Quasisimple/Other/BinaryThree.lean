module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.LocalOrders
public import Theory.Mathieu.M22.Properties.TwoLocalSeven
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# M₂₂ exclusion for the original binary-three quotient

The literal moved image is nonzero elementary and is normalized by both
the local image and a full Sylow subgroup of the containing central quotient.
Its normalizer is therefore a full-Sylow two-local. In M₂₂ such a subgroup
has order prime to seven, whereas the original SL₃(2) quotient has order 168.
The marked two-core quotient equivalence preserves this contradiction.

This comparison retains every module row, including four-natural, and
allows vectors fixed by the original component. Other.Source applies it
to the actual remaining carrier catalogue. Source: Aschbacher--Smith
A.3.12 and 10.2.9, printed pp.47--48,750--751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The literal local quotient cannot have a factor seven in an M₂₂ carrier. -/
theorem not_mathieuTwentyTwo_of_seven [Group.IsPerfect I]
    (h7 : 7 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* Sporadic.Mathieu.M22) : False :=
  quotient_not_dvd_of_twoLocal_orders D c e
    Sporadic.Mathieu.M22TwoLocalOrders.not_seven_dvd_card_twoLocal h7

/-- M₂₂ is excluded for every original L₃(2) module row. -/
theorem not_mathieuTwentyTwo_of_binary_three [Group.IsPerfect I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (e : (I ⧸ center I) ≃* Sporadic.Mathieu.M22) : False := by
  apply not_mathieuTwentyTwo_of_seven D c _ e
  rw [Nat.card_congr dL.toEquiv,Matrix.PSL3Two.card_SL]
  decide

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
