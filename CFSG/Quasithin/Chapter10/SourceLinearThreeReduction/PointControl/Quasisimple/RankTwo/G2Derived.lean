module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.CarrierReduction
public import Theory.SpecificGroups.G2.BinaryResidualCover

/-!
# Excluding the binary derived G₂ containing component

The original fully moved elementary subgroup forces two-rank at least
three in the containing central quotient. The actual exceptional
isomorphism with PSU₃(3) identifies G₂(2)′ with a projective unitary group
of degree three over the nine-element field, whose two-rank is at most
two. This excludes the binary derived row without an A₅ quotient or an
irreducibility assumption on the original module.

Source: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--751;
the exceptional comparison is G.7.2(3), printed p.348.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
open Chapter3.Section02 Atlas.G2.BinaryResidualCover
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)

include D c

/-- The actual binary derived carrier contradicts the rank supplied by
full movement of the original local elementary subgroup. -/
theorem not_binary_g2 [Group.IsPerfect I]
    (e : (I ⧸ center I) ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hl := Other.center_quotient_rank D c
  have hu := Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le unitaryForm
    (by decide : Nat.Prime 3) (by decide : Odd 3)
    FiniteField.Nine.natCard FiniteField.Nine.star_eq_cube
  rw [primeRank_equiv 2 (e.trans unitaryEquiv.symm)] at hl
  omega
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
