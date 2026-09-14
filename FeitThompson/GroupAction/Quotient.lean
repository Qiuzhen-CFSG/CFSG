module


public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Basic
public import FeitThompson.GroupAction.Invariant
public import Theory.GroupAction.Quotient

open scoped IsMulCommutative commutatorElement
open scoped Pointwise
open Theory.GroupAction

-- Three legacy `fixedPoint`-prefixed names (used by many downstream consumers), as
-- forwarders to the canonical `Theory.GroupAction.fixedPoints`-prefixed theorems
-- (naming difference only; mathematically identical).
public theorem fixedPointSubgroup_quotient_eq_map_of_solvable_coprime
    {G : Type*} {A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G]
    (hsolv : Group.IsSolvable G)
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    ∀ (H : Subgroup G) [H.Normal] (hH : IsInvariant A G H),
      letI : MulDistribMulAction A (G ⧸ H) := quotientMulDistribMulAction (A := A) (G := G) H hH
      fixedPointSubgroup A (G ⧸ H) = (fixedPointSubgroup A G).map (QuotientGroup.mk' H) := by
  simpa [fixedPointSubgroup] using fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime (G := G) (A := A) hsolv hcoprime

public theorem fixedPointSubgroup_quotient_eq_map_of_isMulCommutative
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G]
    (H : Subgroup G) [H.Normal] (hH : IsInvariant A G H)
    [IsMulCommutative H]
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card H)) :
    letI : MulDistribMulAction A (G ⧸ H) := quotientMulDistribMulAction (A := A) (G := G) H hH
    fixedPointSubgroup A (G ⧸ H) = (fixedPointSubgroup A G).map (QuotientGroup.mk' H) := by
  simpa [fixedPointSubgroup] using fixedPoints_subgroup_quotient_eq_map_of_isMulCommutative (G := G) (A := A) H hH hcoprime

public theorem fixedPointSubgroup_map_mk'_le_fixedPointSubgroup_quotient
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (H : Subgroup G) [H.Normal] (hH : IsInvariant A G H) :
    letI : MulDistribMulAction A (G ⧸ H) := quotientMulDistribMulAction (A := A) (G := G) H hH
    (fixedPointSubgroup A G).map (QuotientGroup.mk' H) ≤ fixedPointSubgroup A (G ⧸ H) := by
  simpa [fixedPointSubgroup] using fixedPoints_subgroup_map_mk'_le_fixedPoints_subgroup_quotient (G := G) (A := A) H hH


