module

public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Index
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.Nat.Log

/-!
# Relative index and binary quotient dimension

For an elementary abelian two-subgroup `V`, the relative index of `A` in `V`
is two to the dimension of the actual quotient `V / (A ∩ V)`. This follows by
counting the vectors in that quotient. In particular, when `A ≤ V`, powers
of two in relative-index definitions express exactly the usual codimension.

This supplies the rank convention used in Aschbacher–Smith, combined manuscript
(1 March 2004), Definition E.3.13.
-/

public section

open scoped IsMulCommutative

namespace Subgroup

variable {G : Type*} [Group G] [Finite G] (V A : Subgroup G)
  [IsElementaryAbelian 2 V]

theorem relIndex_eq_two_pow_quotient_finrank :
    A.relIndex V =
      2 ^ Module.finrank (ZMod 2) (Additive (V ⧸ A.subgroupOf V)) := by
  rw [relIndex, index_eq_card]
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (V ⧸ A.subgroupOf V))
  change Nat.card (V ⧸ A.subgroupOf V) = _ at h
  simpa only [Nat.card_zmod] using h

theorem relIndex_eq_two_pow_iff_quotient_finrank (i : ℕ) :
    A.relIndex V = 2 ^ i ↔
      Module.finrank (ZMod 2) (Additive (V ⧸ A.subgroupOf V)) = i := by
  rw [relIndex_eq_two_pow_quotient_finrank]
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)).eq_iff

theorem log_relIndex_eq_quotient_finrank :
    Nat.log 2 (A.relIndex V) =
      Module.finrank (ZMod 2) (Additive (V ⧸ A.subgroupOf V)) := by
  rw [relIndex_eq_two_pow_quotient_finrank, Nat.log_pow (by decide)]

end Subgroup
