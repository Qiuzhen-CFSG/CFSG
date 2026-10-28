module

public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Lowering iterated displacement for a perfect actor

If the second commutator lies in a normal subgroup N, passage to G/N
and the three-subgroup lemma kill the first commutator there as well.
The quotient is the original one and no abelianness or finiteness is needed.

Application: the C_H(U)-to-U lowering in Aschbacher--Smith 14.7.74,
using the earlier centralizer calculation in 14.7.71, printed pp.1075--1077.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A perfect actor cannot have a nonzero central displacement in a quotient. -/
theorem commutator_le_of_iterated_le (M L N : Subgroup G) [Group.IsPerfect L] [N.Normal]
    (h : ⁅⁅M,L⁆,L⁆ ≤ N) : ⁅M,L⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  let : Group.IsPerfect (L.map q) := Group.IsPerfect.map q
  have hzero : (⁅⁅M,L⁆,L⁆).map q = ⊥ :=
    (map_eq_bot_iff _).mpr (by simpa only [q, QuotientGroup.ker_mk'] using h)
  rw [map_commutator, map_commutator] at hzero
  have hc := commutator_eq_bot_of_iterated_eq_bot (M.map q) (L.map q) hzero
  rw [← map_commutator] at hc
  simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff _).mp hc
end Subgroup

