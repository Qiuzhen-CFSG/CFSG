module

public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure.Restriction

/-!
# Orders of the two finite hexad images

The even permutations of the six-point hexad that preserve the partition
form a group of order 24. Those also preserving the marked pair have order 8.
The counts use the direct finite permutation enumeration and are checked by
Lean's kernel. No enumeration of the degree-22 symmetric group is needed.

Together with the genuine pointwise hexad kernel, these calculations give
the local orders needed in Aschbacher–Smith E.4.3(2), printed pp. 241–242.
-/

@[expose] public section
open scoped Pointwise
open Subgroup
namespace Sporadic.Mathieu.M22ValueBound.Concrete.PartitionStructure
theorem smallGroup_card : Nat.card smallGroup = 24 := by
  let : Fintype (Equiv.Perm m22Hexad123) := fintypePerm
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem smallMarked_card : Nat.card smallMarked = 8 := by
  let : Fintype (Equiv.Perm m22Hexad123) := fintypePerm
  rw [Nat.card_eq_fintype_card]
  decide +kernel
end Sporadic.Mathieu.M22ValueBound.Concrete.PartitionStructure
