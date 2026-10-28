module
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.PGroupCore

/-!
# The radical after quotienting the two-core

The two-core is solvable, so the radical of its quotient is the image of
the original radical. The kernel-index formula identifies its order with
the relative index of the two-core in that radical.

Source: finite solvable extension theory; the component calculation in
Aschbacher--Smith 14.6.10(5), printed p.1029.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The actual radical image under the two-core quotient has this order. -/
theorem card_radical_twoCore_quotient :
    Nat.card (solvableRadical (G ⧸ pCore 2 G)) =
      (pCore 2 G).relIndex (solvableRadical G) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
    infer_instance
  have he : (solvableRadical G).map q = solvableRadical (G ⧸ pCore 2 G) := by
    rw [← comap_solvableRadical_eq_of_solvable_ker q (QuotientGroup.mk'_surjective _),
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  rw [← he, ← relIndex_ker, QuotientGroup.ker_mk']

/-- Odd relative index is precisely odd radical order after removing the two-core. -/
theorem odd_radical_twoCore_quotient_iff :
    Odd (Nat.card (solvableRadical (G ⧸ pCore 2 G))) ↔
      Odd ((pCore 2 G).relIndex (solvableRadical G)) := by
  rw [card_radical_twoCore_quotient]

end Theory.GroupTheory
