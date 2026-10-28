module

public import GorensteinWalter.ASevenOddClosureCoverage
public import GorensteinWalter.ASevenOddClosureElimination

/-!
# Sylow-normalized odd subgroups of A₇

Every odd-order subgroup of the concrete `A7` normalized by the dihedral
Sylow subgroup `a7S` lies in the canonical order-three subgroup `a7U`.
This supplies the containment needed for ABG II.5 Lemma9(i), article p49
(PDF page50). The source's subgroup-family notation is on article p7:
the actor here is the actual Sylow subgroup, not an arbitrary four subgroup.

Oddness and normalization imply every element passes all depths of the
odd-cycle closure test: element orders divide subgroup order, and products
with Sylow conjugates of an element or its inverse remain in the subgroup.
The first-round coverage theorem puts the element in the explicit candidate
list. The second-round elimination theorem excludes every listed element
outside `a7U`. Both finite certificates are kernel-checked prerequisites;
no classification assumption or external computation is trusted here.
-/

namespace ABG

open GorensteinWalter

public theorem aSeven_normalized_odd_subgroup_le (K : Subgroup A7)
    (hodd : Odd (Nat.card K))
    (hnorm : a7S ≤ Subgroup.normalizer (K : Set A7)) : K ≤ a7U := by
  intro x hx
  exact a7_oddClosureTest_two_mem_U_of_mem_candidates x
    (a7_oddClosureTest_one_mem_candidates x (a7_oddClosureTest_of_mem K hodd hnorm 1 x hx))
    (a7_oddClosureTest_of_mem K hodd hnorm 2 x hx)

end ABG
