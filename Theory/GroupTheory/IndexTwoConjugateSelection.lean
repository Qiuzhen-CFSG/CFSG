module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic

/-!
# Selecting a conjugate in an index-two subgroup

Suppose the R-conjugates of an involution y lie in B, and N has index
two in B. If all those conjugates missed N, their quotients with y
would lie in N. Thus `[R, ⟨y⟩]` would lie in N. The contrapositive
selects an actual conjugate in N. This elementary observation is used
to choose the central-line geometry in Thompson VI, printed p.630.
-/

namespace Subgroup
open scoped commutatorElement

/-- A commutator escaping an index-two subgroup forces an involution
conjugate into that subgroup. -/
public theorem exists_conj_mem_of_index_two_commutator_not_le
    {G : Type*} [Group G] [Finite G] (R B N : Subgroup G)
    (hindex : N.relIndex B = 2) (y : G) (hy : orderOf y = 2)
    (hconj : ∀ r ∈ R, MulAut.conj r y ∈ B)
    (hcomm : ¬ ⁅R, zpowers y⁆ ≤ N) :
    ∃ r ∈ R, MulAut.conj r y ∈ N := by
  classical
  by_contra hn
  have hout : ∀ r ∈ R, MulAut.conj r y ∉ N := by
    simpa only [not_exists, not_and] using hn
  have hyB : y ∈ B := by simpa using hconj 1 R.one_mem
  have hyN : y ∉ N := by simpa using hout 1 R.one_mem
  apply hcomm
  apply commutator_le.mpr
  intro r hr t ht
  rw [mem_zpowers_iff_mem_range_orderOf, hy] at ht
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
  have hnlt : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · simp
  · simp only [pow_one]
    have hh := (N.subgroupOf B).mul_mem_iff_of_index_two hindex
      (a := ⟨MulAut.conj r y, hconj r hr⟩) (b := ⟨y⁻¹, B.inv_mem hyB⟩)
    apply hh.mpr
    change MulAut.conj r y ∈ N ↔ y⁻¹ ∈ N
    simp only [hout r hr, inv_mem_iff, hyN]

end Subgroup
