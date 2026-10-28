module

public import Theory.Character.AlternatingSix.Rational.Permutations

/-!
# The two order-three classes in A6

An element of order three in the natural six-letter action has cycle type
`(3)` or `(3,3)`, and thus fixes three or zero points. Each type is a single
conjugacy class in A6 itself. For the double three-cycle, the odd permutation
exchanging its two cycles centralizes it; multiplying an odd S6 conjugator by
this permutation therefore gives an even conjugator.

Consequently the natural fixed-point count distinguishes precisely the two
order-three classes. This proves the marking needed to interchange the two
degree-five rows in the rational character block.

Source: the two order-three columns used in Janko, *A characterization of the
Mathieu simple groups, I*, J. Algebra 9 (1968), Section 6, pp.10–11.
-/

open Equiv Equiv.Perm
namespace Theory.Character.AlternatingSix.RationalConstruction

private theorem cycleType_of_order_three (g : Perm (Fin 6)) (hg : orderOf g = 3) :
    g.cycleType = {3} ∨ g.cycleType = {3, 3} := by
  obtain ⟨n, hn⟩ := cycleType_prime_order (show (orderOf g).Prime by rw [hg]; decide)
  rw [hg] at hn
  have hs := g.sum_cycleType_le
  rw [hn, Multiset.sum_replicate] at hs
  simp only [nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hs
  have hcases : n = 0 ∨ n = 1 := by omega
  rcases hcases with rfl | rfl
  · left
    simpa using hn
  · right
    simpa [Multiset.replicate_succ] using hn

private theorem pointCount_eq (g : A6) : pointCount g = 6 - g.val.support.card := by
  have he : (Finset.univ.filter fun i => g.val i = i) = g.val.supportᶜ := by
    ext i
    simp
  rw [pointCount, he, Finset.card_compl, Fintype.card_fin]

private def doubleThree : Perm (Fin 6) :=
  (swap 0 1 * swap 1 2) * (swap 3 4 * swap 4 5)

private def exchangeThree : Perm (Fin 6) := swap 0 3 * swap 1 4 * swap 2 5

private theorem doubleThree_even : doubleThree ∈ alternatingGroup (Fin 6) := by
  simp [doubleThree, mem_alternatingGroup]

private theorem doubleThree_type : doubleThree.cycleType = {3, 3} := by
  have ho : orderOf doubleThree = 3 :=
    orderOf_eq_prime (by decide : doubleThree ^ 3 = 1) (by decide)
  rcases cycleType_of_order_three doubleThree ho with h | h
  · have hs := doubleThree.sum_cycleType
    rw [h] at hs
    have hc : doubleThree.support.card = 6 := by decide
    simp [hc] at hs
  · exact h

private theorem exchangeThree_odd : sign exchangeThree = -1 := by
  simp [exchangeThree]

private theorem exchangeThree_commute : Commute exchangeThree doubleThree := by
  show exchangeThree * doubleThree = doubleThree * exchangeThree
  decide

private theorem doubleThree_isConj (g : A6) (hg : g.val.cycleType = {3, 3}) :
    IsConj (⟨doubleThree, doubleThree_even⟩ : A6) g := by
  have hconj : IsConj doubleThree g.val :=
    isConj_iff_cycleType_eq.mpr (doubleThree_type.trans hg.symm)
  obtain ⟨p, hp⟩ := isConj_iff.mp hconj
  rcases Int.units_eq_one_or (sign p) with he | ho
  · refine isConj_iff.mpr ⟨⟨p, mem_alternatingGroup.mpr he⟩, ?_⟩
    exact Subtype.ext hp
  · refine isConj_iff.mpr ⟨⟨p * exchangeThree, ?_⟩, ?_⟩
    · rw [mem_alternatingGroup, map_mul, ho, exchangeThree_odd]
      decide
    · apply Subtype.ext
      change (p * exchangeThree) * doubleThree * (p * exchangeThree)⁻¹ = g.val
      rw [mul_inv_rev]
      calc
        _ = p * (exchangeThree * doubleThree * exchangeThree⁻¹) * p⁻¹ := by group
        _ = p * doubleThree * p⁻¹ := by rw [exchangeThree_commute.eq]; simp
        _ = g.val := hp

/-- Among elements of order three, equality of natural fixed-point counts is
exactly conjugacy in A6. -/
public theorem isConj_iff_pointCount_eq_of_order_three {x y : A6}
    (hx : orderOf x = 3) (hy : orderOf y = 3) :
    IsConj x y ↔ pointCount x = pointCount y := by
  constructor
  · intro h
    have ht := isConj_iff_cycleType_eq.mp ((alternatingGroup (Fin 6)).subtype.map_isConj h)
    change x.val.cycleType = y.val.cycleType at ht
    simp only [pointCount_eq, ← sum_cycleType, ht]
  · intro h
    rcases cycleType_of_order_three x.val (by simpa using hx) with hx' | hx' <;>
      rcases cycleType_of_order_three y.val (by simpa using hy) with hy' | hy'
    · exact alternatingGroup.isThreeCycle_isConj (by norm_num) hx' hy'
    · simp [pointCount_eq, ← sum_cycleType, hx', hy'] at h
    · simp [pointCount_eq, ← sum_cycleType, hx', hy'] at h
    · exact (doubleThree_isConj x hx').symm.trans (doubleThree_isConj y hy')

private theorem pointCount_of_order_three (x : A6) (hx : orderOf x = 3) :
    pointCount x = 0 ∨ pointCount x = 3 := by
  rcases cycleType_of_order_three x.val (by simpa using hx) with h | h <;>
    simp [pointCount_eq, ← sum_cycleType, h]

/-- Nonconjugate elements of order three have opposite natural markings. -/
public theorem otherThreeSeparation : OtherThreeSeparation := by
  intro c x hc hx hxc
  have hne : pointCount x ≠ pointCount c :=
    fun h => hxc ((isConj_iff_pointCount_eq_of_order_three hx hc).mpr h)
  rcases pointCount_of_order_three x hx with h | h <;>
    rcases pointCount_of_order_three c hc with h' | h' <;>
    simp_all

end Theory.Character.AlternatingSix.RationalConstruction
