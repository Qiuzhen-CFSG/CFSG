module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Words
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The literal order-25 subgroup for the Hall--Janko corner

The two retained words are checked against degree-100 permutation tables.
They commute, have order five, and the second is outside the first cyclic
subgroup, as witnessed on point zero. The cyclic-factor cardinality formula
therefore gives an actual subgroup of order 25, without an ambient order
or simplicity assumption. This is the subgroup used by the five-corner
presentation for Guralnick--Malle Proposition 5.1.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
open Sporadic.LeechRelated.J2 Subgroup

set_option maxRecDepth 20000 in
def leftTable : Equiv.Perm (Fin 100) where
  toFun := leftValues
  invFun := leftInvValues
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxRecDepth 20000 in
def rightTable : Equiv.Perm (Fin 100) where
  toFun := rightValues
  invFun := rightInvValues
  left_inv := by decide +kernel
  right_inv := by decide +kernel

set_option maxRecDepth 20000 in
theorem inclusion_leftGenerator : inclusion leftGenerator = leftTable := by
  rw [leftGenerator, inclusion_word]
  apply _root_.Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
theorem inclusion_rightGenerator : inclusion rightGenerator = rightTable := by
  rw [rightGenerator, inclusion_word]
  apply _root_.Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
theorem leftGenerator_fifth : leftGenerator ^ 5 = 1 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_pow, map_one, inclusion_leftGenerator]
  decide +kernel

set_option maxRecDepth 20000 in
theorem rightGenerator_fifth : rightGenerator ^ 5 = 1 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_pow, map_one, inclusion_rightGenerator]
  decide +kernel

theorem leftGenerator_ne_one : leftGenerator ≠ 1 := by
  intro h
  have h0 := congrArg (fun x : Carrier => inclusion x 0) h
  rw [inclusion_leftGenerator, map_one] at h0
  exact (by decide +kernel : leftTable 0 ≠ 0) h0

theorem rightGenerator_ne_one : rightGenerator ≠ 1 := by
  intro h
  have h0 := congrArg (fun x : Carrier => inclusion x 0) h
  rw [inclusion_rightGenerator, map_one] at h0
  exact (by decide +kernel : rightTable 0 ≠ 0) h0

theorem leftGenerator_order : orderOf leftGenerator = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact orderOf_eq_prime leftGenerator_fifth leftGenerator_ne_one

theorem rightGenerator_order : orderOf rightGenerator = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact orderOf_eq_prime rightGenerator_fifth rightGenerator_ne_one

set_option maxRecDepth 20000 in
theorem generators_commute : Commute leftGenerator rightGenerator := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul, map_mul, inclusion_leftGenerator, inclusion_rightGenerator]
  decide +kernel

theorem rightGenerator_not_mem_left : rightGenerator ∉ zpowers leftGenerator := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, leftGenerator_order]
  intro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  have hh : ∀ i : Fin 5, rightTable 0 ≠ (leftTable ^ i.val) 0 := by
    decide +kernel
  have he0 := congrArg (fun g : Carrier => inclusion g 0) he
  rw [map_pow, inclusion_leftGenerator, inclusion_rightGenerator] at he0
  exact hh ⟨i, Finset.mem_range.mp hi⟩ he0.symm

/-- The fixed literal subgroup; both generators are certified ATLAS words. -/
def subgroup : Subgroup Carrier := zpowers leftGenerator ⊔ zpowers rightGenerator

/-- The subgroup in the numerical coset discovery has order exactly 25. -/
theorem card_subgroup : Nat.card subgroup = 25 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsElementaryAbelian 5 (zpowers leftGenerator) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one leftGenerator_fifth
  exact (IsElementaryAbelian.fixed_join_card (n := 1)
    (zpowers leftGenerator) rightGenerator rightGenerator_order
    ((zpowers leftGenerator).disjoint_zpowers_of_prime_order_not_mem
      rightGenerator rightGenerator_order rightGenerator_not_mem_left)
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr generators_commute.eq))
    (by rw [Nat.card_zpowers, leftGenerator_order]; norm_num)).2

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
