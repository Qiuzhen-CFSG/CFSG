module

public import Theory.Mathieu.M22.Properties.Order
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.GroupTheory.PrimeRankSylow
import Mathlib.Tactic.FinCases

/-!
# The ordinary three-rank of M22

Two explicit words in the certified degree-22 ATLAS generators give commuting
independent elements of order three. Their join is an elementary abelian group
of order nine. The proved order 443520 of the Steiner-system model makes that
subgroup Sylow, so Sylow conjugacy and the elementary abelian generator bound
prove `primeRank 3 M22 = 2`.

The short permutation tables below are checked against the words pointwise;
all computations are kernel-checked. They avoid repeatedly reducing long words.

Sources: Aschbacher–Smith, *The Classification of Quasithin Groups*, Lemma
A.2.19, printed p. 41 (PDF p. 52); GLS, volume 3, Table 5.6.1. The underlying
ATLAS generators and their identification with the Steiner model are supplied
by `Theory.Mathieu.M22.Properties.Order`.
-/

namespace Sporadic.Mathieu
noncomputable section
open Subgroup
set_option maxRecDepth 100000

private def rankA : M22 := ⟨m22GeneratorA, m22GeneratorA_mem_M22⟩
private def rankB : M22 := ⟨m22GeneratorB, m22GeneratorB_mem_M22⟩
private def rankXWord : M22 := rankA * rankB * rankA * rankB * rankA * rankB⁻¹ * rankA * rankB⁻¹
private def rankConjugator : M22 := rankB * rankB * rankA * rankB⁻¹ * rankA * rankB * rankA * rankB⁻¹ * rankA * rankB
private def rankYWord : M22 := rankConjugator * rankXWord * rankConjugator⁻¹
private def rankXPerm : Equiv.Perm (Fin 22) where
  toFun := ![4, 21, 8, 16, 17, 5, 7, 12, 18, 10, 19, 11, 6, 1, 14, 15, 20, 0, 2, 9, 3, 13]
  invFun := ![17, 13, 18, 20, 0, 5, 12, 6, 2, 19, 9, 11, 7, 21, 14, 15, 3, 4, 8, 10, 16, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def rankYPerm : Equiv.Perm (Fin 22) where
  toFun := ![20, 13, 8, 7, 3, 5, 0, 4, 18, 9, 10, 15, 17, 21, 11, 14, 12, 16, 2, 19, 6, 1]
  invFun := ![6, 21, 18, 4, 7, 5, 20, 3, 2, 9, 10, 14, 16, 1, 15, 11, 17, 12, 8, 19, 0, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem rankXPerm_eq_word : rankXPerm = (rankXWord : Equiv.Perm (Fin 22)) := by
  ext i
  fin_cases i <;> decide +kernel

private theorem rankYPerm_eq_word : rankYPerm = (rankYWord : Equiv.Perm (Fin 22)) := by
  ext i
  fin_cases i <;> decide +kernel

private def rankX : M22 := ⟨rankXPerm, rankXPerm_eq_word.symm ▸ rankXWord.property⟩
private def rankY : M22 := ⟨rankYPerm, rankYPerm_eq_word.symm ▸ rankYWord.property⟩

private theorem rankX_order : orderOf rankX = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide +kernel
  · intro h
    have hne : (rankX : Equiv.Perm (Fin 22)) ≠ 1 := by decide +kernel
    exact hne (congrArg Subtype.val h)

private theorem rankY_order : orderOf rankY = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide +kernel
  · intro h
    have hne : (rankY : Equiv.Perm (Fin 22)) ≠ 1 := by decide +kernel
    exact hne (congrArg Subtype.val h)

private theorem rankX_commute_rankY : Commute rankX rankY := by
  apply Subtype.ext
  decide +kernel

private theorem rankY_not_mem : rankY ∉ zpowers rankX := by
  rw [mem_zpowers_iff_mem_range_orderOf, rankX_order]
  intro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  have hh : ∀ i : Fin 3,
      (rankY : Equiv.Perm (Fin 22)) ≠ (rankX : Equiv.Perm (Fin 22)) ^ i.val := by
    decide +kernel
  exact hh ⟨i, Finset.mem_range.mp hi⟩ (congrArg Subtype.val he).symm

/-- The join of two certified commuting order-three permutation subgroups. -/
public def m22ThreeElementary : Subgroup M22 := zpowers rankX ⊔ zpowers rankY

private theorem m22ThreeElementary_properties : IsElementaryAbelian 3 m22ThreeElementary ∧
    Nat.card m22ThreeElementary = 3 ^ 2 := by
  let : IsElementaryAbelian 3 (zpowers rankX) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (rankX_order ▸ pow_orderOf_eq_one rankX)
  have hc : Nat.card (zpowers rankX) = 3 ^ 1 := by
    rw [Nat.card_zpowers, rankX_order]; norm_num
  have hfix : zpowers rankX ≤ centralizer ({rankY} : Set M22) := by
    apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr rankX_commute_rankY.eq
  exact IsElementaryAbelian.fixed_join_card (zpowers rankX) rankY rankY_order
    ((zpowers rankX).disjoint_zpowers_of_prime_order_not_mem rankY rankY_order rankY_not_mem)
    hfix hc

/-- A concrete elementary abelian subgroup of order nine in M22. -/
public instance m22ThreeElementary_elementary : IsElementaryAbelian 3 m22ThreeElementary :=
  m22ThreeElementary_properties.1

public theorem m22ThreeElementary_card : Nat.card m22ThreeElementary = 3 ^ 2 :=
  m22ThreeElementary_properties.2

/-- The order-nine witness is Sylow because its index is prime to three. -/
public def m22ThreeSylow : Sylow 3 M22 :=
  (IsPGroup.of_card m22ThreeElementary_properties.2).toSylow (by
    have hc := m22ThreeElementary.card_mul_index
    rw [m22ThreeElementary_properties.2, m22_order] at hc
    have hi : m22ThreeElementary.index = 49280 := by omega
    rw [hi]
    norm_num)

/-- The underlying subgroup of the constructed Sylow subgroup is the order-nine witness. -/
public theorem m22ThreeSylow_coe : (m22ThreeSylow : Subgroup M22) = m22ThreeElementary := by rfl

/-- The actual three-rank of the Steiner-system Mathieu group M22. -/
public theorem m22_primeRank_three : primeRank 3 M22 = 2 := by
  let : IsElementaryAbelian 3 m22ThreeElementary := m22ThreeElementary_properties.1
  apply le_antisymm _ (IsElementaryAbelian.primeRank_ge_of_card
    m22ThreeElementary m22ThreeElementary_properties.2)
  rw [m22ThreeSylow.primeRank_eq]
  let : IsElementaryAbelian 3 m22ThreeSylow := m22ThreeElementary_properties.1
  exact IsElementaryAbelian.primeRank_le_of_card_le m22ThreeSylow
    (le_of_eq m22ThreeElementary_properties.2)
end
end Sporadic.Mathieu
