module

public import Theory.GroupTheory.TwoElementaryIndexTwo
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Cubic automorphisms and elementary subgroups of index two

In a finite non-elementary group, an automorphism permutes at most two
elementary abelian subgroups of index two. Its square therefore fixes each
one, and an automorphism whose cube is the identity fixes each one as well.
Consequently a self-centralizing elementary two-subgroup whose normalizer
is a two-group cannot have index two in a subgroup with normalizer order
divisible by three.

The elementary subgroup classification is in `TwoElementaryIndexTwo`.
The normalizer consequence is used in Parrott (1972), p.676, to exclude
maximality of the fixed join in the first omega subgroup.
-/

open Subgroup
open scoped Pointwise

namespace Subgroup

private theorem eq_of_le_of_indices_two
    {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hA : A.index = 2) (hB : B.index = 2)
    (hAB : A ≤ B) : A = B := by
  have hca := A.card_mul_index
  have hcb := B.card_mul_index
  rw [hA] at hca
  rw [hB] at hcb
  exact eq_of_le_of_card_ge hAB (by omega)

/-- An automorphism's square preserves every elementary subgroup of index two
in a finite group that is not elementary abelian. -/
public theorem square_fixes_elementary_index_two
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAi : A.index = 2) (hG : ¬ IsElementaryAbelian 2 G)
    (τ : MulAut G) : τ ^ 2 • A = A := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA
  by_cases heq : τ • A = A
  · rw [pow_two, mul_smul, heq, heq]
  let B : Subgroup G := τ • A
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map τ.toMonoidHom
  have hBi : B.index = 2 :=
    (index_map_of_bijective (f := τ.toMonoidHom) τ.bijective A).trans hAi
  let : IsElementaryAbelian 2 B := hB
  have hτB : IsElementaryAbelian 2 ↥(τ • B : Subgroup G) :=
    IsElementaryAbelian.map τ.toMonoidHom
  have hτBi : (τ • B).index = 2 :=
    (index_map_of_bijective (f := τ.toMonoidHom) τ.bijective B).trans hBi
  rcases elementary_le_one_of_two_index_two A B hA hB hAi hBi (Ne.symm heq) hG
      (τ • B) hτB with hleA | hleB
  · have hEq := eq_of_le_of_indices_two (τ • B) A hτBi hAi hleA
    simpa [B, pow_two, mul_smul] using hEq
  · have hEq := eq_of_le_of_indices_two (τ • B) B hτBi hBi hleB
    have hback : B = A := Subgroup.map_injective (f := τ.toMonoidHom) τ.injective hEq
    exact (heq hback).elim

/-- Cubic automorphisms fix an elementary subgroup of index two. -/
public theorem cubic_fixes_elementary_index_two
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAi : A.index = 2) (hG : ¬ IsElementaryAbelian 2 G)
    (τ : MulAut G) (hτ : τ ^ 3 = 1) : τ • A = A := by
  have hs := square_fixes_elementary_index_two A hA hAi hG τ
  calc
    τ • A = τ • (τ ^ 2 • A) := by rw [hs]
    _ = τ ^ 3 • A := by rw [← mul_smul, ← pow_succ']
    _ = A := by rw [hτ, one_smul]

/-- A self-centralizing elementary two-subgroup with a two-group normalizer
cannot have index two in a subgroup whose normalizer has order divisible by three. -/
public theorem relIndex_ne_two_of_three_dvd_normalizer
    {G : Type*} [Group G] [Finite G]
    (A U : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAU : A ≤ U)
    (hCA : centralizer (A : Set G) ≤ A)
    (hN : IsPGroup 2 (normalizer (A : Set G)))
    (hthree : 3 ∣ Nat.card (normalizer (U : Set G))) : A.relIndex U ≠ 2 := by
  intro hindex
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsElementaryAbelian 2 A := hA
  let B := A.subgroupOf U
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAU
  have hnot : ¬ IsElementaryAbelian 2 U := by
    intro hU
    have hUA : U ≤ A := by
      apply le_trans ?_ hCA
      intro u hu a ha
      exact congrArg U.subtype
        (hU.toIsMulCommutative.is_comm.comm (⟨a, hAU ha⟩ : U) ⟨u, hu⟩)
    have heq : A.relIndex U = 1 := relIndex_eq_one.mpr hUA
    omega
  obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card'
    (G := normalizer (U : Set G)) 3 hthree
  let τ := U.normalizerMonoidHom n
  have hτ : τ ^ 3 = 1 := by
    rw [← map_pow, ← hn, pow_orderOf_eq_one, map_one]
  have hfix := cubic_fixes_elementary_index_two B hB hindex hnot τ hτ
  have hBmap : B.map U.subtype = A := map_subgroupOf_eq_of_le hAU
  have hcompat : U.subtype.comp τ.toMonoidHom =
      (MulAut.conj (n : G)).toMonoidHom.comp U.subtype := by
    ext x
    rfl
  have hnA : (n : G) ∈ normalizer (A : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh := congrArg (fun R : Subgroup U => R.map U.subtype) hfix
    change (B.map τ.toMonoidHom).map U.subtype = B.map U.subtype at hh
    rwa [map_map, hcompat, ← map_map, hBmap] at hh
  let nA : normalizer (A : Set G) := ⟨n, hnA⟩
  have hnAorder : orderOf nA = 3 :=
    (orderOf_coe nA).symm.trans ((orderOf_coe n).trans hn)
  have hh := hN.orderOf_coprime (by decide : Nat.Coprime 2 3) nA
  rw [hnAorder] at hh
  norm_num at hh

end Subgroup
