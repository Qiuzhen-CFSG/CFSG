module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index

/-!
# Fusion of a central square into a normal subgroup

A conjugate of an involution that is a square in the Sylow center has an
order-four square root commuting with the original involution. To find the
root, transport the original involution into the centralizer of its conjugate,
use Sylow conjugacy there, and transport a central square root back.

If a normal subgroup of that centralizer meets a Sylow subgroup in index two,
every order-four element has its square in the normal subgroup. Combining
these observations controls fusion without a classification of the Sylow group.
This provides an alternative to the outside-involution calculation in
Janko–Thompson, Math. Z. 113 (1970), Lemma 4.1, printed p.393.
-/

open Subgroup
open scoped Pointwise

namespace Sylow

/-- A fused central square has a square root centralizing the original involution. -/
public theorem exists_commuting_square_root_of_isConj
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (r : S) (hr : r ∈ center S) (hrz : r ^ 2 = z)
    (t : S) (hconj : IsConj (t : G) (z : G)) :
    ∃ x : G, x ^ 2 = (t : G) ∧ Commute x (z : G) ∧ orderOf x = 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let f : G ≃* G := MulAut.conj g
  have hft : f (t : G) = z := hg
  let C : Subgroup G := centralizer ({(z : G)} : Set G)
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hzc ⟨s, hs⟩))
  let y : C := ⟨f (z : G), mem_centralizer_singleton_iff.mpr (by
    have hh := congrArg f (congrArg Subtype.val (mem_center_iff.mp hzc t))
    change f ((t : G) * (z : G)) = f ((z : G) * (t : G)) at hh
    simpa only [map_mul, hft] using hh.symm)⟩
  have hy : orderOf y = 2 := by
    rw [← Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hz]
  have hp : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; rfl)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq C T (S.subtype hSC)
  have hyS : (MulAut.conj n) y ∈ S.subtype hSC := by
    rw [← hn]
    change (MulAut.conj n) • y ∈ (MulAut.conj n) • (T : Set C)
    exact Set.smul_mem_smul_set (hT (mem_zpowers y))
  let a : G ≃* G := f.trans (MulAut.conj (n : G))
  have haz : a (z : G) ∈ (S : Subgroup G) := hyS
  have hat : a (t : G) = z := by
    change (n : G) * f (t : G) * (n : G)⁻¹ = z
    rw [hft, mem_centralizer_singleton_iff.mp n.property, mul_assoc,
      mul_inv_cancel, mul_one]
  have hr4 : orderOf r = 4 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 1)
    · simpa only [pow_one, hrz] using (orderOf_eq_prime_iff.mp hz).2
    · change r ^ 4 = 1
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hrz]
      simpa only [hz] using pow_orderOf_eq_one z
  refine ⟨a.symm (r : G), ?_, ?_, ?_⟩
  · apply a.injective
    rw [map_pow, a.apply_symm_apply, hat]
    exact congrArg Subtype.val hrz
  · change a.symm (r : G) * (z : G) = (z : G) * a.symm (r : G)
    apply a.injective
    simp only [map_mul, a.apply_symm_apply]
    exact (congrArg Subtype.val (mem_center_iff.mp hr (⟨a (z : G), haz⟩ : S))).symm
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hr4]

/-- Squares of order-four elements lie in a normal subgroup of relative Sylow index two. -/
public theorem sq_mem_normal_of_relIndex_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (hindex : K.relIndex S = 2) (x : G) (hx : orderOf x = 4) : x ^ 2 ∈ K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; rfl)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq G T S
  have hxS : (MulAut.conj n) x ∈ S := by
    rw [← hn]
    change (MulAut.conj n) • x ∈ (MulAut.conj n) • (T : Set G)
    exact Set.smul_mem_smul_set (hT (mem_zpowers x))
  have hsq : ((MulAut.conj n) x) ^ 2 ∈ K :=
    (K.subgroupOf S).sq_mem_of_index_two hindex ⟨_, hxS⟩
  have hnK : n ∈ normalizer (K : Set G) := by rw [K.normalizer_eq_top]; trivial
  apply (mem_normalizer_iff.mp hnK (x ^ 2)).mpr
  change (MulAut.conj n) (x ^ 2) ∈ K
  rwa [map_pow]

end Sylow
