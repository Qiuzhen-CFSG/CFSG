module

public import Theory.Alternating.Aut
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Cubic elements fixed by involutions of Aut(A₇) and Aut(A₈)

An involutive permutation of seven or eight letters has only one-cycles
and two-cycles. Its symmetric centralizer has order divisible by three:
either three fixed letters remain, or at least three two-cycles can be
permuted. Cauchy's theorem produces an element of order three, which is
automatically even. The actual isomorphism Sₙ ≃ Aut(Aₙ) transports this
calculation to every automorphism whose square is one.

This supplies a cubic stabilizer of the involution displacement space in
Aschbacher–Smith, 15.3.58, printed p.1149, for the normal A₇ and A₈ cases.
-/

public section

namespace alternatingGroup

open Equiv Equiv.Perm Subgroup

private theorem three_dvd_centralizer_of_sq_eq_one {n : ℕ}
    (hn : n = 7 ∨ n = 8) (s : Perm (Fin n)) (hs : s ^ 2 = 1) :
    3 ∣ Nat.card (centralizer ({s} : Set (Perm (Fin n)))) := by
  have hc := cycleType_of_pow_prime_eq_one hs
  have hb := s.sum_cycleType_le
  rw [hc, Multiset.sum_replicate] at hb
  simp only [Fintype.card_fin, smul_eq_mul] at hb
  rw [nat_card_centralizer, hc]
  rcases hn with rfl | rfl
  · have hk : s.cycleType.card ≤ 3 := by omega
    interval_cases h : s.cycleType.card <;>
      norm_num [h, Multiset.replicate_succ, Nat.factorial]
  · have hk : s.cycleType.card ≤ 4 := by omega
    interval_cases h : s.cycleType.card <;>
      norm_num [h, Multiset.replicate_succ, Nat.factorial]

/-- Every square-one automorphism of A₇ or A₈ fixes an actual cubic element.
The identity automorphism is allowed. -/
theorem exists_order_three_fixed_of_sq_eq_one {n : ℕ} (hn : n = 7 ∨ n = 8)
    (a : MulAut (alternatingGroup (Fin n))) (ha : a ^ 2 = 1) :
    ∃ b : alternatingGroup (Fin n), orderOf b = 3 ∧ a b = b := by
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    (by omega) (by omega)
  obtain ⟨s, hs⟩ := hbij.surjective a
  have hs2 : s ^ 2 = 1 := by
    apply hbij.injective
    rw [map_pow, map_one, hs, ha]
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3
    (three_dvd_centralizer_of_sq_eq_one hn s hs2)
  have hb3 : orderOf (b : Perm (Fin n)) = 3 := (Subgroup.orderOf_coe b).trans hb
  have hbEven : (b : Perm (Fin n)) ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup]
    have hp : sign (b : Perm (Fin n)) ^ 3 = 1 := by
      rw [← map_pow, ← hb3, pow_orderOf_eq_one, map_one]
    rcases Int.units_eq_one_or (sign (b : Perm (Fin n))) with h | h
    · exact h
    · rw [h] at hp
      exact ((by decide : (-1 : ℤˣ) ^ 3 ≠ 1) hp).elim
  refine ⟨⟨b, hbEven⟩, (Subgroup.orderOf_mk _ _).trans hb3, ?_⟩
  rw [← hs]
  apply Subtype.ext
  change s * (b : Perm (Fin n)) * s⁻¹ = b
  have hcomm := mem_centralizer_singleton_iff.mp b.property
  rw [← hcomm, mul_inv_cancel_right]

/-- A square-one ambient element normalizing an actual A₇ or A₈ subgroup
centralizes an order-three element of that subgroup. -/
theorem exists_order_three_commuting_of_normalizes
    {G : Type*} [Group G] (L : Subgroup G) {n : ℕ} (hn : n = 7 ∨ n = 8)
    (e : L ≃* alternatingGroup (Fin n)) (v : G)
    (hv : v ∈ normalizer (L : Set G)) (hv2 : v ^ 2 = 1) :
    ∃ b : L, orderOf (b : G) = 3 ∧ Commute v (b : G) := by
  let a := L.normalizerMonoidHom ⟨v, hv⟩
  have ha2 : a ^ 2 = 1 := by
    change L.normalizerMonoidHom ⟨v, hv⟩ ^ 2 = 1
    rw [← map_pow, show (⟨v, hv⟩ : normalizer (L : Set G)) ^ 2 = 1 from
      Subtype.ext hv2, map_one]
  have he2 : (MulAut.congr e a) ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
  obtain ⟨b, hb, hab⟩ := exists_order_three_fixed_of_sq_eq_one hn (MulAut.congr e a) he2
  refine ⟨e.symm b, (Subgroup.orderOf_coe _).trans ((e.symm.orderOf_eq b).trans hb), ?_⟩
  have he : a (e.symm b) = e.symm b := by
    apply e.injective
    change e (a (e.symm b)) = b at hab
    simpa only [e.apply_symm_apply] using hab
  have hc : v * (e.symm b : G) * v⁻¹ = (e.symm b : G) := congrArg Subtype.val he
  exact mul_inv_eq_iff_eq_mul.mp hc

end alternatingGroup
