module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Contracts
import Mathlib.Tactic.IntervalCases


/-!
# Odd involutions yield even involutions in two conjugates

An odd involution in S₆ has one or three transpositions. In either case an
explicit even conjugator gives a distinct commuting conjugate, whose product
is an even involution. Cycle-type conjugacy transports these two small
identities to every odd involution, preserving the even conjugator.

Source: the group-generation bound used for Aschbacher–Smith K.1.1, printed
p.452 / PDF p.463, citing GM02 Theorem 6.2 and Table 6.3. This is an intrinsic
generation calculation, not the full representation-theoretic conclusion.
-/

public section

open Equiv Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof.NaturalProof
local notation "S6" => Perm (Fin 6)
private def DoubleDifference (x : S6) : Prop :=
  ∃ k t : A6, t ≠ 1 ∧ t ^ 2 = 1 ∧
    (t : S6) = x * (k : S6) * x * (k : S6)⁻¹

private theorem difference_conjugate {x y : S6} (h : DoubleDifference x)
    (hxy : IsConj x y) : DoubleDifference y := by
  obtain ⟨k,t,ht,ht2,he⟩ := h
  obtain ⟨q,hq⟩ := isConj_iff.mp hxy
  let e := permutationAction q
  refine ⟨e k, e t, ?_, ?_, ?_⟩
  · exact fun h => ht (e.injective (h.trans e.map_one.symm))
  · rw [← map_pow, ht2, map_one]
  · change q * (t : S6) * q⁻¹ = y * (q * (k : S6) * q⁻¹) * y * (q * (k : S6) * q⁻¹)⁻¹
    rw [he, ← hq]
    group

private theorem transposition_difference : DoubleDifference (swap 0 1) := by
  let k : A6 := ⟨swap 0 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩
  let t : A6 := ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩
  exact ⟨k,t, by decide +kernel, by decide +kernel, by decide +kernel⟩

private theorem triple_difference : DoubleDifference (swap 0 1 * swap 2 3 * swap 4 5) := by
  let k : A6 := ⟨swap 1 2 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩
  let t : A6 := ⟨swap 0 3 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩
  exact ⟨k,t, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem odd_difference (x : S6) (hx : x ≠ 1) (hx2 : x ^ 2 = 1)
    (hodd : x ∉ alternatingGroup (Fin 6)) :
    ∃ k t : A6, t ≠ 1 ∧ t ^ 2 = 1 ∧
      (t : S6) = x * (k : S6) * x * (k : S6)⁻¹ := by
  have ho : orderOf x = 2 := orderOf_eq_prime hx2 hx
  obtain ⟨k,hk⟩ := Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hb := x.sum_cycleType_le
  rw [hk] at hb
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hb
  have hs : Perm.sign x ≠ 1 := hodd
  rw [Perm.sign_of_cycleType', hk] at hs
  have hkb : k ≤ 2 := by omega
  interval_cases k
  · apply difference_conjugate transposition_difference
    apply Perm.isConj_iff_cycleType_eq.mpr
    rw [hk]
    decide +kernel
  · norm_num at hs
  · apply difference_conjugate triple_difference
    apply Perm.isConj_iff_cycleType_eq.mpr
    rw [hk]
    decide +kernel
end CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof.NaturalProof
