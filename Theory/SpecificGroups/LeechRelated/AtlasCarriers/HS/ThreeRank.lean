module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base
public import Theory.GroupTheory.PrimeRankFixedJoin
import Mathlib.Tactic.IntervalCases

/-!
# A cubic rank witness in the published HS carrier

For the actual ATLAS generators set x = (ab²ab³)² and
g = (ab)(ab²)(ab)(ab)(ab²)(ab⁴). The conjugate y = gxg⁻¹ commutes with x.
The four elements 1, x, x² and y send point zero to 0, 94, 59 and 15.
Thus they generate a noncyclic three-subgroup, excluding three-rank one.
All permutation identities are checked by Lean's kernel against the imported
generator tables; GAP was used only to discover the word g.

Source: ATLAS HSG1-p100B0, with provenance and original permutations retained
in `Theory/SpecificGroups/LeechRelated/AtlasCarriers/HS/source/`.
Application: Aschbacher–Smith, 1.1.5(3)(f), printed pp.501–503,
and the rank-one case of 15.3.37, printed p.1135.
-/

namespace Sporadic.LeechRelated.HS.ThreeRank
open Subgroup Theory.GroupTheory Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.OrderCertificate

private def a : Carrier := ⟨generatorA, subset_closure (by simp)⟩
private def b : Carrier := ⟨generatorB, subset_closure (by simp)⟩
private def cubicWord {G : Type*} [Group G] (a b : G) : G := (a * b ^ 2 * a * b ^ 3) ^ 2
private def conjugatingWord {G : Type*} [Group G] (a b : G) : G :=
  (a * b) * (a * b ^ 2) * (a * b) * (a * b) * (a * b ^ 2) * (a * b ^ 4)
private def x : Carrier := cubicWord a b
private def g : Carrier := conjugatingWord a b
private def y : Carrier := g * x * g⁻¹

private theorem inclusion_x : inclusion x = cubicWord generatorA generatorB := by
  simp only [x, cubicWord, map_pow, map_mul]
  rfl

private theorem inclusion_g : inclusion g = conjugatingWord generatorA generatorB := by
  simp only [g, conjugatingWord, map_pow, map_mul]
  rfl

private theorem inclusion_y : inclusion y =
    conjugatingWord generatorA generatorB * cubicWord generatorA generatorB *
      (conjugatingWord generatorA generatorB)⁻¹ := by
  simp only [y, map_mul, map_inv, inclusion_x, inclusion_g]

private theorem x_cube : x ^ 3 = 1 := by
  apply Subtype.ext
  change cubicWord generatorA generatorB ^ 3 = 1
  rw [← a_eq_generator, ← b_eq_generator]
  decide +kernel

private theorem y_cube : y ^ 3 = 1 := by
  simpa only [MulAut.conj_apply, y] using
    (map_pow (MulAut.conj g) x 3).symm.trans
      ((congrArg (MulAut.conj g) x_cube).trans (map_one _))

private theorem xy_commute : Commute x y := by
  apply Subtype.ext
  change cubicWord generatorA generatorB *
      (conjugatingWord generatorA generatorB * cubicWord generatorA generatorB *
        (conjugatingWord generatorA generatorB)⁻¹) =
    (conjugatingWord generatorA generatorB * cubicWord generatorA generatorB *
        (conjugatingWord generatorA generatorB)⁻¹) * cubicWord generatorA generatorB
  rw [← a_eq_generator, ← b_eq_generator]
  decide +kernel

private theorem witness_images :
    inclusion x 0 = 94 ∧ inclusion (x ^ 2) 0 = 59 ∧ inclusion y 0 = 15 := by
  rw [map_pow, inclusion_x, inclusion_y]
  rw [← a_eq_generator, ← b_eq_generator]
  decide +kernel

/-- The literal degree-100 HS carrier has three-rank at least two. -/
public theorem two_le_primeRank : 2 ≤ primeRank 3 Carrier := by
  classical
  have hx1 : x ≠ 1 := by
    intro h
    have hh := congrArg (fun z : Carrier => Sporadic.LeechRelated.HS.inclusion z 0) h
    norm_num only [witness_images.1, map_one, Equiv.Perm.one_apply] at hh
    exact (by decide : (94 : Fin 100) ≠ 0) hh
  have hy1 : y ≠ 1 := by
    intro h
    have hh := congrArg (fun z : Carrier => Sporadic.LeechRelated.HS.inclusion z 0) h
    norm_num only [witness_images.2.2, map_one, Equiv.Perm.one_apply] at hh
    exact (by decide : (15 : Fin 100) ≠ 0) hh
  have hyx : y ≠ x := by
    intro h
    have hh := congrArg (fun z : Carrier => Sporadic.LeechRelated.HS.inclusion z 0) h
    norm_num only [witness_images.1, witness_images.2.2] at hh
    exact (by decide : (15 : Fin 100) ≠ 94) hh
  have hyx2 : y ≠ x ^ 2 := by
    intro h
    have hh := congrArg (fun z : Carrier => Sporadic.LeechRelated.HS.inclusion z 0) h
    norm_num only [witness_images.2.1, witness_images.2.2] at hh
    exact (by decide : (15 : Fin 100) ≠ 59) hh
  have hxo : orderOf x = 3 := orderOf_eq_prime x_cube hx1
  let : IsElementaryAbelian 3 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one x_cube
  apply IsElementaryAbelian.primeRank_ge_of_fixed_join (n := 1) (zpowers x) y
    (orderOf_eq_prime y_cube hy1)
  · intro hm
    rw [mem_zpowers_iff_mem_range_orderOf, hxo] at hm
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hm
    have hk' : k < 3 := Finset.mem_range.mp hk
    interval_cases k <;> simp_all
  · rw [zpowers_le]
    exact mem_centralizer_singleton_iff.mpr xy_commute.eq
  · rw [Nat.card_zpowers, hxo]
    decide

end Sporadic.LeechRelated.HS.ThreeRank
