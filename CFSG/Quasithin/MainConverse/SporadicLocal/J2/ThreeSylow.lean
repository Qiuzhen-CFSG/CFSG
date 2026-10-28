module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J2.ThreeSylowData
public import CFSG.Quasithin.MainConverse.SporadicLocal.Criteria
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.GroupTheory.SubgroupClosureFinite
import Mathlib.Tactic.FinCases

/-!
# The odd-prime ranks of the actual J₂ carrier

The certified normal forms enumerate a nonabelian subgroup of order 27.
A Sylow three-subgroup containing it also has order 27, by the independent
order certificate for the degree-100 carrier. Every other odd prime cube
fails to divide the carrier order. Thus every odd prime rank is at most two.
No simplicity assumption or comparison with the icosian carrier is used.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed pp.4 and 482;
GLS3, Table 5.3g; retained ATLAS `J2G1-p100B0` permutations.
-/

public section
namespace CFSG.Quasithin.MainConverse.SporadicLocal.J2Rank
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
theorem signedGen_map (i : Fin 4) : inclusion (signedGen i) = fastSignedGen i := by
  fin_cases i <;> simp [signedGen, fastSignedGen, map_inv, x_fast, y_fast]

theorem word_map (w : List (Fin 4)) :
    inclusion (evalWord signedGen w) = evalWord fastSignedGen w := by
  induction w with
  | nil => exact map_one inclusion
  | cons i w ih => simp only [evalWord, map_mul, signedGen_map, ih]

theorem reps_map (i : Fin 27) : inclusion (reps i) = fastReps i := word_map _

theorem transitions (i : Fin 27) (j : Fin 2) :
    reps i * generators j = reps (next i j) := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul, reps_map, reps_map]
  have hg : inclusion (generators j) = (![fastX,fastY] : Fin 2 → _) j := by
    fin_cases j <;> simp [generators, x_fast, y_fast]
  rw [hg]
  exact fast_transitions i j

theorem gen_mem (i : Fin 2) : generators i ∈ P := Subgroup.subset_closure ⟨i, rfl⟩
theorem x_mem : x ∈ P := gen_mem 0
theorem y_mem : y ∈ P := gen_mem 1

theorem signedGen_mem (i : Fin 4) : signedGen i ∈ P := by
  fin_cases i
  · exact x_mem
  · exact y_mem
  · exact P.inv_mem x_mem
  · exact P.inv_mem y_mem

theorem word_mem (w : List (Fin 4)) : evalWord signedGen w ∈ P := by
  induction w with
  | nil => exact P.one_mem
  | cons i w ih => exact P.mul_mem (signedGen_mem i) ih

theorem reps_mem (i : Fin 27) : reps i ∈ P := word_mem _

theorem reps_injective : Function.Injective reps := by
  intro i j h
  apply point_injective
  rw [← fast_point, ← fast_point, ← reps_map, ← reps_map, h]

theorem reps_surjective (g : P) : ∃ i, reps i = g.val :=
  SubgroupEnumeration.closure_range_subset_range_of_transitions
    generators reps 0 next prev rfl transitions index_inverse g.property

/-- The generated subgroup has exactly 27 elements. -/
theorem card_P : Nat.card P = 27 := by
  let f : Fin 27 → P := fun i => ⟨reps i, reps_mem i⟩
  have hi : Function.Injective f := fun i j h => reps_injective (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro g
    obtain ⟨i, hi⟩ := reps_surjective g
    exact ⟨i, Subtype.ext hi⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩).symm).trans (Nat.card_fin 27)

theorem noncommute : x * y ≠ y * x := by
  intro h
  apply fast_noncommute
  simpa only [map_mul, x_fast, y_fast] using congrArg inclusion h

/-- A genuine nonabelian Sylow three-subgroup of the degree-100 carrier. -/
theorem sylow_three : ∃ S : Sylow 3 Carrier, Nat.card S = 3 ^ 3 ∧ ¬ IsMulCommutative S := by
  have hp : IsPGroup 3 P := IsPGroup.of_card (n := 3) card_P
  obtain ⟨S, hPS⟩ := hp.exists_le_sylow
  refine ⟨S, ?_, ?_⟩
  · rw [S.card_eq_multiplicity, ExceptionalParabolics.FirstParabolic.card_carrier]
    decide +kernel
  · intro hc
    exact noncommute ((isMulCommutative_iff_of_setLike.mp hc) x (hPS x_mem) y (hPS y_mem))

private theorem odd_cube_not_dvd {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hne : p ≠ 3) : ¬ p ^ 3 ∣ 604800 := by
  intro hd
  have hpd : p ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 :=
    (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  simp only [hp.dvd_mul] at hpd
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    rcases hpd with ((h2 | h3) | h5) | h7
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
        (hp.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
        (hp.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
        (hp.dvd_of_dvd_pow h5))))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h7)))
  rcases hcases with rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  · exact hne rfl
  · norm_num at hd
  · norm_num at hd

/-- Every odd-prime rank of the carrier is at most two. -/
theorem stronglyQuasithin : IsStronglyQuasithin Carrier := by
  apply stronglyQuasithin_of_odd_sylow_cases
  intro p hp ho
  by_cases h3 : p = 3
  · subst p
    exact Or.inr sylow_three
  · apply Or.inl
    rw [ExceptionalParabolics.FirstParabolic.card_carrier]
    exact odd_cube_not_dvd hp ho h3

end CFSG.Quasithin.MainConverse.SporadicLocal.J2Rank
